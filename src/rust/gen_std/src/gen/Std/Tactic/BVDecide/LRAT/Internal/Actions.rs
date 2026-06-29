// Lean compiler output
// Module: Std.Tactic.BVDecide.LRAT.Internal.Actions
// Imports: Std.Tactic.BVDecide.LRAT.Actions Std.Tactic.BVDecide.LRAT.Internal.Clause
use crate::ffi::{
    lean_array_size, lean_array_uget, lean_array_uset, lean_int_dec_eq, lean_int_dec_lt,
    lean_nat_abs, lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_to_int, lean_usize_add,
    lean_usize_dec_lt,
};
use crate::r#gen::Std::Tactic::BVDecide::LRAT::Actions::{
    initialize_Std_Tactic_BVDecide_LRAT_Actions,
    runtime_initialize_Std_Tactic_BVDecide_LRAT_Actions,
};
use crate::r#gen::Std::Tactic::BVDecide::LRAT::Internal::Clause::{
    initialize_Std_Tactic_BVDecide_LRAT_Internal_Clause,
    l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray,
    runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Clause,
};
static mut l_Std_Tactic_BVDecide_LRAT_Internal_intToLiteral___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Tactic_BVDecide_LRAT_Internal_intToLiteral___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_natLiteralToPosFinLiteral(
    mut v_n_161_: *mut crate::leanh::LeanObject,
    mut v_x_162_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_167_: u8 = 0;
    let mut v___x_168_: u8 = 0;
    let mut v___x_169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_171_: u8 = 0;
    let mut v___x_172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_178_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_163_ = crate::leanh::lean_ctor_get(v_x_162_, 0);
                v_snd_164_ = crate::leanh::lean_ctor_get(v_x_162_, 1);
                v_isSharedCheck_178_ = (!crate::leanh::lean_is_exclusive(v_x_162_)) as u8;
                if v_isSharedCheck_178_ == 0 {
                    v___x_166_ = v_x_162_;
                    v_isShared_167_ = v_isSharedCheck_178_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_164_);
                    crate::leanh::lean_inc(v_fst_163_);
                    crate::leanh::lean_dec(v_x_162_);
                    v___x_166_ = crate::leanh::lean_box(0);
                    v_isShared_167_ = v_isSharedCheck_178_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_168_ = lean_nat_dec_lt(v_fst_163_, v_n_161_);
                if v___x_168_ == 0 {
                    crate::leanh::lean_del_object(v___x_166_);
                    crate::leanh::lean_dec(v_snd_164_);
                    crate::leanh::lean_dec(v_fst_163_);
                    v___x_169_ = crate::leanh::lean_box(0);
                    return v___x_169_;
                } else {
                    v___x_170_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_171_ = lean_nat_dec_eq(v_fst_163_, v___x_170_);
                    if v___x_171_ == 0 {
                        if v___x_168_ == 0 {
                            crate::leanh::lean_del_object(v___x_166_);
                            crate::leanh::lean_dec(v_snd_164_);
                            crate::leanh::lean_dec(v_fst_163_);
                            v___x_172_ = crate::leanh::lean_box(0);
                            return v___x_172_;
                        } else {
                            if v_isShared_167_ == 0 {
                                v___x_174_ = v___x_166_;
                                state = 2;
                                continue;
                            } else {
                                v_reuseFailAlloc_176_ =
                                    crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_176_, 0, v_fst_163_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_176_, 1, v_snd_164_);
                                v___x_174_ = v_reuseFailAlloc_176_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_166_);
                        crate::leanh::lean_dec(v_snd_164_);
                        crate::leanh::lean_dec(v_fst_163_);
                        v___x_177_ = crate::leanh::lean_box(0);
                        return v___x_177_;
                    }
                }
            }
            2 => {
                v___x_175_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_175_, 0, v___x_174_);
                return v___x_175_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_natLiteralToPosFinLiteral___boxed(
    mut v_n_179_: *mut crate::leanh::LeanObject,
    mut v_x_180_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_181_ = l_Std_Tactic_BVDecide_LRAT_Internal_natLiteralToPosFinLiteral(v_n_179_, v_x_180_);
    crate::leanh::lean_dec(v_n_179_);
    return v_res_181_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_LRAT_Internal_intToLiteral___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_182_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_183_ = lean_nat_to_int(v___x_182_);
    return v___x_183_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_intToLiteral(
    mut v_n_184_: *mut crate::leanh::LeanObject,
    mut v_x_185_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_187_: u8 = 0;
    v___x_186_ = lean_nat_abs(v_x_185_);
    v___x_187_ = lean_nat_dec_lt(v___x_186_, v_n_184_);
    if v___x_187_ == 0 {
        let mut v___x_188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___x_186_);
        v___x_188_ = crate::leanh::lean_box(0);
        return v___x_188_;
    } else {
        let mut v___x_189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_190_: u8 = 0;
        v___x_189_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_LRAT_Internal_intToLiteral___closed__0),
            core::ptr::addr_of_mut!(
                l_Std_Tactic_BVDecide_LRAT_Internal_intToLiteral___closed__0_once
            ),
            _init_l_Std_Tactic_BVDecide_LRAT_Internal_intToLiteral___closed__0,
        );
        v___x_190_ = lean_int_dec_eq(v_x_185_, v___x_189_);
        if v___x_190_ == 0 {
            if v___x_187_ == 0 {
                let mut v___x_191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v___x_186_);
                v___x_191_ = crate::leanh::lean_box(0);
                return v___x_191_;
            } else {
                let mut v___x_192_: u8 = 0;
                let mut v___x_193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_192_ = lean_int_dec_lt(v___x_189_, v_x_185_);
                v___x_193_ = crate::leanh::lean_box((v___x_192_) as usize);
                v___x_194_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_194_, 0, v___x_186_);
                crate::leanh::lean_ctor_set(v___x_194_, 1, v___x_193_);
                v___x_195_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_195_, 0, v___x_194_);
                return v___x_195_;
            }
        } else {
            let mut v___x_196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_186_);
            v___x_196_ = crate::leanh::lean_box(0);
            return v___x_196_;
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_intToLiteral___boxed(
    mut v_n_197_: *mut crate::leanh::LeanObject,
    mut v_x_198_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_199_ = l_Std_Tactic_BVDecide_LRAT_Internal_intToLiteral(v_n_197_, v_x_198_);
    crate::leanh::lean_dec(v_x_198_);
    crate::leanh::lean_dec(v_n_197_);
    return v_res_199_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Tactic_BVDecide_LRAT_Internal_intActionToDefaultClauseAction_spec__0(
    mut v_n_200_: *mut crate::leanh::LeanObject,
    mut v_sz_201_: usize,
    mut v_i_202_: usize,
    mut v_bs_203_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_204_: u8 = 0;
    let mut v___x_205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_208_: u8 = 0;
    let mut v___x_209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_212_: u8 = 0;
    let mut v___x_213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_215_: u8 = 0;
    let mut v___x_216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_218_: usize = 0;
    let mut v___x_219_: usize = 0;
    let mut v___x_220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_204_ = lean_usize_dec_lt(v_i_202_, v_sz_201_);
                if v___x_204_ == 0 {
                    v___x_205_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_205_, 0, v_bs_203_);
                    return v___x_205_;
                } else {
                    v_v_206_ = lean_array_uget(v_bs_203_, v_i_202_);
                    v___x_207_ = lean_nat_abs(v_v_206_);
                    v___x_208_ = lean_nat_dec_lt(v___x_207_, v_n_200_);
                    if v___x_208_ == 0 {
                        crate::leanh::lean_dec(v___x_207_);
                        crate::leanh::lean_dec(v_v_206_);
                        crate::leanh::lean_dec_ref(v_bs_203_);
                        v___x_209_ = crate::leanh::lean_box(0);
                        return v___x_209_;
                    } else {
                        v___x_210_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_211_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Internal_intToLiteral___closed__0
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Tactic_BVDecide_LRAT_Internal_intToLiteral___closed__0_once
                            ),
                            _init_l_Std_Tactic_BVDecide_LRAT_Internal_intToLiteral___closed__0,
                        );
                        v___x_212_ = lean_int_dec_eq(v_v_206_, v___x_211_);
                        if v___x_212_ == 0 {
                            if v___x_208_ == 0 {
                                crate::leanh::lean_dec(v___x_207_);
                                crate::leanh::lean_dec(v_v_206_);
                                crate::leanh::lean_dec_ref(v_bs_203_);
                                v___x_213_ = crate::leanh::lean_box(0);
                                return v___x_213_;
                            } else {
                                v_bs_x27_214_ = lean_array_uset(v_bs_203_, v_i_202_, v___x_210_);
                                v___x_215_ = lean_int_dec_lt(v___x_211_, v_v_206_);
                                crate::leanh::lean_dec(v_v_206_);
                                v___x_216_ = crate::leanh::lean_box((v___x_215_) as usize);
                                v___x_217_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_217_, 0, v___x_207_);
                                crate::leanh::lean_ctor_set(v___x_217_, 1, v___x_216_);
                                v___x_218_ = 1usize;
                                v___x_219_ = lean_usize_add(v_i_202_, v___x_218_);
                                v___x_220_ = lean_array_uset(v_bs_x27_214_, v_i_202_, v___x_217_);
                                v_i_202_ = v___x_219_;
                                v_bs_203_ = v___x_220_;
                                state = 0;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_207_);
                            crate::leanh::lean_dec(v_v_206_);
                            crate::leanh::lean_dec_ref(v_bs_203_);
                            v___x_222_ = crate::leanh::lean_box(0);
                            return v___x_222_;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Tactic_BVDecide_LRAT_Internal_intActionToDefaultClauseAction_spec__0___boxed(
    mut v_n_223_: *mut crate::leanh::LeanObject,
    mut v_sz_224_: *mut crate::leanh::LeanObject,
    mut v_i_225_: *mut crate::leanh::LeanObject,
    mut v_bs_226_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_227_: usize = 0;
    let mut v_i_boxed_228_: usize = 0;
    let mut v_res_229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_227_ = crate::leanh::lean_unbox_usize(v_sz_224_);
    crate::leanh::lean_dec(v_sz_224_);
    v_i_boxed_228_ = crate::leanh::lean_unbox_usize(v_i_225_);
    crate::leanh::lean_dec(v_i_225_);
    v_res_229_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Tactic_BVDecide_LRAT_Internal_intActionToDefaultClauseAction_spec__0(v_n_223_, v_sz_boxed_227_, v_i_boxed_228_, v_bs_226_);
    crate::leanh::lean_dec(v_n_223_);
    return v_res_229_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_intActionToDefaultClauseAction(
    mut v_n_230_: *mut crate::leanh::LeanObject,
    mut v_x_231_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_id_232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rupHints_233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_236_: u8 = 0;
    let mut v___x_238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_241_: u8 = 0;
    let mut v_id_242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rupHints_244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_247_: u8 = 0;
    let mut v_sz_248_: usize = 0;
    let mut v___x_249_: usize = 0;
    let mut v___x_250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_258_: u8 = 0;
    let mut v___x_260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_265_: u8 = 0;
    let mut v_isSharedCheck_266_: u8 = 0;
    let mut v_pivot_267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rupHints_270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ratHints_271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_274_: u8 = 0;
    let mut v_fst_275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_279_: u8 = 0;
    let mut v___x_280_: u8 = 0;
    let mut v___x_281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_283_: u8 = 0;
    let mut v___x_284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_285_: usize = 0;
    let mut v___x_286_: usize = 0;
    let mut v___x_287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_295_: u8 = 0;
    let mut v___x_297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_305_: u8 = 0;
    let mut v___x_306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_307_: u8 = 0;
    let mut v_isSharedCheck_308_: u8 = 0;
    let mut v_ids_309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_312_: u8 = 0;
    let mut v___x_314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_317_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_231_) {
                0 => {
                    v_id_232_ = crate::leanh::lean_ctor_get(v_x_231_, 0);
                    v_rupHints_233_ = crate::leanh::lean_ctor_get(v_x_231_, 1);
                    v_isSharedCheck_241_ = (!crate::leanh::lean_is_exclusive(v_x_231_)) as u8;
                    if v_isSharedCheck_241_ == 0 {
                        v___x_235_ = v_x_231_;
                        v_isShared_236_ = v_isSharedCheck_241_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_rupHints_233_);
                        crate::leanh::lean_inc(v_id_232_);
                        crate::leanh::lean_dec(v_x_231_);
                        v___x_235_ = crate::leanh::lean_box(0);
                        v_isShared_236_ = v_isSharedCheck_241_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_id_242_ = crate::leanh::lean_ctor_get(v_x_231_, 0);
                    v_c_243_ = crate::leanh::lean_ctor_get(v_x_231_, 1);
                    v_rupHints_244_ = crate::leanh::lean_ctor_get(v_x_231_, 2);
                    v_isSharedCheck_266_ = (!crate::leanh::lean_is_exclusive(v_x_231_)) as u8;
                    if v_isSharedCheck_266_ == 0 {
                        v___x_246_ = v_x_231_;
                        v_isShared_247_ = v_isSharedCheck_266_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_rupHints_244_);
                        crate::leanh::lean_inc(v_c_243_);
                        crate::leanh::lean_inc(v_id_242_);
                        crate::leanh::lean_dec(v_x_231_);
                        v___x_246_ = crate::leanh::lean_box(0);
                        v_isShared_247_ = v_isSharedCheck_266_;
                        state = 3;
                        continue;
                    }
                }
                2 => {
                    v_pivot_267_ = crate::leanh::lean_ctor_get(v_x_231_, 2);
                    v_id_268_ = crate::leanh::lean_ctor_get(v_x_231_, 0);
                    v_c_269_ = crate::leanh::lean_ctor_get(v_x_231_, 1);
                    v_rupHints_270_ = crate::leanh::lean_ctor_get(v_x_231_, 3);
                    v_ratHints_271_ = crate::leanh::lean_ctor_get(v_x_231_, 4);
                    v_isSharedCheck_308_ = (!crate::leanh::lean_is_exclusive(v_x_231_)) as u8;
                    if v_isSharedCheck_308_ == 0 {
                        v___x_273_ = v_x_231_;
                        v_isShared_274_ = v_isSharedCheck_308_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_ratHints_271_);
                        crate::leanh::lean_inc(v_rupHints_270_);
                        crate::leanh::lean_inc(v_pivot_267_);
                        crate::leanh::lean_inc(v_c_269_);
                        crate::leanh::lean_inc(v_id_268_);
                        crate::leanh::lean_dec(v_x_231_);
                        v___x_273_ = crate::leanh::lean_box(0);
                        v_isShared_274_ = v_isSharedCheck_308_;
                        state = 7;
                        continue;
                    }
                }
                _ => {
                    v_ids_309_ = crate::leanh::lean_ctor_get(v_x_231_, 0);
                    v_isSharedCheck_317_ = (!crate::leanh::lean_is_exclusive(v_x_231_)) as u8;
                    if v_isSharedCheck_317_ == 0 {
                        v___x_311_ = v_x_231_;
                        v_isShared_312_ = v_isSharedCheck_317_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_ids_309_);
                        crate::leanh::lean_dec(v_x_231_);
                        v___x_311_ = crate::leanh::lean_box(0);
                        v_isShared_312_ = v_isSharedCheck_317_;
                        state = 13;
                        continue;
                    }
                }
            },
            1 => {
                if v_isShared_236_ == 0 {
                    v___x_238_ = v___x_235_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_240_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_240_, 0, v_id_232_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_240_, 1, v_rupHints_233_);
                    v___x_238_ = v_reuseFailAlloc_240_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_239_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_239_, 0, v___x_238_);
                return v___x_239_;
            }
            3 => {
                v_sz_248_ = lean_array_size(v_c_243_);
                v___x_249_ = 0usize;
                v___x_250_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Tactic_BVDecide_LRAT_Internal_intActionToDefaultClauseAction_spec__0(v_n_230_, v_sz_248_, v___x_249_, v_c_243_);
                if crate::leanh::lean_obj_tag(v___x_250_) == 0 {
                    crate::leanh::lean_del_object(v___x_246_);
                    crate::leanh::lean_dec_ref(v_rupHints_244_);
                    crate::leanh::lean_dec(v_id_242_);
                    v___x_251_ = crate::leanh::lean_box(0);
                    return v___x_251_;
                } else {
                    v_val_252_ = crate::leanh::lean_ctor_get(v___x_250_, 0);
                    crate::leanh::lean_inc(v_val_252_);
                    crate::leanh::lean_dec_ref_known(v___x_250_, 1);
                    v___x_253_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray(
                        v_n_230_, v_val_252_,
                    );
                    crate::leanh::lean_dec(v_val_252_);
                    if crate::leanh::lean_obj_tag(v___x_253_) == 0 {
                        crate::leanh::lean_del_object(v___x_246_);
                        crate::leanh::lean_dec_ref(v_rupHints_244_);
                        crate::leanh::lean_dec(v_id_242_);
                        v___x_254_ = crate::leanh::lean_box(0);
                        return v___x_254_;
                    } else {
                        v_val_255_ = crate::leanh::lean_ctor_get(v___x_253_, 0);
                        v_isSharedCheck_265_ = (!crate::leanh::lean_is_exclusive(v___x_253_)) as u8;
                        if v_isSharedCheck_265_ == 0 {
                            v___x_257_ = v___x_253_;
                            v_isShared_258_ = v_isSharedCheck_265_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_255_);
                            crate::leanh::lean_dec(v___x_253_);
                            v___x_257_ = crate::leanh::lean_box(0);
                            v_isShared_258_ = v_isSharedCheck_265_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            4 => {
                if v_isShared_247_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_246_, 1, v_val_255_);
                    v___x_260_ = v___x_246_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_264_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_264_, 0, v_id_242_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_264_, 1, v_val_255_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_264_, 2, v_rupHints_244_);
                    v___x_260_ = v_reuseFailAlloc_264_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_258_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_257_, 0, v___x_260_);
                    v___x_262_ = v___x_257_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_263_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_263_, 0, v___x_260_);
                    v___x_262_ = v_reuseFailAlloc_263_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_262_;
            }
            7 => {
                v_fst_275_ = crate::leanh::lean_ctor_get(v_pivot_267_, 0);
                v_snd_276_ = crate::leanh::lean_ctor_get(v_pivot_267_, 1);
                v_isSharedCheck_307_ = (!crate::leanh::lean_is_exclusive(v_pivot_267_)) as u8;
                if v_isSharedCheck_307_ == 0 {
                    v___x_278_ = v_pivot_267_;
                    v_isShared_279_ = v_isSharedCheck_307_;
                    state = 8;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_276_);
                    crate::leanh::lean_inc(v_fst_275_);
                    crate::leanh::lean_dec(v_pivot_267_);
                    v___x_278_ = crate::leanh::lean_box(0);
                    v_isShared_279_ = v_isSharedCheck_307_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_280_ = lean_nat_dec_lt(v_fst_275_, v_n_230_);
                if v___x_280_ == 0 {
                    crate::leanh::lean_del_object(v___x_278_);
                    crate::leanh::lean_dec(v_snd_276_);
                    crate::leanh::lean_dec(v_fst_275_);
                    crate::leanh::lean_del_object(v___x_273_);
                    crate::leanh::lean_dec_ref(v_ratHints_271_);
                    crate::leanh::lean_dec_ref(v_rupHints_270_);
                    crate::leanh::lean_dec(v_c_269_);
                    crate::leanh::lean_dec(v_id_268_);
                    v___x_281_ = crate::leanh::lean_box(0);
                    return v___x_281_;
                } else {
                    v___x_282_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_283_ = lean_nat_dec_eq(v_fst_275_, v___x_282_);
                    if v___x_283_ == 0 {
                        if v___x_280_ == 0 {
                            crate::leanh::lean_del_object(v___x_278_);
                            crate::leanh::lean_dec(v_snd_276_);
                            crate::leanh::lean_dec(v_fst_275_);
                            crate::leanh::lean_del_object(v___x_273_);
                            crate::leanh::lean_dec_ref(v_ratHints_271_);
                            crate::leanh::lean_dec_ref(v_rupHints_270_);
                            crate::leanh::lean_dec(v_c_269_);
                            crate::leanh::lean_dec(v_id_268_);
                            v___x_284_ = crate::leanh::lean_box(0);
                            return v___x_284_;
                        } else {
                            v_sz_285_ = lean_array_size(v_c_269_);
                            v___x_286_ = 0usize;
                            v___x_287_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Tactic_BVDecide_LRAT_Internal_intActionToDefaultClauseAction_spec__0(v_n_230_, v_sz_285_, v___x_286_, v_c_269_);
                            if crate::leanh::lean_obj_tag(v___x_287_) == 0 {
                                crate::leanh::lean_del_object(v___x_278_);
                                crate::leanh::lean_dec(v_snd_276_);
                                crate::leanh::lean_dec(v_fst_275_);
                                crate::leanh::lean_del_object(v___x_273_);
                                crate::leanh::lean_dec_ref(v_ratHints_271_);
                                crate::leanh::lean_dec_ref(v_rupHints_270_);
                                crate::leanh::lean_dec(v_id_268_);
                                v___x_288_ = crate::leanh::lean_box(0);
                                return v___x_288_;
                            } else {
                                v_val_289_ = crate::leanh::lean_ctor_get(v___x_287_, 0);
                                crate::leanh::lean_inc(v_val_289_);
                                crate::leanh::lean_dec_ref_known(v___x_287_, 1);
                                v___x_290_ =
                                    l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray(
                                        v_n_230_, v_val_289_,
                                    );
                                crate::leanh::lean_dec(v_val_289_);
                                if crate::leanh::lean_obj_tag(v___x_290_) == 0 {
                                    crate::leanh::lean_del_object(v___x_278_);
                                    crate::leanh::lean_dec(v_snd_276_);
                                    crate::leanh::lean_dec(v_fst_275_);
                                    crate::leanh::lean_del_object(v___x_273_);
                                    crate::leanh::lean_dec_ref(v_ratHints_271_);
                                    crate::leanh::lean_dec_ref(v_rupHints_270_);
                                    crate::leanh::lean_dec(v_id_268_);
                                    v___x_291_ = crate::leanh::lean_box(0);
                                    return v___x_291_;
                                } else {
                                    v_val_292_ = crate::leanh::lean_ctor_get(v___x_290_, 0);
                                    v_isSharedCheck_305_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_290_)) as u8;
                                    if v_isSharedCheck_305_ == 0 {
                                        v___x_294_ = v___x_290_;
                                        v_isShared_295_ = v_isSharedCheck_305_;
                                        state = 9;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_val_292_);
                                        crate::leanh::lean_dec(v___x_290_);
                                        v___x_294_ = crate::leanh::lean_box(0);
                                        v_isShared_295_ = v_isSharedCheck_305_;
                                        state = 9;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_278_);
                        crate::leanh::lean_dec(v_snd_276_);
                        crate::leanh::lean_dec(v_fst_275_);
                        crate::leanh::lean_del_object(v___x_273_);
                        crate::leanh::lean_dec_ref(v_ratHints_271_);
                        crate::leanh::lean_dec_ref(v_rupHints_270_);
                        crate::leanh::lean_dec(v_c_269_);
                        crate::leanh::lean_dec(v_id_268_);
                        v___x_306_ = crate::leanh::lean_box(0);
                        return v___x_306_;
                    }
                }
            }
            9 => {
                if v_isShared_279_ == 0 {
                    v___x_297_ = v___x_278_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_304_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_304_, 0, v_fst_275_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_304_, 1, v_snd_276_);
                    v___x_297_ = v_reuseFailAlloc_304_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_274_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_273_, 2, v___x_297_);
                    crate::leanh::lean_ctor_set(v___x_273_, 1, v_val_292_);
                    v___x_299_ = v___x_273_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_303_ = crate::leanh::lean_alloc_ctor(2, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_303_, 0, v_id_268_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_303_, 1, v_val_292_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_303_, 2, v___x_297_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_303_, 3, v_rupHints_270_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_303_, 4, v_ratHints_271_);
                    v___x_299_ = v_reuseFailAlloc_303_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_295_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_294_, 0, v___x_299_);
                    v___x_301_ = v___x_294_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_302_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_302_, 0, v___x_299_);
                    v___x_301_ = v_reuseFailAlloc_302_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_301_;
            }
            13 => {
                if v_isShared_312_ == 0 {
                    v___x_314_ = v___x_311_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_316_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_316_, 0, v_ids_309_);
                    v___x_314_ = v_reuseFailAlloc_316_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_315_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_315_, 0, v___x_314_);
                return v___x_315_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_intActionToDefaultClauseAction___boxed(
    mut v_n_318_: *mut crate::leanh::LeanObject,
    mut v_x_319_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_320_ =
        l_Std_Tactic_BVDecide_LRAT_Internal_intActionToDefaultClauseAction(v_n_318_, v_x_319_);
    crate::leanh::lean_dec(v_n_318_);
    return v_res_320_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Actions(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Actions(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Clause(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Actions(
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
pub unsafe fn initialize_Std_Tactic_BVDecide_LRAT_Internal_Actions(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_BVDecide_LRAT_Actions(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Clause(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Actions(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Actions(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_LRAT_Internal_Actions(builtin);
}
