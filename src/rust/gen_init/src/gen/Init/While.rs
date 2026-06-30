// Lean compiler output
// Module: Init.While
// Imports: Init.Core Init.Classical
use crate::r#gen::Init::Classical::{initialize_Init_Classical, runtime_initialize_Init_Classical};
use crate::r#gen::Init::Core::{initialize_Init_Core, runtime_initialize_Init_Core};
pub unsafe fn l_whileM_body___redArg___lam__0(
    mut v_recur_154_: *mut leanh::LeanObject,
    mut v_toPure_155_: *mut leanh::LeanObject,
    mut v_____do__lift_156_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_156_) == 0 {
        let mut v_val_157_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_158_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_toPure_155_);
        v_val_157_ = leanh::lean_ctor_get(v_____do__lift_156_, 0);
        leanh::lean_inc(v_val_157_);
        leanh::lean_dec_ref_known(v_____do__lift_156_, 1);
        v___x_158_ = leanh::lean_apply_1(v_recur_154_, v_val_157_);
        return v___x_158_;
    } else {
        let mut v_val_159_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_160_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_recur_154_);
        v_val_159_ = leanh::lean_ctor_get(v_____do__lift_156_, 0);
        leanh::lean_inc(v_val_159_);
        leanh::lean_dec_ref_known(v_____do__lift_156_, 1);
        v___x_160_ =
            leanh::lean_apply_2(v_toPure_155_, leanh::lean_box(0), v_val_159_);
        return v___x_160_;
    }
}
pub unsafe fn l_whileM_body___redArg(
    mut v_inst_161_: *mut leanh::LeanObject,
    mut v_f_162_: *mut leanh::LeanObject,
    mut v_recur_163_: *mut leanh::LeanObject,
    mut v_a_164_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_170_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_165_ = leanh::lean_ctor_get(v_inst_161_, 0);
    leanh::lean_inc_ref(v_toApplicative_165_);
    v_toBind_166_ = leanh::lean_ctor_get(v_inst_161_, 1);
    leanh::lean_inc(v_toBind_166_);
    leanh::lean_dec_ref(v_inst_161_);
    v_toPure_167_ = leanh::lean_ctor_get(v_toApplicative_165_, 1);
    leanh::lean_inc(v_toPure_167_);
    leanh::lean_dec_ref(v_toApplicative_165_);
    v___x_168_ = leanh::lean_apply_1(v_f_162_, v_a_164_);
    v___f_169_ = leanh::lean_alloc_closure(
        l_whileM_body___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_169_, 0, v_recur_163_);
    leanh::lean_closure_set(v___f_169_, 1, v_toPure_167_);
    v___x_170_ = leanh::lean_apply_4(
        v_toBind_166_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_168_,
        v___f_169_,
    );
    return v___x_170_;
}
pub unsafe fn l_whileM_body(
    mut v_00_u03b1_171_: *mut leanh::LeanObject,
    mut v_m_172_: *mut leanh::LeanObject,
    mut v_inst_173_: *mut leanh::LeanObject,
    mut v_00_u03b2_174_: *mut leanh::LeanObject,
    mut v_f_175_: *mut leanh::LeanObject,
    mut v_recur_176_: *mut leanh::LeanObject,
    mut v_a_177_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_183_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_178_ = leanh::lean_ctor_get(v_inst_173_, 0);
    leanh::lean_inc_ref(v_toApplicative_178_);
    v_toBind_179_ = leanh::lean_ctor_get(v_inst_173_, 1);
    leanh::lean_inc(v_toBind_179_);
    leanh::lean_dec_ref(v_inst_173_);
    v_toPure_180_ = leanh::lean_ctor_get(v_toApplicative_178_, 1);
    leanh::lean_inc(v_toPure_180_);
    leanh::lean_dec_ref(v_toApplicative_178_);
    v___x_181_ = leanh::lean_apply_1(v_f_175_, v_a_177_);
    v___f_182_ = leanh::lean_alloc_closure(
        l_whileM_body___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_182_, 0, v_recur_176_);
    leanh::lean_closure_set(v___f_182_, 1, v_toPure_180_);
    v___x_183_ = leanh::lean_apply_4(
        v_toBind_179_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_181_,
        v___f_182_,
    );
    return v___x_183_;
}
pub unsafe fn l___private_Init_While_0__whileM_impl___redArg(
    mut v_inst_184_: *mut leanh::LeanObject,
    mut v_f_185_: *mut leanh::LeanObject,
    mut v_a_186_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_192_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_187_ = leanh::lean_ctor_get(v_inst_184_, 0);
    v_toBind_188_ = leanh::lean_ctor_get(v_inst_184_, 1);
    leanh::lean_inc(v_toBind_188_);
    v_toPure_189_ = leanh::lean_ctor_get(v_toApplicative_187_, 1);
    leanh::lean_inc(v_toPure_189_);
    leanh::lean_inc(v_f_185_);
    v___x_190_ = leanh::lean_apply_1(v_f_185_, v_a_186_);
    v___f_191_ = leanh::lean_alloc_closure(
        l___private_Init_While_0__whileM_impl___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_191_, 0, v_inst_184_);
    leanh::lean_closure_set(v___f_191_, 1, v_f_185_);
    leanh::lean_closure_set(v___f_191_, 2, v_toPure_189_);
    v___x_192_ = leanh::lean_apply_4(
        v_toBind_188_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_190_,
        v___f_191_,
    );
    return v___x_192_;
}
pub unsafe fn l___private_Init_While_0__whileM_impl___redArg___lam__0(
    mut v_inst_193_: *mut leanh::LeanObject,
    mut v_f_194_: *mut leanh::LeanObject,
    mut v_toPure_195_: *mut leanh::LeanObject,
    mut v_____do__lift_196_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_196_) == 0 {
        let mut v_val_197_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_198_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_toPure_195_);
        v_val_197_ = leanh::lean_ctor_get(v_____do__lift_196_, 0);
        leanh::lean_inc(v_val_197_);
        leanh::lean_dec_ref_known(v_____do__lift_196_, 1);
        v___x_198_ =
            l___private_Init_While_0__whileM_impl___redArg(v_inst_193_, v_f_194_, v_val_197_);
        return v___x_198_;
    } else {
        let mut v_val_199_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_200_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_f_194_);
        leanh::lean_dec_ref(v_inst_193_);
        v_val_199_ = leanh::lean_ctor_get(v_____do__lift_196_, 0);
        leanh::lean_inc(v_val_199_);
        leanh::lean_dec_ref_known(v_____do__lift_196_, 1);
        v___x_200_ =
            leanh::lean_apply_2(v_toPure_195_, leanh::lean_box(0), v_val_199_);
        return v___x_200_;
    }
}
pub unsafe fn l___private_Init_While_0__whileM_impl(
    mut v_00_u03b1_201_: *mut leanh::LeanObject,
    mut v_m_202_: *mut leanh::LeanObject,
    mut v_inst_203_: *mut leanh::LeanObject,
    mut v_00_u03b2_204_: *mut leanh::LeanObject,
    mut v_inst_205_: *mut leanh::LeanObject,
    mut v_f_206_: *mut leanh::LeanObject,
    mut v_a_207_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_208_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_208_ = l___private_Init_While_0__whileM_impl___redArg(v_inst_203_, v_f_206_, v_a_207_);
    return v___x_208_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___redArg(
    mut v_inst_209_: *mut leanh::LeanObject,
    mut v_f_210_: *mut leanh::LeanObject,
    mut v_a_211_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_217_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_212_ = leanh::lean_ctor_get(v_inst_209_, 0);
    v_toBind_213_ = leanh::lean_ctor_get(v_inst_209_, 1);
    leanh::lean_inc(v_toBind_213_);
    v_toPure_214_ = leanh::lean_ctor_get(v_toApplicative_212_, 1);
    leanh::lean_inc(v_toPure_214_);
    leanh::lean_inc(v_f_210_);
    v___x_215_ = leanh::lean_apply_1(v_f_210_, v_a_211_);
    v___f_216_ = leanh::lean_alloc_closure(
        l___private_Init_While_0__whileM_erased___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_216_, 0, v_inst_209_);
    leanh::lean_closure_set(v___f_216_, 1, v_f_210_);
    leanh::lean_closure_set(v___f_216_, 2, v_toPure_214_);
    v___x_217_ = leanh::lean_apply_4(
        v_toBind_213_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_215_,
        v___f_216_,
    );
    return v___x_217_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___redArg___lam__0(
    mut v_inst_218_: *mut leanh::LeanObject,
    mut v_f_219_: *mut leanh::LeanObject,
    mut v_toPure_220_: *mut leanh::LeanObject,
    mut v_____do__lift_221_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_221_) == 0 {
        let mut v_val_222_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_223_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_toPure_220_);
        v_val_222_ = leanh::lean_ctor_get(v_____do__lift_221_, 0);
        leanh::lean_inc(v_val_222_);
        leanh::lean_dec_ref_known(v_____do__lift_221_, 1);
        v___x_223_ =
            l___private_Init_While_0__whileM_erased___redArg(v_inst_218_, v_f_219_, v_val_222_);
        return v___x_223_;
    } else {
        let mut v_val_224_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_225_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_f_219_);
        leanh::lean_dec_ref(v_inst_218_);
        v_val_224_ = leanh::lean_ctor_get(v_____do__lift_221_, 0);
        leanh::lean_inc(v_val_224_);
        leanh::lean_dec_ref_known(v_____do__lift_221_, 1);
        v___x_225_ =
            leanh::lean_apply_2(v_toPure_220_, leanh::lean_box(0), v_val_224_);
        return v___x_225_;
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased(
    mut v_00_u03b1_226_: *mut leanh::LeanObject,
    mut v_m_227_: *mut leanh::LeanObject,
    mut v_inst_228_: *mut leanh::LeanObject,
    mut v_00_u03b2_229_: *mut leanh::LeanObject,
    mut v_inst_230_: *mut leanh::LeanObject,
    mut v_f_231_: *mut leanh::LeanObject,
    mut v_a_232_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_233_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_233_ = l___private_Init_While_0__whileM_erased___redArg(v_inst_228_, v_f_231_, v_a_232_);
    return v___x_233_;
}
pub unsafe fn l_Lean_Loop_toCtorIdx(
    mut v_x_234_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_235_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_235_ = leanh::lean_unsigned_to_nat(0);
    return v___x_235_;
}
pub unsafe fn l_Lean_Loop_forIn___redArg___lam__0(
    mut v_toPure_236_: *mut leanh::LeanObject,
    mut v_____do__lift_237_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_241_: u8 = 0;
    let mut v___x_243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_246_: u8 = 0;
    let mut v_a_247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_250_: u8 = 0;
    let mut v___x_252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_255_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_____do__lift_237_) == 0 {
                    v_a_238_ = leanh::lean_ctor_get(v_____do__lift_237_, 0);
                    v_isSharedCheck_246_ =
                        (!leanh::lean_is_exclusive(v_____do__lift_237_)) as u8;
                    if v_isSharedCheck_246_ == 0 {
                        v___x_240_ = v_____do__lift_237_;
                        v_isShared_241_ = v_isSharedCheck_246_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_238_);
                        leanh::lean_dec(v_____do__lift_237_);
                        v___x_240_ = leanh::lean_box(0);
                        v_isShared_241_ = v_isSharedCheck_246_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_247_ = leanh::lean_ctor_get(v_____do__lift_237_, 0);
                    v_isSharedCheck_255_ =
                        (!leanh::lean_is_exclusive(v_____do__lift_237_)) as u8;
                    if v_isSharedCheck_255_ == 0 {
                        v___x_249_ = v_____do__lift_237_;
                        v_isShared_250_ = v_isSharedCheck_255_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_247_);
                        leanh::lean_dec(v_____do__lift_237_);
                        v___x_249_ = leanh::lean_box(0);
                        v_isShared_250_ = v_isSharedCheck_255_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_241_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_240_, 1);
                    v___x_243_ = v___x_240_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_245_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_245_, 0, v_a_238_);
                    v___x_243_ = v_reuseFailAlloc_245_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_244_ = leanh::lean_apply_2(
                    v_toPure_236_,
                    leanh::lean_box(0),
                    v___x_243_,
                );
                return v___x_244_;
            }
            3 => {
                if v_isShared_250_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_249_, 0);
                    v___x_252_ = v___x_249_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_254_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_254_, 0, v_a_247_);
                    v___x_252_ = v_reuseFailAlloc_254_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_253_ = leanh::lean_apply_2(
                    v_toPure_236_,
                    leanh::lean_box(0),
                    v___x_252_,
                );
                return v___x_253_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Loop_forIn___redArg___lam__1(
    mut v_f_256_: *mut leanh::LeanObject,
    mut v_toBind_257_: *mut leanh::LeanObject,
    mut v___f_258_: *mut leanh::LeanObject,
    mut v_b_259_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_262_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_260_ = leanh::lean_box(0);
    v___x_261_ = leanh::lean_apply_2(v_f_256_, v___x_260_, v_b_259_);
    v___x_262_ = leanh::lean_apply_4(
        v_toBind_257_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_261_,
        v___f_258_,
    );
    return v___x_262_;
}
pub unsafe fn l_Lean_Loop_forIn___redArg(
    mut v_inst_263_: *mut leanh::LeanObject,
    mut v_init_264_: *mut leanh::LeanObject,
    mut v_f_265_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_271_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_266_ = leanh::lean_ctor_get(v_inst_263_, 0);
    v_toBind_267_ = leanh::lean_ctor_get(v_inst_263_, 1);
    v_toPure_268_ = leanh::lean_ctor_get(v_toApplicative_266_, 1);
    leanh::lean_inc(v_toPure_268_);
    v___f_269_ = leanh::lean_alloc_closure(
        l_Lean_Loop_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_269_, 0, v_toPure_268_);
    leanh::lean_inc(v_toBind_267_);
    v___f_270_ = leanh::lean_alloc_closure(
        l_Lean_Loop_forIn___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_270_, 0, v_f_265_);
    leanh::lean_closure_set(v___f_270_, 1, v_toBind_267_);
    leanh::lean_closure_set(v___f_270_, 2, v___f_269_);
    v___x_271_ =
        l___private_Init_While_0__whileM_erased___redArg(v_inst_263_, v___f_270_, v_init_264_);
    return v___x_271_;
}
pub unsafe fn l_Lean_Loop_forIn(
    mut v_00_u03b2_272_: *mut leanh::LeanObject,
    mut v_m_273_: *mut leanh::LeanObject,
    mut v_inst_274_: *mut leanh::LeanObject,
    mut v_x_275_: *mut leanh::LeanObject,
    mut v_init_276_: *mut leanh::LeanObject,
    mut v_f_277_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_283_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_278_ = leanh::lean_ctor_get(v_inst_274_, 0);
    v_toBind_279_ = leanh::lean_ctor_get(v_inst_274_, 1);
    v_toPure_280_ = leanh::lean_ctor_get(v_toApplicative_278_, 1);
    leanh::lean_inc(v_toPure_280_);
    v___f_281_ = leanh::lean_alloc_closure(
        l_Lean_Loop_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_281_, 0, v_toPure_280_);
    leanh::lean_inc(v_toBind_279_);
    v___f_282_ = leanh::lean_alloc_closure(
        l_Lean_Loop_forIn___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_282_, 0, v_f_277_);
    leanh::lean_closure_set(v___f_282_, 1, v_toBind_279_);
    leanh::lean_closure_set(v___f_282_, 2, v___f_281_);
    v___x_283_ =
        l___private_Init_While_0__whileM_erased___redArg(v_inst_274_, v___f_282_, v_init_276_);
    return v___x_283_;
}
pub unsafe fn l_Lean_instForInLoopUnitOfMonad___redArg___lam__1(
    mut v___y_284_: *mut leanh::LeanObject,
    mut v_toBind_285_: *mut leanh::LeanObject,
    mut v___f_286_: *mut leanh::LeanObject,
    mut v_b_287_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_290_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_288_ = leanh::lean_box(0);
    v___x_289_ = leanh::lean_apply_2(v___y_284_, v___x_288_, v_b_287_);
    v___x_290_ = leanh::lean_apply_4(
        v_toBind_285_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_289_,
        v___f_286_,
    );
    return v___x_290_;
}
pub unsafe fn l_Lean_instForInLoopUnitOfMonad___redArg___lam__0(
    mut v_inst_291_: *mut leanh::LeanObject,
    mut v_00_u03b2_292_: *mut leanh::LeanObject,
    mut v___y_293_: *mut leanh::LeanObject,
    mut v___y_294_: *mut leanh::LeanObject,
    mut v___y_295_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_301_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_296_ = leanh::lean_ctor_get(v_inst_291_, 0);
    v_toBind_297_ = leanh::lean_ctor_get(v_inst_291_, 1);
    v_toPure_298_ = leanh::lean_ctor_get(v_toApplicative_296_, 1);
    leanh::lean_inc(v_toPure_298_);
    v___f_299_ = leanh::lean_alloc_closure(
        l_Lean_Loop_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_299_, 0, v_toPure_298_);
    leanh::lean_inc(v_toBind_297_);
    v___f_300_ = leanh::lean_alloc_closure(
        l_Lean_instForInLoopUnitOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_300_, 0, v___y_295_);
    leanh::lean_closure_set(v___f_300_, 1, v_toBind_297_);
    leanh::lean_closure_set(v___f_300_, 2, v___f_299_);
    v___x_301_ =
        l___private_Init_While_0__whileM_erased___redArg(v_inst_291_, v___f_300_, v___y_294_);
    return v___x_301_;
}
pub unsafe fn l_Lean_instForInLoopUnitOfMonad___redArg(
    mut v_inst_302_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_303_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_303_ = leanh::lean_alloc_closure(
        l_Lean_instForInLoopUnitOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_303_, 0, v_inst_302_);
    return v___f_303_;
}
pub unsafe fn l_Lean_instForInLoopUnitOfMonad(
    mut v_m_304_: *mut leanh::LeanObject,
    mut v_inst_305_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_306_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_306_ = leanh::lean_alloc_closure(
        l_Lean_instForInLoopUnitOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_306_, 0, v_inst_305_);
    return v___f_306_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_While(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Core(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Classical(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_While(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_While(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Core(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Classical(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_While(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_While(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_While(builtin);
}