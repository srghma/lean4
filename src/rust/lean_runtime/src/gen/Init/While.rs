// Lean compiler output
// Module: Init.While
// Imports: Init.Core Init.Classical
use crate::r#gen::Init::Classical::{initialize_Init_Classical, runtime_initialize_Init_Classical};
use crate::r#gen::Init::Core::{initialize_Init_Core, runtime_initialize_Init_Core};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set,
    lean_ctor_set_tag, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_tag,
    lean_unsigned_to_nat,
};
pub unsafe fn l_whileM_body___redArg___lam__0(
    mut v_recur_154_: *mut LeanObject,
    mut v_toPure_155_: *mut LeanObject,
    mut v_____do__lift_156_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_156_) == 0 {
        let mut v_val_157_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_158_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_155_);
        v_val_157_ = lean_ctor_get(v_____do__lift_156_, 0);
        lean_inc(v_val_157_);
        lean_dec_ref_known(v_____do__lift_156_, 1);
        v___x_158_ = lean_apply_1(v_recur_154_, v_val_157_);
        return v___x_158_;
    } else {
        let mut v_val_159_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_160_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_recur_154_);
        v_val_159_ = lean_ctor_get(v_____do__lift_156_, 0);
        lean_inc(v_val_159_);
        lean_dec_ref_known(v_____do__lift_156_, 1);
        v___x_160_ = lean_apply_2(v_toPure_155_, lean_box(0), v_val_159_);
        return v___x_160_;
    }
}
pub unsafe fn l_whileM_body___redArg(
    mut v_inst_161_: *mut LeanObject,
    mut v_f_162_: *mut LeanObject,
    mut v_recur_163_: *mut LeanObject,
    mut v_a_164_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_170_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_165_ = lean_ctor_get(v_inst_161_, 0);
    lean_inc_ref(v_toApplicative_165_);
    v_toBind_166_ = lean_ctor_get(v_inst_161_, 1);
    lean_inc(v_toBind_166_);
    lean_dec_ref(v_inst_161_);
    v_toPure_167_ = lean_ctor_get(v_toApplicative_165_, 1);
    lean_inc(v_toPure_167_);
    lean_dec_ref(v_toApplicative_165_);
    v___x_168_ = lean_apply_1(v_f_162_, v_a_164_);
    v___f_169_ = lean_alloc_closure(
        l_whileM_body___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_169_, 0, v_recur_163_);
    lean_closure_set(v___f_169_, 1, v_toPure_167_);
    v___x_170_ = lean_apply_4(
        v_toBind_166_,
        lean_box(0),
        lean_box(0),
        v___x_168_,
        v___f_169_,
    );
    return v___x_170_;
}
pub unsafe fn l_whileM_body(
    mut v_00_u03b1_171_: *mut LeanObject,
    mut v_m_172_: *mut LeanObject,
    mut v_inst_173_: *mut LeanObject,
    mut v_00_u03b2_174_: *mut LeanObject,
    mut v_f_175_: *mut LeanObject,
    mut v_recur_176_: *mut LeanObject,
    mut v_a_177_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_183_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_178_ = lean_ctor_get(v_inst_173_, 0);
    lean_inc_ref(v_toApplicative_178_);
    v_toBind_179_ = lean_ctor_get(v_inst_173_, 1);
    lean_inc(v_toBind_179_);
    lean_dec_ref(v_inst_173_);
    v_toPure_180_ = lean_ctor_get(v_toApplicative_178_, 1);
    lean_inc(v_toPure_180_);
    lean_dec_ref(v_toApplicative_178_);
    v___x_181_ = lean_apply_1(v_f_175_, v_a_177_);
    v___f_182_ = lean_alloc_closure(
        l_whileM_body___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_182_, 0, v_recur_176_);
    lean_closure_set(v___f_182_, 1, v_toPure_180_);
    v___x_183_ = lean_apply_4(
        v_toBind_179_,
        lean_box(0),
        lean_box(0),
        v___x_181_,
        v___f_182_,
    );
    return v___x_183_;
}
pub unsafe fn l___private_Init_While_0__whileM_impl___redArg(
    mut v_inst_184_: *mut LeanObject,
    mut v_f_185_: *mut LeanObject,
    mut v_a_186_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_192_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_187_ = lean_ctor_get(v_inst_184_, 0);
    v_toBind_188_ = lean_ctor_get(v_inst_184_, 1);
    lean_inc(v_toBind_188_);
    v_toPure_189_ = lean_ctor_get(v_toApplicative_187_, 1);
    lean_inc(v_toPure_189_);
    lean_inc(v_f_185_);
    v___x_190_ = lean_apply_1(v_f_185_, v_a_186_);
    v___f_191_ = lean_alloc_closure(
        l___private_Init_While_0__whileM_impl___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_191_, 0, v_inst_184_);
    lean_closure_set(v___f_191_, 1, v_f_185_);
    lean_closure_set(v___f_191_, 2, v_toPure_189_);
    v___x_192_ = lean_apply_4(
        v_toBind_188_,
        lean_box(0),
        lean_box(0),
        v___x_190_,
        v___f_191_,
    );
    return v___x_192_;
}
pub unsafe fn l___private_Init_While_0__whileM_impl___redArg___lam__0(
    mut v_inst_193_: *mut LeanObject,
    mut v_f_194_: *mut LeanObject,
    mut v_toPure_195_: *mut LeanObject,
    mut v_____do__lift_196_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_196_) == 0 {
        let mut v_val_197_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_198_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_195_);
        v_val_197_ = lean_ctor_get(v_____do__lift_196_, 0);
        lean_inc(v_val_197_);
        lean_dec_ref_known(v_____do__lift_196_, 1);
        v___x_198_ =
            l___private_Init_While_0__whileM_impl___redArg(v_inst_193_, v_f_194_, v_val_197_);
        return v___x_198_;
    } else {
        let mut v_val_199_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_200_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_f_194_);
        lean_dec_ref(v_inst_193_);
        v_val_199_ = lean_ctor_get(v_____do__lift_196_, 0);
        lean_inc(v_val_199_);
        lean_dec_ref_known(v_____do__lift_196_, 1);
        v___x_200_ = lean_apply_2(v_toPure_195_, lean_box(0), v_val_199_);
        return v___x_200_;
    }
}
pub unsafe fn l___private_Init_While_0__whileM_impl(
    mut v_00_u03b1_201_: *mut LeanObject,
    mut v_m_202_: *mut LeanObject,
    mut v_inst_203_: *mut LeanObject,
    mut v_00_u03b2_204_: *mut LeanObject,
    mut v_inst_205_: *mut LeanObject,
    mut v_f_206_: *mut LeanObject,
    mut v_a_207_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_208_: *mut LeanObject = core::ptr::null_mut();
    v___x_208_ = l___private_Init_While_0__whileM_impl___redArg(v_inst_203_, v_f_206_, v_a_207_);
    return v___x_208_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___redArg(
    mut v_inst_209_: *mut LeanObject,
    mut v_f_210_: *mut LeanObject,
    mut v_a_211_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_217_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_212_ = lean_ctor_get(v_inst_209_, 0);
    v_toBind_213_ = lean_ctor_get(v_inst_209_, 1);
    lean_inc(v_toBind_213_);
    v_toPure_214_ = lean_ctor_get(v_toApplicative_212_, 1);
    lean_inc(v_toPure_214_);
    lean_inc(v_f_210_);
    v___x_215_ = lean_apply_1(v_f_210_, v_a_211_);
    v___f_216_ = lean_alloc_closure(
        l___private_Init_While_0__whileM_erased___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_216_, 0, v_inst_209_);
    lean_closure_set(v___f_216_, 1, v_f_210_);
    lean_closure_set(v___f_216_, 2, v_toPure_214_);
    v___x_217_ = lean_apply_4(
        v_toBind_213_,
        lean_box(0),
        lean_box(0),
        v___x_215_,
        v___f_216_,
    );
    return v___x_217_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___redArg___lam__0(
    mut v_inst_218_: *mut LeanObject,
    mut v_f_219_: *mut LeanObject,
    mut v_toPure_220_: *mut LeanObject,
    mut v_____do__lift_221_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_221_) == 0 {
        let mut v_val_222_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_223_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_220_);
        v_val_222_ = lean_ctor_get(v_____do__lift_221_, 0);
        lean_inc(v_val_222_);
        lean_dec_ref_known(v_____do__lift_221_, 1);
        v___x_223_ =
            l___private_Init_While_0__whileM_erased___redArg(v_inst_218_, v_f_219_, v_val_222_);
        return v___x_223_;
    } else {
        let mut v_val_224_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_225_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_f_219_);
        lean_dec_ref(v_inst_218_);
        v_val_224_ = lean_ctor_get(v_____do__lift_221_, 0);
        lean_inc(v_val_224_);
        lean_dec_ref_known(v_____do__lift_221_, 1);
        v___x_225_ = lean_apply_2(v_toPure_220_, lean_box(0), v_val_224_);
        return v___x_225_;
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased(
    mut v_00_u03b1_226_: *mut LeanObject,
    mut v_m_227_: *mut LeanObject,
    mut v_inst_228_: *mut LeanObject,
    mut v_00_u03b2_229_: *mut LeanObject,
    mut v_inst_230_: *mut LeanObject,
    mut v_f_231_: *mut LeanObject,
    mut v_a_232_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_233_: *mut LeanObject = core::ptr::null_mut();
    v___x_233_ = l___private_Init_While_0__whileM_erased___redArg(v_inst_228_, v_f_231_, v_a_232_);
    return v___x_233_;
}
pub unsafe fn l_Lean_Loop_toCtorIdx(mut v_x_234_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_235_: *mut LeanObject = core::ptr::null_mut();
    v___x_235_ = lean_unsigned_to_nat(0);
    return v___x_235_;
}
pub unsafe fn l_Lean_Loop_forIn___redArg___lam__0(
    mut v_toPure_236_: *mut LeanObject,
    mut v_____do__lift_237_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_241_: u8 = 0;
    let mut v___x_243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_246_: u8 = 0;
    let mut v_a_247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_250_: u8 = 0;
    let mut v___x_252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_255_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_____do__lift_237_) == 0 {
                    v_a_238_ = lean_ctor_get(v_____do__lift_237_, 0);
                    v_isSharedCheck_246_ = (!lean_is_exclusive(v_____do__lift_237_)) as u8;
                    if v_isSharedCheck_246_ == 0 {
                        v___x_240_ = v_____do__lift_237_;
                        v_isShared_241_ = v_isSharedCheck_246_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_238_);
                        lean_dec(v_____do__lift_237_);
                        v___x_240_ = lean_box(0);
                        v_isShared_241_ = v_isSharedCheck_246_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_247_ = lean_ctor_get(v_____do__lift_237_, 0);
                    v_isSharedCheck_255_ = (!lean_is_exclusive(v_____do__lift_237_)) as u8;
                    if v_isSharedCheck_255_ == 0 {
                        v___x_249_ = v_____do__lift_237_;
                        v_isShared_250_ = v_isSharedCheck_255_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_247_);
                        lean_dec(v_____do__lift_237_);
                        v___x_249_ = lean_box(0);
                        v_isShared_250_ = v_isSharedCheck_255_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_241_ == 0 {
                    lean_ctor_set_tag(v___x_240_, 1);
                    v___x_243_ = v___x_240_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_245_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_245_, 0, v_a_238_);
                    v___x_243_ = v_reuseFailAlloc_245_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_244_ = lean_apply_2(v_toPure_236_, lean_box(0), v___x_243_);
                return v___x_244_;
            }
            3 => {
                if v_isShared_250_ == 0 {
                    lean_ctor_set_tag(v___x_249_, 0);
                    v___x_252_ = v___x_249_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_254_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_254_, 0, v_a_247_);
                    v___x_252_ = v_reuseFailAlloc_254_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_253_ = lean_apply_2(v_toPure_236_, lean_box(0), v___x_252_);
                return v___x_253_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Loop_forIn___redArg___lam__1(
    mut v_f_256_: *mut LeanObject,
    mut v_toBind_257_: *mut LeanObject,
    mut v___f_258_: *mut LeanObject,
    mut v_b_259_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_262_: *mut LeanObject = core::ptr::null_mut();
    v___x_260_ = lean_box(0);
    v___x_261_ = lean_apply_2(v_f_256_, v___x_260_, v_b_259_);
    v___x_262_ = lean_apply_4(
        v_toBind_257_,
        lean_box(0),
        lean_box(0),
        v___x_261_,
        v___f_258_,
    );
    return v___x_262_;
}
pub unsafe fn l_Lean_Loop_forIn___redArg(
    mut v_inst_263_: *mut LeanObject,
    mut v_init_264_: *mut LeanObject,
    mut v_f_265_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_271_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_266_ = lean_ctor_get(v_inst_263_, 0);
    v_toBind_267_ = lean_ctor_get(v_inst_263_, 1);
    v_toPure_268_ = lean_ctor_get(v_toApplicative_266_, 1);
    lean_inc(v_toPure_268_);
    v___f_269_ = lean_alloc_closure(
        l_Lean_Loop_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_269_, 0, v_toPure_268_);
    lean_inc(v_toBind_267_);
    v___f_270_ = lean_alloc_closure(
        l_Lean_Loop_forIn___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_270_, 0, v_f_265_);
    lean_closure_set(v___f_270_, 1, v_toBind_267_);
    lean_closure_set(v___f_270_, 2, v___f_269_);
    v___x_271_ =
        l___private_Init_While_0__whileM_erased___redArg(v_inst_263_, v___f_270_, v_init_264_);
    return v___x_271_;
}
pub unsafe fn l_Lean_Loop_forIn(
    mut v_00_u03b2_272_: *mut LeanObject,
    mut v_m_273_: *mut LeanObject,
    mut v_inst_274_: *mut LeanObject,
    mut v_x_275_: *mut LeanObject,
    mut v_init_276_: *mut LeanObject,
    mut v_f_277_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_283_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_278_ = lean_ctor_get(v_inst_274_, 0);
    v_toBind_279_ = lean_ctor_get(v_inst_274_, 1);
    v_toPure_280_ = lean_ctor_get(v_toApplicative_278_, 1);
    lean_inc(v_toPure_280_);
    v___f_281_ = lean_alloc_closure(
        l_Lean_Loop_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_281_, 0, v_toPure_280_);
    lean_inc(v_toBind_279_);
    v___f_282_ = lean_alloc_closure(
        l_Lean_Loop_forIn___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_282_, 0, v_f_277_);
    lean_closure_set(v___f_282_, 1, v_toBind_279_);
    lean_closure_set(v___f_282_, 2, v___f_281_);
    v___x_283_ =
        l___private_Init_While_0__whileM_erased___redArg(v_inst_274_, v___f_282_, v_init_276_);
    return v___x_283_;
}
pub unsafe fn l_Lean_instForInLoopUnitOfMonad___redArg___lam__1(
    mut v___y_284_: *mut LeanObject,
    mut v_toBind_285_: *mut LeanObject,
    mut v___f_286_: *mut LeanObject,
    mut v_b_287_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_290_: *mut LeanObject = core::ptr::null_mut();
    v___x_288_ = lean_box(0);
    v___x_289_ = lean_apply_2(v___y_284_, v___x_288_, v_b_287_);
    v___x_290_ = lean_apply_4(
        v_toBind_285_,
        lean_box(0),
        lean_box(0),
        v___x_289_,
        v___f_286_,
    );
    return v___x_290_;
}
pub unsafe fn l_Lean_instForInLoopUnitOfMonad___redArg___lam__0(
    mut v_inst_291_: *mut LeanObject,
    mut v_00_u03b2_292_: *mut LeanObject,
    mut v___y_293_: *mut LeanObject,
    mut v___y_294_: *mut LeanObject,
    mut v___y_295_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_301_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_296_ = lean_ctor_get(v_inst_291_, 0);
    v_toBind_297_ = lean_ctor_get(v_inst_291_, 1);
    v_toPure_298_ = lean_ctor_get(v_toApplicative_296_, 1);
    lean_inc(v_toPure_298_);
    v___f_299_ = lean_alloc_closure(
        l_Lean_Loop_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_299_, 0, v_toPure_298_);
    lean_inc(v_toBind_297_);
    v___f_300_ = lean_alloc_closure(
        l_Lean_instForInLoopUnitOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_300_, 0, v___y_295_);
    lean_closure_set(v___f_300_, 1, v_toBind_297_);
    lean_closure_set(v___f_300_, 2, v___f_299_);
    v___x_301_ =
        l___private_Init_While_0__whileM_erased___redArg(v_inst_291_, v___f_300_, v___y_294_);
    return v___x_301_;
}
pub unsafe fn l_Lean_instForInLoopUnitOfMonad___redArg(
    mut v_inst_302_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_303_: *mut LeanObject = core::ptr::null_mut();
    v___f_303_ = lean_alloc_closure(
        l_Lean_instForInLoopUnitOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_303_, 0, v_inst_302_);
    return v___f_303_;
}
pub unsafe fn l_Lean_instForInLoopUnitOfMonad(
    mut v_m_304_: *mut LeanObject,
    mut v_inst_305_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_306_: *mut LeanObject = core::ptr::null_mut();
    v___f_306_ = lean_alloc_closure(
        l_Lean_instForInLoopUnitOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_306_, 0, v_inst_305_);
    return v___f_306_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_While(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Core(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Classical(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_While(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_While(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Core(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Classical(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_While(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_While(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_While(builtin);
}
