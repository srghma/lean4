// Lean compiler output
// Module: Std.Data.Iterators.Combinators.Monadic.Drop
// Imports: Init.Data.Iterators.Consumers.Loop
use crate::r#gen::Init::Data::Iterators::Consumers::Loop::{
    initialize_Init_Data_Iterators_Consumers_Loop,
    runtime_initialize_Init_Data_Iterators_Consumers_Loop,
};
use crate::r#gen::Init::WFExtrinsicFix::l_WellFounded_opaqueFix_u2083___redArg;
use crate::ffi::{lean_nat_dec_eq, lean_nat_sub};
pub unsafe fn l_Std_IterM_drop___redArg(
    mut v_n_160_: *mut crate::leanh::LeanObject,
    mut v_it_161_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_162_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_162_, 0, v_n_160_);
    crate::leanh::lean_ctor_set(v___x_162_, 1, v_it_161_);
    return v___x_162_;
}
pub unsafe fn l_Std_IterM_drop(
    mut v_00_u03b1_163_: *mut crate::leanh::LeanObject,
    mut v_m_164_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_165_: *mut crate::leanh::LeanObject,
    mut v_n_166_: *mut crate::leanh::LeanObject,
    mut v_it_167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_168_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_168_, 0, v_n_166_);
    crate::leanh::lean_ctor_set(v___x_168_, 1, v_it_167_);
    return v___x_168_;
}
pub unsafe fn l_Std_Iterators_Types_Drop_instIterator___redArg___lam__0(
    mut v_remaining_169_: *mut crate::leanh::LeanObject,
    mut v_toPure_170_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_171_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_it_172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_176_: u8 = 0;
    let mut v_zero_177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_178_: u8 = 0;
    let mut v___x_179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_189_: u8 = 0;
    let mut v_it_190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_193_: u8 = 0;
    let mut v___x_194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_199_: u8 = 0;
    let mut v___x_200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_____do__lift_171_) {
                0 => {
                    v_it_172_ = crate::leanh::lean_ctor_get(v_____do__lift_171_, 0);
                    v_out_173_ = crate::leanh::lean_ctor_get(v_____do__lift_171_, 1);
                    v_isSharedCheck_189_ =
                        (!crate::leanh::lean_is_exclusive(v_____do__lift_171_)) as u8;
                    if v_isSharedCheck_189_ == 0 {
                        v___x_175_ = v_____do__lift_171_;
                        v_isShared_176_ = v_isSharedCheck_189_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_out_173_);
                        crate::leanh::lean_inc(v_it_172_);
                        crate::leanh::lean_dec(v_____do__lift_171_);
                        v___x_175_ = crate::leanh::lean_box(0);
                        v_isShared_176_ = v_isSharedCheck_189_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_it_190_ = crate::leanh::lean_ctor_get(v_____do__lift_171_, 0);
                    v_isSharedCheck_199_ =
                        (!crate::leanh::lean_is_exclusive(v_____do__lift_171_)) as u8;
                    if v_isSharedCheck_199_ == 0 {
                        v___x_192_ = v_____do__lift_171_;
                        v_isShared_193_ = v_isSharedCheck_199_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_it_190_);
                        crate::leanh::lean_dec(v_____do__lift_171_);
                        v___x_192_ = crate::leanh::lean_box(0);
                        v_isShared_193_ = v_isSharedCheck_199_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    crate::leanh::lean_dec(v_remaining_169_);
                    v___x_200_ = crate::leanh::lean_box(2);
                    v___x_201_ = crate::leanh::lean_apply_2(
                        v_toPure_170_,
                        crate::leanh::lean_box(0),
                        v___x_200_,
                    );
                    return v___x_201_;
                }
            },
            1 => {
                v_zero_177_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_178_ = lean_nat_dec_eq(v_remaining_169_, v_zero_177_);
                if v_isZero_178_ == 1 {
                    crate::leanh::lean_dec(v_remaining_169_);
                    v___x_179_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_179_, 0, v_zero_177_);
                    crate::leanh::lean_ctor_set(v___x_179_, 1, v_it_172_);
                    if v_isShared_176_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_175_, 0, v___x_179_);
                        v___x_181_ = v___x_175_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_183_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_183_, 0, v___x_179_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_183_, 1, v_out_173_);
                        v___x_181_ = v_reuseFailAlloc_183_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_175_);
                    crate::leanh::lean_dec(v_out_173_);
                    v_one_184_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_185_ = lean_nat_sub(v_remaining_169_, v_one_184_);
                    crate::leanh::lean_dec(v_remaining_169_);
                    v___x_186_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_186_, 0, v_n_185_);
                    crate::leanh::lean_ctor_set(v___x_186_, 1, v_it_172_);
                    v___x_187_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_187_, 0, v___x_186_);
                    v___x_188_ = crate::leanh::lean_apply_2(
                        v_toPure_170_,
                        crate::leanh::lean_box(0),
                        v___x_187_,
                    );
                    return v___x_188_;
                }
            }
            2 => {
                v___x_182_ = crate::leanh::lean_apply_2(
                    v_toPure_170_,
                    crate::leanh::lean_box(0),
                    v___x_181_,
                );
                return v___x_182_;
            }
            3 => {
                v___x_194_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_194_, 0, v_remaining_169_);
                crate::leanh::lean_ctor_set(v___x_194_, 1, v_it_190_);
                if v_isShared_193_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_192_, 0, v___x_194_);
                    v___x_196_ = v___x_192_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_198_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_198_, 0, v___x_194_);
                    v___x_196_ = v_reuseFailAlloc_198_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_197_ = crate::leanh::lean_apply_2(
                    v_toPure_170_,
                    crate::leanh::lean_box(0),
                    v___x_196_,
                );
                return v___x_197_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Iterators_Types_Drop_instIterator___redArg___lam__1(
    mut v_toPure_202_: *mut crate::leanh::LeanObject,
    mut v_inst_203_: *mut crate::leanh::LeanObject,
    mut v_toBind_204_: *mut crate::leanh::LeanObject,
    mut v_it_205_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_remaining_206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inner_207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_remaining_206_ = crate::leanh::lean_ctor_get(v_it_205_, 0);
    crate::leanh::lean_inc(v_remaining_206_);
    v_inner_207_ = crate::leanh::lean_ctor_get(v_it_205_, 1);
    crate::leanh::lean_inc(v_inner_207_);
    crate::leanh::lean_dec_ref(v_it_205_);
    v___f_208_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_Types_Drop_instIterator___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_208_, 0, v_remaining_206_);
    crate::leanh::lean_closure_set(v___f_208_, 1, v_toPure_202_);
    v___x_209_ = crate::leanh::lean_apply_1(v_inst_203_, v_inner_207_);
    v___x_210_ = crate::leanh::lean_apply_4(
        v_toBind_204_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_209_,
        v___f_208_,
    );
    return v___x_210_;
}
pub unsafe fn l_Std_Iterators_Types_Drop_instIterator___redArg(
    mut v_inst_211_: *mut crate::leanh::LeanObject,
    mut v_inst_212_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_213_ = crate::leanh::lean_ctor_get(v_inst_211_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_213_);
    v_toBind_214_ = crate::leanh::lean_ctor_get(v_inst_211_, 1);
    crate::leanh::lean_inc(v_toBind_214_);
    crate::leanh::lean_dec_ref(v_inst_211_);
    v_toPure_215_ = crate::leanh::lean_ctor_get(v_toApplicative_213_, 1);
    crate::leanh::lean_inc(v_toPure_215_);
    crate::leanh::lean_dec_ref(v_toApplicative_213_);
    v___f_216_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_Types_Drop_instIterator___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_216_, 0, v_toPure_215_);
    crate::leanh::lean_closure_set(v___f_216_, 1, v_inst_212_);
    crate::leanh::lean_closure_set(v___f_216_, 2, v_toBind_214_);
    return v___f_216_;
}
pub unsafe fn l_Std_Iterators_Types_Drop_instIterator(
    mut v_00_u03b1_217_: *mut crate::leanh::LeanObject,
    mut v_m_218_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_219_: *mut crate::leanh::LeanObject,
    mut v_inst_220_: *mut crate::leanh::LeanObject,
    mut v_inst_221_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_222_ = l_Std_Iterators_Types_Drop_instIterator___redArg(v_inst_220_, v_inst_221_);
    return v___x_222_;
}
pub unsafe fn l___private_Std_Data_Iterators_Combinators_Monadic_Drop_0__Std_Iterators_Types_Drop_instFinitenessRelation(
    mut v_00_u03b1_223_: *mut crate::leanh::LeanObject,
    mut v_m_224_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_225_: *mut crate::leanh::LeanObject,
    mut v_inst_226_: *mut crate::leanh::LeanObject,
    mut v_inst_227_: *mut crate::leanh::LeanObject,
    mut v_inst_228_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_229_ = crate::leanh::lean_box(0);
    return v___x_229_;
}
pub unsafe fn l___private_Std_Data_Iterators_Combinators_Monadic_Drop_0__Std_Iterators_Types_Drop_instFinitenessRelation___boxed(
    mut v_00_u03b1_230_: *mut crate::leanh::LeanObject,
    mut v_m_231_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_232_: *mut crate::leanh::LeanObject,
    mut v_inst_233_: *mut crate::leanh::LeanObject,
    mut v_inst_234_: *mut crate::leanh::LeanObject,
    mut v_inst_235_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_236_ = l___private_Std_Data_Iterators_Combinators_Monadic_Drop_0__Std_Iterators_Types_Drop_instFinitenessRelation(v_00_u03b1_230_, v_m_231_, v_00_u03b2_232_, v_inst_233_, v_inst_234_, v_inst_235_);
    crate::leanh::lean_dec_ref(v_inst_234_);
    crate::leanh::lean_dec(v_inst_233_);
    return v_res_236_;
}
pub unsafe fn l___private_Std_Data_Iterators_Combinators_Monadic_Drop_0__Std_Iterators_Types_Drop_instProductivenessRelation(
    mut v_00_u03b1_237_: *mut crate::leanh::LeanObject,
    mut v_m_238_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_239_: *mut crate::leanh::LeanObject,
    mut v_inst_240_: *mut crate::leanh::LeanObject,
    mut v_inst_241_: *mut crate::leanh::LeanObject,
    mut v_inst_242_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_243_ = crate::leanh::lean_box(0);
    return v___x_243_;
}
pub unsafe fn l___private_Std_Data_Iterators_Combinators_Monadic_Drop_0__Std_Iterators_Types_Drop_instProductivenessRelation___boxed(
    mut v_00_u03b1_244_: *mut crate::leanh::LeanObject,
    mut v_m_245_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_246_: *mut crate::leanh::LeanObject,
    mut v_inst_247_: *mut crate::leanh::LeanObject,
    mut v_inst_248_: *mut crate::leanh::LeanObject,
    mut v_inst_249_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_250_ = l___private_Std_Data_Iterators_Combinators_Monadic_Drop_0__Std_Iterators_Types_Drop_instProductivenessRelation(v_00_u03b1_244_, v_m_245_, v_00_u03b2_246_, v_inst_247_, v_inst_248_, v_inst_249_);
    crate::leanh::lean_dec_ref(v_inst_248_);
    crate::leanh::lean_dec(v_inst_247_);
    return v_res_250_;
}
pub unsafe fn l_Std_Iterators_Types_Drop_instIteratorLoop___redArg___lam__0(
    mut v_toPure_251_: *mut crate::leanh::LeanObject,
    mut v_recur_252_: *mut crate::leanh::LeanObject,
    mut v_it_253_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_254_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_254_) == 0 {
        let mut v_a_255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_it_253_);
        crate::leanh::lean_dec(v_recur_252_);
        v_a_255_ = crate::leanh::lean_ctor_get(v_____do__lift_254_, 0);
        crate::leanh::lean_inc(v_a_255_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_254_, 1);
        v___x_256_ = crate::leanh::lean_apply_2(v_toPure_251_, crate::leanh::lean_box(0), v_a_255_);
        return v___x_256_;
    } else {
        let mut v_a_257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_251_);
        v_a_257_ = crate::leanh::lean_ctor_get(v_____do__lift_254_, 0);
        crate::leanh::lean_inc(v_a_257_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_254_, 1);
        v___x_258_ = crate::leanh::lean_apply_4(
            v_recur_252_,
            v_it_253_,
            v_a_257_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_258_;
    }
}
pub unsafe fn l_Std_Iterators_Types_Drop_instIteratorLoop___redArg___lam__1(
    mut v_toPure_259_: *mut crate::leanh::LeanObject,
    mut v_recur_260_: *mut crate::leanh::LeanObject,
    mut v___y_261_: *mut crate::leanh::LeanObject,
    mut v_acc_262_: *mut crate::leanh::LeanObject,
    mut v_toBind_263_: *mut crate::leanh::LeanObject,
    mut v_s_264_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_s_264_) {
        0 => {
            let mut v_it_265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_it_265_ = crate::leanh::lean_ctor_get(v_s_264_, 0);
            crate::leanh::lean_inc(v_it_265_);
            v_out_266_ = crate::leanh::lean_ctor_get(v_s_264_, 1);
            crate::leanh::lean_inc(v_out_266_);
            crate::leanh::lean_dec_ref_known(v_s_264_, 2);
            v___f_267_ = crate::leanh::lean_alloc_closure(
                l_Std_Iterators_Types_Drop_instIteratorLoop___redArg___lam__0
                    as *mut core::ffi::c_void,
                4,
                3,
            );
            crate::leanh::lean_closure_set(v___f_267_, 0, v_toPure_259_);
            crate::leanh::lean_closure_set(v___f_267_, 1, v_recur_260_);
            crate::leanh::lean_closure_set(v___f_267_, 2, v_it_265_);
            v___x_268_ = crate::leanh::lean_apply_3(
                v___y_261_,
                v_out_266_,
                crate::leanh::lean_box(0),
                v_acc_262_,
            );
            v___x_269_ = crate::leanh::lean_apply_4(
                v_toBind_263_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_268_,
                v___f_267_,
            );
            return v___x_269_;
        }
        1 => {
            let mut v_it_270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_toBind_263_);
            crate::leanh::lean_dec(v___y_261_);
            crate::leanh::lean_dec(v_toPure_259_);
            v_it_270_ = crate::leanh::lean_ctor_get(v_s_264_, 0);
            crate::leanh::lean_inc(v_it_270_);
            crate::leanh::lean_dec_ref_known(v_s_264_, 1);
            v___x_271_ = crate::leanh::lean_apply_4(
                v_recur_260_,
                v_it_270_,
                v_acc_262_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_271_;
        }
        _ => {
            let mut v___x_272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_toBind_263_);
            crate::leanh::lean_dec(v___y_261_);
            crate::leanh::lean_dec(v_recur_260_);
            v___x_272_ =
                crate::leanh::lean_apply_2(v_toPure_259_, crate::leanh::lean_box(0), v_acc_262_);
            return v___x_272_;
        }
    }
}
pub unsafe fn l_Std_Iterators_Types_Drop_instIteratorLoop___redArg___lam__3(
    mut v_inst_273_: *mut crate::leanh::LeanObject,
    mut v_toPure_274_: *mut crate::leanh::LeanObject,
    mut v___y_275_: *mut crate::leanh::LeanObject,
    mut v_toBind_276_: *mut crate::leanh::LeanObject,
    mut v_inst_277_: *mut crate::leanh::LeanObject,
    mut v_lift_278_: *mut crate::leanh::LeanObject,
    mut v_it_279_: *mut crate::leanh::LeanObject,
    mut v_acc_280_: *mut crate::leanh::LeanObject,
    mut v_hP_281_: *mut crate::leanh::LeanObject,
    mut v_recur_282_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_remaining_286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inner_287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_283_ = crate::leanh::lean_ctor_get(v_inst_273_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_283_);
    v_toBind_284_ = crate::leanh::lean_ctor_get(v_inst_273_, 1);
    crate::leanh::lean_inc(v_toBind_284_);
    crate::leanh::lean_dec_ref(v_inst_273_);
    v_toPure_285_ = crate::leanh::lean_ctor_get(v_toApplicative_283_, 1);
    crate::leanh::lean_inc(v_toPure_285_);
    crate::leanh::lean_dec_ref(v_toApplicative_283_);
    v_remaining_286_ = crate::leanh::lean_ctor_get(v_it_279_, 0);
    crate::leanh::lean_inc(v_remaining_286_);
    v_inner_287_ = crate::leanh::lean_ctor_get(v_it_279_, 1);
    crate::leanh::lean_inc(v_inner_287_);
    crate::leanh::lean_dec_ref(v_it_279_);
    v___f_288_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_Types_Drop_instIteratorLoop___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___f_288_, 0, v_toPure_274_);
    crate::leanh::lean_closure_set(v___f_288_, 1, v_recur_282_);
    crate::leanh::lean_closure_set(v___f_288_, 2, v___y_275_);
    crate::leanh::lean_closure_set(v___f_288_, 3, v_acc_280_);
    crate::leanh::lean_closure_set(v___f_288_, 4, v_toBind_276_);
    v___f_289_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_Types_Drop_instIterator___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_289_, 0, v_remaining_286_);
    crate::leanh::lean_closure_set(v___f_289_, 1, v_toPure_285_);
    v___x_290_ = crate::leanh::lean_apply_1(v_inst_277_, v_inner_287_);
    v___x_291_ = crate::leanh::lean_apply_4(
        v_toBind_284_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_290_,
        v___f_289_,
    );
    v___x_292_ = crate::leanh::lean_apply_4(
        v_lift_278_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_288_,
        v___x_291_,
    );
    return v___x_292_;
}
pub unsafe fn l_Std_Iterators_Types_Drop_instIteratorLoop___redArg___lam__2(
    mut v_inst_293_: *mut crate::leanh::LeanObject,
    mut v_inst_294_: *mut crate::leanh::LeanObject,
    mut v_inst_295_: *mut crate::leanh::LeanObject,
    mut v_lift_296_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_297_: *mut crate::leanh::LeanObject,
    mut v_Pl_298_: *mut crate::leanh::LeanObject,
    mut v_it_299_: *mut crate::leanh::LeanObject,
    mut v_init_300_: *mut crate::leanh::LeanObject,
    mut v___y_301_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_302_ = crate::leanh::lean_ctor_get(v_inst_293_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_302_);
    v_toBind_303_ = crate::leanh::lean_ctor_get(v_inst_293_, 1);
    crate::leanh::lean_inc(v_toBind_303_);
    crate::leanh::lean_dec_ref(v_inst_293_);
    v_toPure_304_ = crate::leanh::lean_ctor_get(v_toApplicative_302_, 1);
    crate::leanh::lean_inc(v_toPure_304_);
    crate::leanh::lean_dec_ref(v_toApplicative_302_);
    v___f_305_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_Types_Drop_instIteratorLoop___redArg___lam__3 as *mut core::ffi::c_void,
        10,
        6,
    );
    crate::leanh::lean_closure_set(v___f_305_, 0, v_inst_294_);
    crate::leanh::lean_closure_set(v___f_305_, 1, v_toPure_304_);
    crate::leanh::lean_closure_set(v___f_305_, 2, v___y_301_);
    crate::leanh::lean_closure_set(v___f_305_, 3, v_toBind_303_);
    crate::leanh::lean_closure_set(v___f_305_, 4, v_inst_295_);
    crate::leanh::lean_closure_set(v___f_305_, 5, v_lift_296_);
    v___x_306_ = l_WellFounded_opaqueFix_u2083___redArg(
        v___f_305_,
        v_it_299_,
        v_init_300_,
        crate::leanh::lean_box(0),
    );
    return v___x_306_;
}
pub unsafe fn l_Std_Iterators_Types_Drop_instIteratorLoop___redArg(
    mut v_inst_307_: *mut crate::leanh::LeanObject,
    mut v_inst_308_: *mut crate::leanh::LeanObject,
    mut v_inst_309_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_310_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_Types_Drop_instIteratorLoop___redArg___lam__2 as *mut core::ffi::c_void,
        9,
        3,
    );
    crate::leanh::lean_closure_set(v___f_310_, 0, v_inst_308_);
    crate::leanh::lean_closure_set(v___f_310_, 1, v_inst_307_);
    crate::leanh::lean_closure_set(v___f_310_, 2, v_inst_309_);
    return v___f_310_;
}
pub unsafe fn l_Std_Iterators_Types_Drop_instIteratorLoop(
    mut v_00_u03b1_311_: *mut crate::leanh::LeanObject,
    mut v_m_312_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_313_: *mut crate::leanh::LeanObject,
    mut v_n_314_: *mut crate::leanh::LeanObject,
    mut v_inst_315_: *mut crate::leanh::LeanObject,
    mut v_inst_316_: *mut crate::leanh::LeanObject,
    mut v_inst_317_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_318_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_Types_Drop_instIteratorLoop___redArg___lam__2 as *mut core::ffi::c_void,
        9,
        3,
    );
    crate::leanh::lean_closure_set(v___f_318_, 0, v_inst_316_);
    crate::leanh::lean_closure_set(v___f_318_, 1, v_inst_315_);
    crate::leanh::lean_closure_set(v___f_318_, 2, v_inst_317_);
    return v___f_318_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_Iterators_Combinators_Monadic_Drop(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Consumers_Loop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_Iterators_Combinators_Monadic_Drop(
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
pub unsafe fn initialize_Std_Data_Iterators_Combinators_Monadic_Drop(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Consumers_Loop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Combinators_Monadic_Drop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_Iterators_Combinators_Monadic_Drop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Data_Iterators_Combinators_Monadic_Drop(builtin);
}
