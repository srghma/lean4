// Lean compiler output
// Module: Init.Data.Iterators.Producers.Monadic.List
// Imports: Init.Data.Iterators.Consumers Init.Data.Nat.Lemmas
use crate::r#gen::Init::Data::Iterators::Consumers::{
    initialize_Init_Data_Iterators_Consumers, runtime_initialize_Init_Data_Iterators_Consumers,
};
use crate::r#gen::Init::Data::Nat::Lemmas::{
    initialize_Init_Data_Nat_Lemmas, runtime_initialize_Init_Data_Nat_Lemmas,
};
use crate::r#gen::Init::WFExtrinsicFix::l_WellFounded_opaqueFix_u2083___redArg;
pub unsafe fn l_List_iterM___redArg(
    mut v_l_157_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_l_157_);
    return v_l_157_;
}
pub unsafe fn l_List_iterM___redArg___boxed(
    mut v_l_158_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_159_ = l_List_iterM___redArg(v_l_158_);
    crate::leanh::lean_dec(v_l_158_);
    return v_res_159_;
}
pub unsafe fn l_List_iterM(
    mut v_00_u03b1_160_: *mut crate::leanh::LeanObject,
    mut v_l_161_: *mut crate::leanh::LeanObject,
    mut v_m_162_: *mut crate::leanh::LeanObject,
    mut v_inst_163_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_l_161_);
    return v_l_161_;
}
pub unsafe fn l_List_iterM___boxed(
    mut v_00_u03b1_164_: *mut crate::leanh::LeanObject,
    mut v_l_165_: *mut crate::leanh::LeanObject,
    mut v_m_166_: *mut crate::leanh::LeanObject,
    mut v_inst_167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_168_ = l_List_iterM(v_00_u03b1_164_, v_l_165_, v_m_166_, v_inst_167_);
    crate::leanh::lean_dec(v_inst_167_);
    crate::leanh::lean_dec(v_l_165_);
    return v_res_168_;
}
pub unsafe fn l_Std_Iterators_Types_ListIterator_instIterator___redArg___lam__0(
    mut v_inst_169_: *mut crate::leanh::LeanObject,
    mut v_it_170_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_177_: u8 = 0;
    let mut v___x_179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_182_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_it_170_) == 0 {
                    v___x_171_ = crate::leanh::lean_box(2);
                    v___x_172_ = crate::leanh::lean_apply_2(
                        v_inst_169_,
                        crate::leanh::lean_box(0),
                        v___x_171_,
                    );
                    return v___x_172_;
                } else {
                    v_head_173_ = crate::leanh::lean_ctor_get(v_it_170_, 0);
                    v_tail_174_ = crate::leanh::lean_ctor_get(v_it_170_, 1);
                    v_isSharedCheck_182_ = (!crate::leanh::lean_is_exclusive(v_it_170_)) as u8;
                    if v_isSharedCheck_182_ == 0 {
                        v___x_176_ = v_it_170_;
                        v_isShared_177_ = v_isSharedCheck_182_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_174_);
                        crate::leanh::lean_inc(v_head_173_);
                        crate::leanh::lean_dec(v_it_170_);
                        v___x_176_ = crate::leanh::lean_box(0);
                        v_isShared_177_ = v_isSharedCheck_182_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_177_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_176_, 0);
                    crate::leanh::lean_ctor_set(v___x_176_, 1, v_head_173_);
                    crate::leanh::lean_ctor_set(v___x_176_, 0, v_tail_174_);
                    v___x_179_ = v___x_176_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_181_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_181_, 0, v_tail_174_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_181_, 1, v_head_173_);
                    v___x_179_ = v_reuseFailAlloc_181_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_180_ =
                    crate::leanh::lean_apply_2(v_inst_169_, crate::leanh::lean_box(0), v___x_179_);
                return v___x_180_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Iterators_Types_ListIterator_instIterator___redArg(
    mut v_inst_183_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_184_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_Types_ListIterator_instIterator___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_184_, 0, v_inst_183_);
    return v___f_184_;
}
pub unsafe fn l_Std_Iterators_Types_ListIterator_instIterator(
    mut v_m_185_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_186_: *mut crate::leanh::LeanObject,
    mut v_inst_187_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_188_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_Types_ListIterator_instIterator___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_188_, 0, v_inst_187_);
    return v___f_188_;
}
pub unsafe fn l___private_Init_Data_Iterators_Producers_Monadic_List_0__Std_Iterators_Types_ListIterator_instIterator_match__3_splitter___redArg(
    mut v_it_189_: *mut crate::leanh::LeanObject,
    mut v_h__1_190_: *mut crate::leanh::LeanObject,
    mut v_h__2_191_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_it_189_) == 0 {
        let mut v___x_192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_191_);
        v___x_192_ = crate::leanh::lean_box(0);
        v___x_193_ = crate::leanh::lean_apply_1(v_h__1_190_, v___x_192_);
        return v___x_193_;
    } else {
        let mut v_head_194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_190_);
        v_head_194_ = crate::leanh::lean_ctor_get(v_it_189_, 0);
        crate::leanh::lean_inc(v_head_194_);
        v_tail_195_ = crate::leanh::lean_ctor_get(v_it_189_, 1);
        crate::leanh::lean_inc(v_tail_195_);
        crate::leanh::lean_dec_ref_known(v_it_189_, 2);
        v___x_196_ = crate::leanh::lean_apply_2(v_h__2_191_, v_head_194_, v_tail_195_);
        return v___x_196_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Producers_Monadic_List_0__Std_Iterators_Types_ListIterator_instIterator_match__3_splitter(
    mut v_m_197_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_198_: *mut crate::leanh::LeanObject,
    mut v_motive_199_: *mut crate::leanh::LeanObject,
    mut v_it_200_: *mut crate::leanh::LeanObject,
    mut v_h__1_201_: *mut crate::leanh::LeanObject,
    mut v_h__2_202_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_it_200_) == 0 {
        let mut v___x_203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_202_);
        v___x_203_ = crate::leanh::lean_box(0);
        v___x_204_ = crate::leanh::lean_apply_1(v_h__1_201_, v___x_203_);
        return v___x_204_;
    } else {
        let mut v_head_205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_201_);
        v_head_205_ = crate::leanh::lean_ctor_get(v_it_200_, 0);
        crate::leanh::lean_inc(v_head_205_);
        v_tail_206_ = crate::leanh::lean_ctor_get(v_it_200_, 1);
        crate::leanh::lean_inc(v_tail_206_);
        crate::leanh::lean_dec_ref_known(v_it_200_, 2);
        v___x_207_ = crate::leanh::lean_apply_2(v_h__2_202_, v_head_205_, v_tail_206_);
        return v___x_207_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Producers_Monadic_List_0__Std_Iterators_Types_ListIterator_instIterator_match__1_splitter___redArg(
    mut v_x_208_: *mut crate::leanh::LeanObject,
    mut v_h__1_209_: *mut crate::leanh::LeanObject,
    mut v_h__2_210_: *mut crate::leanh::LeanObject,
    mut v_h__3_211_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_208_) {
        0 => {
            let mut v_it_212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_211_);
            crate::leanh::lean_dec(v_h__2_210_);
            v_it_212_ = crate::leanh::lean_ctor_get(v_x_208_, 0);
            crate::leanh::lean_inc(v_it_212_);
            v_out_213_ = crate::leanh::lean_ctor_get(v_x_208_, 1);
            crate::leanh::lean_inc(v_out_213_);
            crate::leanh::lean_dec_ref_known(v_x_208_, 2);
            v___x_214_ = crate::leanh::lean_apply_2(v_h__1_209_, v_it_212_, v_out_213_);
            return v___x_214_;
        }
        1 => {
            let mut v_it_215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_211_);
            crate::leanh::lean_dec(v_h__1_209_);
            v_it_215_ = crate::leanh::lean_ctor_get(v_x_208_, 0);
            crate::leanh::lean_inc(v_it_215_);
            crate::leanh::lean_dec_ref_known(v_x_208_, 1);
            v___x_216_ = crate::leanh::lean_apply_1(v_h__2_210_, v_it_215_);
            return v___x_216_;
        }
        _ => {
            let mut v___x_217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_210_);
            crate::leanh::lean_dec(v_h__1_209_);
            v___x_217_ = crate::leanh::lean_box(0);
            v___x_218_ = crate::leanh::lean_apply_1(v_h__3_211_, v___x_217_);
            return v___x_218_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Producers_Monadic_List_0__Std_Iterators_Types_ListIterator_instIterator_match__1_splitter(
    mut v_m_219_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_220_: *mut crate::leanh::LeanObject,
    mut v_motive_221_: *mut crate::leanh::LeanObject,
    mut v_x_222_: *mut crate::leanh::LeanObject,
    mut v_h__1_223_: *mut crate::leanh::LeanObject,
    mut v_h__2_224_: *mut crate::leanh::LeanObject,
    mut v_h__3_225_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_222_) {
        0 => {
            let mut v_it_226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_225_);
            crate::leanh::lean_dec(v_h__2_224_);
            v_it_226_ = crate::leanh::lean_ctor_get(v_x_222_, 0);
            crate::leanh::lean_inc(v_it_226_);
            v_out_227_ = crate::leanh::lean_ctor_get(v_x_222_, 1);
            crate::leanh::lean_inc(v_out_227_);
            crate::leanh::lean_dec_ref_known(v_x_222_, 2);
            v___x_228_ = crate::leanh::lean_apply_2(v_h__1_223_, v_it_226_, v_out_227_);
            return v___x_228_;
        }
        1 => {
            let mut v_it_229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_225_);
            crate::leanh::lean_dec(v_h__1_223_);
            v_it_229_ = crate::leanh::lean_ctor_get(v_x_222_, 0);
            crate::leanh::lean_inc(v_it_229_);
            crate::leanh::lean_dec_ref_known(v_x_222_, 1);
            v___x_230_ = crate::leanh::lean_apply_1(v_h__2_224_, v_it_229_);
            return v___x_230_;
        }
        _ => {
            let mut v___x_231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_224_);
            crate::leanh::lean_dec(v_h__1_223_);
            v___x_231_ = crate::leanh::lean_box(0);
            v___x_232_ = crate::leanh::lean_apply_1(v_h__3_225_, v___x_231_);
            return v___x_232_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Producers_Monadic_List_0__Std_Iterators_Types_ListIterator_instFinitenessRelation(
    mut v_00_u03b1_233_: *mut crate::leanh::LeanObject,
    mut v_m_234_: *mut crate::leanh::LeanObject,
    mut v_inst_235_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_236_ = crate::leanh::lean_box(0);
    return v___x_236_;
}
pub unsafe fn l___private_Init_Data_Iterators_Producers_Monadic_List_0__Std_Iterators_Types_ListIterator_instFinitenessRelation___boxed(
    mut v_00_u03b1_237_: *mut crate::leanh::LeanObject,
    mut v_m_238_: *mut crate::leanh::LeanObject,
    mut v_inst_239_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_240_ = l___private_Init_Data_Iterators_Producers_Monadic_List_0__Std_Iterators_Types_ListIterator_instFinitenessRelation(v_00_u03b1_237_, v_m_238_, v_inst_239_);
    crate::leanh::lean_dec(v_inst_239_);
    return v_res_240_;
}
pub unsafe fn l_Std_Iterators_Types_ListIterator_instIteratorLoop___redArg___lam__0(
    mut v_toPure_241_: *mut crate::leanh::LeanObject,
    mut v_recur_242_: *mut crate::leanh::LeanObject,
    mut v_it_243_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_244_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_244_) == 0 {
        let mut v_a_245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_it_243_);
        crate::leanh::lean_dec(v_recur_242_);
        v_a_245_ = crate::leanh::lean_ctor_get(v_____do__lift_244_, 0);
        crate::leanh::lean_inc(v_a_245_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_244_, 1);
        v___x_246_ = crate::leanh::lean_apply_2(v_toPure_241_, crate::leanh::lean_box(0), v_a_245_);
        return v___x_246_;
    } else {
        let mut v_a_247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_241_);
        v_a_247_ = crate::leanh::lean_ctor_get(v_____do__lift_244_, 0);
        crate::leanh::lean_inc(v_a_247_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_244_, 1);
        v___x_248_ = crate::leanh::lean_apply_4(
            v_recur_242_,
            v_it_243_,
            v_a_247_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_248_;
    }
}
pub unsafe fn l_Std_Iterators_Types_ListIterator_instIteratorLoop___redArg___lam__1(
    mut v_toPure_249_: *mut crate::leanh::LeanObject,
    mut v_recur_250_: *mut crate::leanh::LeanObject,
    mut v___y_251_: *mut crate::leanh::LeanObject,
    mut v_acc_252_: *mut crate::leanh::LeanObject,
    mut v_toBind_253_: *mut crate::leanh::LeanObject,
    mut v_s_254_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_s_254_) {
        0 => {
            let mut v_it_255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_it_255_ = crate::leanh::lean_ctor_get(v_s_254_, 0);
            crate::leanh::lean_inc(v_it_255_);
            v_out_256_ = crate::leanh::lean_ctor_get(v_s_254_, 1);
            crate::leanh::lean_inc(v_out_256_);
            crate::leanh::lean_dec_ref_known(v_s_254_, 2);
            v___f_257_ = crate::leanh::lean_alloc_closure(
                l_Std_Iterators_Types_ListIterator_instIteratorLoop___redArg___lam__0
                    as *mut core::ffi::c_void,
                4,
                3,
            );
            crate::leanh::lean_closure_set(v___f_257_, 0, v_toPure_249_);
            crate::leanh::lean_closure_set(v___f_257_, 1, v_recur_250_);
            crate::leanh::lean_closure_set(v___f_257_, 2, v_it_255_);
            v___x_258_ = crate::leanh::lean_apply_3(
                v___y_251_,
                v_out_256_,
                crate::leanh::lean_box(0),
                v_acc_252_,
            );
            v___x_259_ = crate::leanh::lean_apply_4(
                v_toBind_253_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_258_,
                v___f_257_,
            );
            return v___x_259_;
        }
        1 => {
            let mut v_it_260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_toBind_253_);
            crate::leanh::lean_dec(v___y_251_);
            crate::leanh::lean_dec(v_toPure_249_);
            v_it_260_ = crate::leanh::lean_ctor_get(v_s_254_, 0);
            crate::leanh::lean_inc(v_it_260_);
            crate::leanh::lean_dec_ref_known(v_s_254_, 1);
            v___x_261_ = crate::leanh::lean_apply_4(
                v_recur_250_,
                v_it_260_,
                v_acc_252_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_261_;
        }
        _ => {
            let mut v___x_262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_toBind_253_);
            crate::leanh::lean_dec(v___y_251_);
            crate::leanh::lean_dec(v_recur_250_);
            v___x_262_ =
                crate::leanh::lean_apply_2(v_toPure_249_, crate::leanh::lean_box(0), v_acc_252_);
            return v___x_262_;
        }
    }
}
pub unsafe fn l_Std_Iterators_Types_ListIterator_instIteratorLoop___redArg___lam__2(
    mut v_toPure_263_: *mut crate::leanh::LeanObject,
    mut v___y_264_: *mut crate::leanh::LeanObject,
    mut v_toBind_265_: *mut crate::leanh::LeanObject,
    mut v_toPure_266_: *mut crate::leanh::LeanObject,
    mut v_lift_267_: *mut crate::leanh::LeanObject,
    mut v_it_268_: *mut crate::leanh::LeanObject,
    mut v_acc_269_: *mut crate::leanh::LeanObject,
    mut v_hP_270_: *mut crate::leanh::LeanObject,
    mut v_recur_271_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_280_: u8 = 0;
    let mut v___x_282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_286_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_272_ = crate::leanh::lean_alloc_closure(
                    l_Std_Iterators_Types_ListIterator_instIteratorLoop___redArg___lam__1
                        as *mut core::ffi::c_void,
                    6,
                    5,
                );
                crate::leanh::lean_closure_set(v___f_272_, 0, v_toPure_263_);
                crate::leanh::lean_closure_set(v___f_272_, 1, v_recur_271_);
                crate::leanh::lean_closure_set(v___f_272_, 2, v___y_264_);
                crate::leanh::lean_closure_set(v___f_272_, 3, v_acc_269_);
                crate::leanh::lean_closure_set(v___f_272_, 4, v_toBind_265_);
                if crate::leanh::lean_obj_tag(v_it_268_) == 0 {
                    v___x_273_ = crate::leanh::lean_box(2);
                    v___x_274_ = crate::leanh::lean_apply_2(
                        v_toPure_266_,
                        crate::leanh::lean_box(0),
                        v___x_273_,
                    );
                    v___x_275_ = crate::leanh::lean_apply_4(
                        v_lift_267_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___f_272_,
                        v___x_274_,
                    );
                    return v___x_275_;
                } else {
                    v_head_276_ = crate::leanh::lean_ctor_get(v_it_268_, 0);
                    v_tail_277_ = crate::leanh::lean_ctor_get(v_it_268_, 1);
                    v_isSharedCheck_286_ = (!crate::leanh::lean_is_exclusive(v_it_268_)) as u8;
                    if v_isSharedCheck_286_ == 0 {
                        v___x_279_ = v_it_268_;
                        v_isShared_280_ = v_isSharedCheck_286_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_277_);
                        crate::leanh::lean_inc(v_head_276_);
                        crate::leanh::lean_dec(v_it_268_);
                        v___x_279_ = crate::leanh::lean_box(0);
                        v_isShared_280_ = v_isSharedCheck_286_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_280_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_279_, 0);
                    crate::leanh::lean_ctor_set(v___x_279_, 1, v_head_276_);
                    crate::leanh::lean_ctor_set(v___x_279_, 0, v_tail_277_);
                    v___x_282_ = v___x_279_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_285_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_285_, 0, v_tail_277_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_285_, 1, v_head_276_);
                    v___x_282_ = v_reuseFailAlloc_285_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_283_ = crate::leanh::lean_apply_2(
                    v_toPure_266_,
                    crate::leanh::lean_box(0),
                    v___x_282_,
                );
                v___x_284_ = crate::leanh::lean_apply_4(
                    v_lift_267_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___f_272_,
                    v___x_283_,
                );
                return v___x_284_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Iterators_Types_ListIterator_instIteratorLoop___redArg___lam__3(
    mut v_inst_287_: *mut crate::leanh::LeanObject,
    mut v_toPure_288_: *mut crate::leanh::LeanObject,
    mut v_lift_289_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_290_: *mut crate::leanh::LeanObject,
    mut v_Pl_291_: *mut crate::leanh::LeanObject,
    mut v_it_292_: *mut crate::leanh::LeanObject,
    mut v_init_293_: *mut crate::leanh::LeanObject,
    mut v___y_294_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_295_ = crate::leanh::lean_ctor_get(v_inst_287_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_295_);
    v_toBind_296_ = crate::leanh::lean_ctor_get(v_inst_287_, 1);
    crate::leanh::lean_inc(v_toBind_296_);
    crate::leanh::lean_dec_ref(v_inst_287_);
    v_toPure_297_ = crate::leanh::lean_ctor_get(v_toApplicative_295_, 1);
    crate::leanh::lean_inc(v_toPure_297_);
    crate::leanh::lean_dec_ref(v_toApplicative_295_);
    v___f_298_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_Types_ListIterator_instIteratorLoop___redArg___lam__2
            as *mut core::ffi::c_void,
        9,
        5,
    );
    crate::leanh::lean_closure_set(v___f_298_, 0, v_toPure_297_);
    crate::leanh::lean_closure_set(v___f_298_, 1, v___y_294_);
    crate::leanh::lean_closure_set(v___f_298_, 2, v_toBind_296_);
    crate::leanh::lean_closure_set(v___f_298_, 3, v_toPure_288_);
    crate::leanh::lean_closure_set(v___f_298_, 4, v_lift_289_);
    v___x_299_ = l_WellFounded_opaqueFix_u2083___redArg(
        v___f_298_,
        v_it_292_,
        v_init_293_,
        crate::leanh::lean_box(0),
    );
    return v___x_299_;
}
pub unsafe fn l_Std_Iterators_Types_ListIterator_instIteratorLoop___redArg(
    mut v_inst_300_: *mut crate::leanh::LeanObject,
    mut v_inst_301_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_302_ = crate::leanh::lean_ctor_get(v_inst_300_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_302_);
    crate::leanh::lean_dec_ref(v_inst_300_);
    v_toPure_303_ = crate::leanh::lean_ctor_get(v_toApplicative_302_, 1);
    crate::leanh::lean_inc(v_toPure_303_);
    crate::leanh::lean_dec_ref(v_toApplicative_302_);
    v___f_304_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_Types_ListIterator_instIteratorLoop___redArg___lam__3
            as *mut core::ffi::c_void,
        8,
        2,
    );
    crate::leanh::lean_closure_set(v___f_304_, 0, v_inst_301_);
    crate::leanh::lean_closure_set(v___f_304_, 1, v_toPure_303_);
    return v___f_304_;
}
pub unsafe fn l_Std_Iterators_Types_ListIterator_instIteratorLoop(
    mut v_m_305_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_306_: *mut crate::leanh::LeanObject,
    mut v_inst_307_: *mut crate::leanh::LeanObject,
    mut v_n_308_: *mut crate::leanh::LeanObject,
    mut v_inst_309_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_310_ = crate::leanh::lean_ctor_get(v_inst_307_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_310_);
    crate::leanh::lean_dec_ref(v_inst_307_);
    v_toPure_311_ = crate::leanh::lean_ctor_get(v_toApplicative_310_, 1);
    crate::leanh::lean_inc(v_toPure_311_);
    crate::leanh::lean_dec_ref(v_toApplicative_310_);
    v___f_312_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_Types_ListIterator_instIteratorLoop___redArg___lam__3
            as *mut core::ffi::c_void,
        8,
        2,
    );
    crate::leanh::lean_closure_set(v___f_312_, 0, v_inst_309_);
    crate::leanh::lean_closure_set(v___f_312_, 1, v_toPure_311_);
    return v___f_312_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_Producers_Monadic_List(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Consumers(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Iterators_Producers_Monadic_List(
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
pub unsafe fn initialize_Init_Data_Iterators_Producers_Monadic_List(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Consumers(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Producers_Monadic_List(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_Producers_Monadic_List(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Iterators_Producers_Monadic_List(builtin);
}
