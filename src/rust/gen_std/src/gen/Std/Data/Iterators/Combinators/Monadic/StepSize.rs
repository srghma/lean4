// Lean compiler output
// Module: Std.Data.Iterators.Combinators.Monadic.StepSize
// Imports: Init.Data.Iterators.Consumers.Monadic.Access Init.Data.Iterators.Consumers.Monadic.Collect Init.Data.Iterators.Consumers.Monadic.Loop
use crate::ffi::lean_nat_sub;
use crate::r#gen::Init::Data::Iterators::Consumers::Monadic::Access::{
    initialize_Init_Data_Iterators_Consumers_Monadic_Access,
    runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Access,
};
use crate::r#gen::Init::Data::Iterators::Consumers::Monadic::Collect::{
    initialize_Init_Data_Iterators_Consumers_Monadic_Collect,
    runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect,
};
use crate::r#gen::Init::Data::Iterators::Consumers::Monadic::Loop::{
    initialize_Init_Data_Iterators_Consumers_Monadic_Loop,
    runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop,
};
use crate::r#gen::Init::WFExtrinsicFix::l_WellFounded_opaqueFix_u2083___redArg;
pub unsafe fn l_Std_IterM_stepSize___redArg(
    mut v_it_193_: *mut leanh::LeanObject,
    mut v_n_194_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_198_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_195_ = leanh::lean_unsigned_to_nat(0);
    v___x_196_ = leanh::lean_unsigned_to_nat(1);
    v___x_197_ = lean_nat_sub(v_n_194_, v___x_196_);
    v___x_198_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_198_, 0, v___x_195_);
    leanh::lean_ctor_set(v___x_198_, 1, v___x_197_);
    leanh::lean_ctor_set(v___x_198_, 2, v_it_193_);
    return v___x_198_;
}
pub unsafe fn l_Std_IterM_stepSize___redArg___boxed(
    mut v_it_199_: *mut leanh::LeanObject,
    mut v_n_200_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_201_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_201_ = l_Std_IterM_stepSize___redArg(v_it_199_, v_n_200_);
    leanh::lean_dec(v_n_200_);
    return v_res_201_;
}
pub unsafe fn l_Std_IterM_stepSize(
    mut v_00_u03b1_202_: *mut leanh::LeanObject,
    mut v_m_203_: *mut leanh::LeanObject,
    mut v_00_u03b2_204_: *mut leanh::LeanObject,
    mut v_inst_205_: *mut leanh::LeanObject,
    mut v_inst_206_: *mut leanh::LeanObject,
    mut v_inst_207_: *mut leanh::LeanObject,
    mut v_it_208_: *mut leanh::LeanObject,
    mut v_n_209_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_213_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_210_ = leanh::lean_unsigned_to_nat(0);
    v___x_211_ = leanh::lean_unsigned_to_nat(1);
    v___x_212_ = lean_nat_sub(v_n_209_, v___x_211_);
    v___x_213_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_213_, 0, v___x_210_);
    leanh::lean_ctor_set(v___x_213_, 1, v___x_212_);
    leanh::lean_ctor_set(v___x_213_, 2, v_it_208_);
    return v___x_213_;
}
pub unsafe fn l_Std_IterM_stepSize___boxed(
    mut v_00_u03b1_214_: *mut leanh::LeanObject,
    mut v_m_215_: *mut leanh::LeanObject,
    mut v_00_u03b2_216_: *mut leanh::LeanObject,
    mut v_inst_217_: *mut leanh::LeanObject,
    mut v_inst_218_: *mut leanh::LeanObject,
    mut v_inst_219_: *mut leanh::LeanObject,
    mut v_it_220_: *mut leanh::LeanObject,
    mut v_n_221_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_222_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_222_ = l_Std_IterM_stepSize(
        v_00_u03b1_214_,
        v_m_215_,
        v_00_u03b2_216_,
        v_inst_217_,
        v_inst_218_,
        v_inst_219_,
        v_it_220_,
        v_n_221_,
    );
    leanh::lean_dec(v_n_221_);
    leanh::lean_dec_ref(v_inst_219_);
    leanh::lean_dec(v_inst_218_);
    leanh::lean_dec(v_inst_217_);
    return v_res_222_;
}
pub unsafe fn l_Std_Iterators_Types_StepSizeIterator_instIterator___redArg___lam__0(
    mut v_n_223_: *mut leanh::LeanObject,
    mut v_s_224_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_it_225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_229_: u8 = 0;
    let mut v___x_230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_234_: u8 = 0;
    let mut v_it_235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_238_: u8 = 0;
    let mut v___x_239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_243_: u8 = 0;
    let mut v___x_244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_s_224_) {
                0 => {
                    v_it_225_ = leanh::lean_ctor_get(v_s_224_, 0);
                    v_out_226_ = leanh::lean_ctor_get(v_s_224_, 1);
                    v_isSharedCheck_234_ = (!leanh::lean_is_exclusive(v_s_224_)) as u8;
                    if v_isSharedCheck_234_ == 0 {
                        v___x_228_ = v_s_224_;
                        v_isShared_229_ = v_isSharedCheck_234_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_out_226_);
                        leanh::lean_inc(v_it_225_);
                        leanh::lean_dec(v_s_224_);
                        v___x_228_ = leanh::lean_box(0);
                        v_isShared_229_ = v_isSharedCheck_234_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_it_235_ = leanh::lean_ctor_get(v_s_224_, 0);
                    v_isSharedCheck_243_ = (!leanh::lean_is_exclusive(v_s_224_)) as u8;
                    if v_isSharedCheck_243_ == 0 {
                        v___x_237_ = v_s_224_;
                        v_isShared_238_ = v_isSharedCheck_243_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_it_235_);
                        leanh::lean_dec(v_s_224_);
                        v___x_237_ = leanh::lean_box(0);
                        v_isShared_238_ = v_isSharedCheck_243_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    leanh::lean_dec(v_n_223_);
                    v___x_244_ = leanh::lean_box(2);
                    return v___x_244_;
                }
            },
            1 => {
                leanh::lean_inc(v_n_223_);
                v___x_230_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_230_, 0, v_n_223_);
                leanh::lean_ctor_set(v___x_230_, 1, v_n_223_);
                leanh::lean_ctor_set(v___x_230_, 2, v_it_225_);
                if v_isShared_229_ == 0 {
                    leanh::lean_ctor_set(v___x_228_, 0, v___x_230_);
                    v___x_232_ = v___x_228_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_233_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_233_, 0, v___x_230_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_233_, 1, v_out_226_);
                    v___x_232_ = v_reuseFailAlloc_233_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_232_;
            }
            3 => {
                leanh::lean_inc(v_n_223_);
                v___x_239_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_239_, 0, v_n_223_);
                leanh::lean_ctor_set(v___x_239_, 1, v_n_223_);
                leanh::lean_ctor_set(v___x_239_, 2, v_it_235_);
                if v_isShared_238_ == 0 {
                    leanh::lean_ctor_set(v___x_237_, 0, v___x_239_);
                    v___x_241_ = v___x_237_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_242_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_242_, 0, v___x_239_);
                    v___x_241_ = v_reuseFailAlloc_242_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_241_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Iterators_Types_StepSizeIterator_instIterator___redArg___lam__1(
    mut v_toFunctor_245_: *mut leanh::LeanObject,
    mut v_inst_246_: *mut leanh::LeanObject,
    mut v_it_247_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_map_248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIdx_249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inner_251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_254_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_map_248_ = leanh::lean_ctor_get(v_toFunctor_245_, 0);
    leanh::lean_inc(v_map_248_);
    leanh::lean_dec_ref(v_toFunctor_245_);
    v_nextIdx_249_ = leanh::lean_ctor_get(v_it_247_, 0);
    leanh::lean_inc(v_nextIdx_249_);
    v_n_250_ = leanh::lean_ctor_get(v_it_247_, 1);
    leanh::lean_inc(v_n_250_);
    v_inner_251_ = leanh::lean_ctor_get(v_it_247_, 2);
    leanh::lean_inc(v_inner_251_);
    leanh::lean_dec_ref(v_it_247_);
    v___f_252_ = leanh::lean_alloc_closure(
        l_Std_Iterators_Types_StepSizeIterator_instIterator___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_252_, 0, v_n_250_);
    v___x_253_ = leanh::lean_apply_2(v_inst_246_, v_inner_251_, v_nextIdx_249_);
    v___x_254_ = leanh::lean_apply_4(
        v_map_248_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_252_,
        v___x_253_,
    );
    return v___x_254_;
}
pub unsafe fn l_Std_Iterators_Types_StepSizeIterator_instIterator___redArg(
    mut v_inst_255_: *mut leanh::LeanObject,
    mut v_inst_256_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_259_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_257_ = leanh::lean_ctor_get(v_inst_256_, 0);
    leanh::lean_inc_ref(v_toApplicative_257_);
    leanh::lean_dec_ref(v_inst_256_);
    v_toFunctor_258_ = leanh::lean_ctor_get(v_toApplicative_257_, 0);
    leanh::lean_inc_ref(v_toFunctor_258_);
    leanh::lean_dec_ref(v_toApplicative_257_);
    v___f_259_ = leanh::lean_alloc_closure(
        l_Std_Iterators_Types_StepSizeIterator_instIterator___redArg___lam__1
            as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_259_, 0, v_toFunctor_258_);
    leanh::lean_closure_set(v___f_259_, 1, v_inst_255_);
    return v___f_259_;
}
pub unsafe fn l_Std_Iterators_Types_StepSizeIterator_instIterator(
    mut v_00_u03b1_260_: *mut leanh::LeanObject,
    mut v_m_261_: *mut leanh::LeanObject,
    mut v_00_u03b2_262_: *mut leanh::LeanObject,
    mut v_inst_263_: *mut leanh::LeanObject,
    mut v_inst_264_: *mut leanh::LeanObject,
    mut v_inst_265_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_266_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_266_ =
        l_Std_Iterators_Types_StepSizeIterator_instIterator___redArg(v_inst_264_, v_inst_265_);
    return v___x_266_;
}
pub unsafe fn l_Std_Iterators_Types_StepSizeIterator_instIterator___boxed(
    mut v_00_u03b1_267_: *mut leanh::LeanObject,
    mut v_m_268_: *mut leanh::LeanObject,
    mut v_00_u03b2_269_: *mut leanh::LeanObject,
    mut v_inst_270_: *mut leanh::LeanObject,
    mut v_inst_271_: *mut leanh::LeanObject,
    mut v_inst_272_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_273_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_273_ = l_Std_Iterators_Types_StepSizeIterator_instIterator(
        v_00_u03b1_267_,
        v_m_268_,
        v_00_u03b2_269_,
        v_inst_270_,
        v_inst_271_,
        v_inst_272_,
    );
    leanh::lean_dec(v_inst_270_);
    return v_res_273_;
}
pub unsafe fn l_Std_Iterators_Types_StepSizeIterator_instFinitenessRelation(
    mut v_00_u03b1_274_: *mut leanh::LeanObject,
    mut v_m_275_: *mut leanh::LeanObject,
    mut v_00_u03b2_276_: *mut leanh::LeanObject,
    mut v_inst_277_: *mut leanh::LeanObject,
    mut v_inst_278_: *mut leanh::LeanObject,
    mut v_inst_279_: *mut leanh::LeanObject,
    mut v_inst_280_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_281_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_281_ = leanh::lean_box(0);
    return v___x_281_;
}
pub unsafe fn l_Std_Iterators_Types_StepSizeIterator_instFinitenessRelation___boxed(
    mut v_00_u03b1_282_: *mut leanh::LeanObject,
    mut v_m_283_: *mut leanh::LeanObject,
    mut v_00_u03b2_284_: *mut leanh::LeanObject,
    mut v_inst_285_: *mut leanh::LeanObject,
    mut v_inst_286_: *mut leanh::LeanObject,
    mut v_inst_287_: *mut leanh::LeanObject,
    mut v_inst_288_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_289_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_289_ = l_Std_Iterators_Types_StepSizeIterator_instFinitenessRelation(
        v_00_u03b1_282_,
        v_m_283_,
        v_00_u03b2_284_,
        v_inst_285_,
        v_inst_286_,
        v_inst_287_,
        v_inst_288_,
    );
    leanh::lean_dec_ref(v_inst_287_);
    leanh::lean_dec(v_inst_286_);
    leanh::lean_dec(v_inst_285_);
    return v_res_289_;
}
pub unsafe fn l_Std_Iterators_Types_StepSizeIterator_instProductivenessRelation(
    mut v_00_u03b1_290_: *mut leanh::LeanObject,
    mut v_m_291_: *mut leanh::LeanObject,
    mut v_00_u03b2_292_: *mut leanh::LeanObject,
    mut v_inst_293_: *mut leanh::LeanObject,
    mut v_inst_294_: *mut leanh::LeanObject,
    mut v_inst_295_: *mut leanh::LeanObject,
    mut v_inst_296_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_297_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_297_ = leanh::lean_box(0);
    return v___x_297_;
}
pub unsafe fn l_Std_Iterators_Types_StepSizeIterator_instProductivenessRelation___boxed(
    mut v_00_u03b1_298_: *mut leanh::LeanObject,
    mut v_m_299_: *mut leanh::LeanObject,
    mut v_00_u03b2_300_: *mut leanh::LeanObject,
    mut v_inst_301_: *mut leanh::LeanObject,
    mut v_inst_302_: *mut leanh::LeanObject,
    mut v_inst_303_: *mut leanh::LeanObject,
    mut v_inst_304_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_305_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_305_ = l_Std_Iterators_Types_StepSizeIterator_instProductivenessRelation(
        v_00_u03b1_298_,
        v_m_299_,
        v_00_u03b2_300_,
        v_inst_301_,
        v_inst_302_,
        v_inst_303_,
        v_inst_304_,
    );
    leanh::lean_dec_ref(v_inst_303_);
    leanh::lean_dec(v_inst_302_);
    leanh::lean_dec(v_inst_301_);
    return v_res_305_;
}
pub unsafe fn l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop___redArg___lam__0(
    mut v_toPure_306_: *mut leanh::LeanObject,
    mut v_recur_307_: *mut leanh::LeanObject,
    mut v_it_308_: *mut leanh::LeanObject,
    mut v_____do__lift_309_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_309_) == 0 {
        let mut v_a_310_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_311_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_it_308_);
        leanh::lean_dec(v_recur_307_);
        v_a_310_ = leanh::lean_ctor_get(v_____do__lift_309_, 0);
        leanh::lean_inc(v_a_310_);
        leanh::lean_dec_ref_known(v_____do__lift_309_, 1);
        v___x_311_ = leanh::lean_apply_2(v_toPure_306_, leanh::lean_box(0), v_a_310_);
        return v___x_311_;
    } else {
        let mut v_a_312_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_313_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_toPure_306_);
        v_a_312_ = leanh::lean_ctor_get(v_____do__lift_309_, 0);
        leanh::lean_inc(v_a_312_);
        leanh::lean_dec_ref_known(v_____do__lift_309_, 1);
        v___x_313_ = leanh::lean_apply_4(
            v_recur_307_,
            v_it_308_,
            v_a_312_,
            leanh::lean_box(0),
            leanh::lean_box(0),
        );
        return v___x_313_;
    }
}
pub unsafe fn l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop___redArg___lam__1(
    mut v_toPure_314_: *mut leanh::LeanObject,
    mut v_recur_315_: *mut leanh::LeanObject,
    mut v___y_316_: *mut leanh::LeanObject,
    mut v_acc_317_: *mut leanh::LeanObject,
    mut v_toBind_318_: *mut leanh::LeanObject,
    mut v_s_319_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_s_319_) {
        0 => {
            let mut v_it_320_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_321_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_322_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_323_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_324_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_it_320_ = leanh::lean_ctor_get(v_s_319_, 0);
            leanh::lean_inc(v_it_320_);
            v_out_321_ = leanh::lean_ctor_get(v_s_319_, 1);
            leanh::lean_inc(v_out_321_);
            leanh::lean_dec_ref_known(v_s_319_, 2);
            v___f_322_ = leanh::lean_alloc_closure(
                l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop___redArg___lam__0
                    as *mut core::ffi::c_void,
                4,
                3,
            );
            leanh::lean_closure_set(v___f_322_, 0, v_toPure_314_);
            leanh::lean_closure_set(v___f_322_, 1, v_recur_315_);
            leanh::lean_closure_set(v___f_322_, 2, v_it_320_);
            v___x_323_ = leanh::lean_apply_3(
                v___y_316_,
                v_out_321_,
                leanh::lean_box(0),
                v_acc_317_,
            );
            v___x_324_ = leanh::lean_apply_4(
                v_toBind_318_,
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_323_,
                v___f_322_,
            );
            return v___x_324_;
        }
        1 => {
            let mut v_it_325_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_326_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_toBind_318_);
            leanh::lean_dec(v___y_316_);
            leanh::lean_dec(v_toPure_314_);
            v_it_325_ = leanh::lean_ctor_get(v_s_319_, 0);
            leanh::lean_inc(v_it_325_);
            leanh::lean_dec_ref_known(v_s_319_, 1);
            v___x_326_ = leanh::lean_apply_4(
                v_recur_315_,
                v_it_325_,
                v_acc_317_,
                leanh::lean_box(0),
                leanh::lean_box(0),
            );
            return v___x_326_;
        }
        _ => {
            let mut v___x_327_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_toBind_318_);
            leanh::lean_dec(v___y_316_);
            leanh::lean_dec(v_recur_315_);
            v___x_327_ =
                leanh::lean_apply_2(v_toPure_314_, leanh::lean_box(0), v_acc_317_);
            return v___x_327_;
        }
    }
}
pub unsafe fn l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop___redArg___lam__3(
    mut v_inst_328_: *mut leanh::LeanObject,
    mut v_toPure_329_: *mut leanh::LeanObject,
    mut v___y_330_: *mut leanh::LeanObject,
    mut v_toBind_331_: *mut leanh::LeanObject,
    mut v_inst_332_: *mut leanh::LeanObject,
    mut v_lift_333_: *mut leanh::LeanObject,
    mut v_it_334_: *mut leanh::LeanObject,
    mut v_acc_335_: *mut leanh::LeanObject,
    mut v_hP_336_: *mut leanh::LeanObject,
    mut v_recur_337_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIdx_341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inner_343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_348_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_338_ = leanh::lean_ctor_get(v_inst_328_, 0);
    leanh::lean_inc_ref(v_toApplicative_338_);
    leanh::lean_dec_ref(v_inst_328_);
    v_toFunctor_339_ = leanh::lean_ctor_get(v_toApplicative_338_, 0);
    leanh::lean_inc_ref(v_toFunctor_339_);
    leanh::lean_dec_ref(v_toApplicative_338_);
    v_map_340_ = leanh::lean_ctor_get(v_toFunctor_339_, 0);
    leanh::lean_inc(v_map_340_);
    leanh::lean_dec_ref(v_toFunctor_339_);
    v_nextIdx_341_ = leanh::lean_ctor_get(v_it_334_, 0);
    leanh::lean_inc(v_nextIdx_341_);
    v_n_342_ = leanh::lean_ctor_get(v_it_334_, 1);
    leanh::lean_inc(v_n_342_);
    v_inner_343_ = leanh::lean_ctor_get(v_it_334_, 2);
    leanh::lean_inc(v_inner_343_);
    leanh::lean_dec_ref(v_it_334_);
    v___f_344_ = leanh::lean_alloc_closure(
        l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop___redArg___lam__1
            as *mut core::ffi::c_void,
        6,
        5,
    );
    leanh::lean_closure_set(v___f_344_, 0, v_toPure_329_);
    leanh::lean_closure_set(v___f_344_, 1, v_recur_337_);
    leanh::lean_closure_set(v___f_344_, 2, v___y_330_);
    leanh::lean_closure_set(v___f_344_, 3, v_acc_335_);
    leanh::lean_closure_set(v___f_344_, 4, v_toBind_331_);
    v___f_345_ = leanh::lean_alloc_closure(
        l_Std_Iterators_Types_StepSizeIterator_instIterator___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_345_, 0, v_n_342_);
    v___x_346_ = leanh::lean_apply_2(v_inst_332_, v_inner_343_, v_nextIdx_341_);
    v___x_347_ = leanh::lean_apply_4(
        v_map_340_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_345_,
        v___x_346_,
    );
    v___x_348_ = leanh::lean_apply_4(
        v_lift_333_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_344_,
        v___x_347_,
    );
    return v___x_348_;
}
pub unsafe fn l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop___redArg___lam__2(
    mut v_inst_349_: *mut leanh::LeanObject,
    mut v_inst_350_: *mut leanh::LeanObject,
    mut v_inst_351_: *mut leanh::LeanObject,
    mut v_lift_352_: *mut leanh::LeanObject,
    mut v_00_u03b3_353_: *mut leanh::LeanObject,
    mut v_Pl_354_: *mut leanh::LeanObject,
    mut v_it_355_: *mut leanh::LeanObject,
    mut v_init_356_: *mut leanh::LeanObject,
    mut v___y_357_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_362_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_358_ = leanh::lean_ctor_get(v_inst_349_, 0);
    leanh::lean_inc_ref(v_toApplicative_358_);
    v_toBind_359_ = leanh::lean_ctor_get(v_inst_349_, 1);
    leanh::lean_inc(v_toBind_359_);
    leanh::lean_dec_ref(v_inst_349_);
    v_toPure_360_ = leanh::lean_ctor_get(v_toApplicative_358_, 1);
    leanh::lean_inc(v_toPure_360_);
    leanh::lean_dec_ref(v_toApplicative_358_);
    v___f_361_ = leanh::lean_alloc_closure(
        l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop___redArg___lam__3
            as *mut core::ffi::c_void,
        10,
        6,
    );
    leanh::lean_closure_set(v___f_361_, 0, v_inst_350_);
    leanh::lean_closure_set(v___f_361_, 1, v_toPure_360_);
    leanh::lean_closure_set(v___f_361_, 2, v___y_357_);
    leanh::lean_closure_set(v___f_361_, 3, v_toBind_359_);
    leanh::lean_closure_set(v___f_361_, 4, v_inst_351_);
    leanh::lean_closure_set(v___f_361_, 5, v_lift_352_);
    v___x_362_ = l_WellFounded_opaqueFix_u2083___redArg(
        v___f_361_,
        v_it_355_,
        v_init_356_,
        leanh::lean_box(0),
    );
    return v___x_362_;
}
pub unsafe fn l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop___redArg(
    mut v_inst_363_: *mut leanh::LeanObject,
    mut v_inst_364_: *mut leanh::LeanObject,
    mut v_inst_365_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_366_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_366_ = leanh::lean_alloc_closure(
        l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop___redArg___lam__2
            as *mut core::ffi::c_void,
        9,
        3,
    );
    leanh::lean_closure_set(v___f_366_, 0, v_inst_365_);
    leanh::lean_closure_set(v___f_366_, 1, v_inst_364_);
    leanh::lean_closure_set(v___f_366_, 2, v_inst_363_);
    return v___f_366_;
}
pub unsafe fn l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop(
    mut v_00_u03b1_367_: *mut leanh::LeanObject,
    mut v_00_u03b2_368_: *mut leanh::LeanObject,
    mut v_m_369_: *mut leanh::LeanObject,
    mut v_n_370_: *mut leanh::LeanObject,
    mut v_inst_371_: *mut leanh::LeanObject,
    mut v_inst_372_: *mut leanh::LeanObject,
    mut v_inst_373_: *mut leanh::LeanObject,
    mut v_inst_374_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_375_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_375_ = leanh::lean_alloc_closure(
        l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop___redArg___lam__2
            as *mut core::ffi::c_void,
        9,
        3,
    );
    leanh::lean_closure_set(v___f_375_, 0, v_inst_374_);
    leanh::lean_closure_set(v___f_375_, 1, v_inst_373_);
    leanh::lean_closure_set(v___f_375_, 2, v_inst_372_);
    return v___f_375_;
}
pub unsafe fn l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop___boxed(
    mut v_00_u03b1_376_: *mut leanh::LeanObject,
    mut v_00_u03b2_377_: *mut leanh::LeanObject,
    mut v_m_378_: *mut leanh::LeanObject,
    mut v_n_379_: *mut leanh::LeanObject,
    mut v_inst_380_: *mut leanh::LeanObject,
    mut v_inst_381_: *mut leanh::LeanObject,
    mut v_inst_382_: *mut leanh::LeanObject,
    mut v_inst_383_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_384_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_384_ = l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop(
        v_00_u03b1_376_,
        v_00_u03b2_377_,
        v_m_378_,
        v_n_379_,
        v_inst_380_,
        v_inst_381_,
        v_inst_382_,
        v_inst_383_,
    );
    leanh::lean_dec(v_inst_380_);
    return v_res_384_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_Iterators_Combinators_Monadic_StepSize(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Access(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_Iterators_Combinators_Monadic_StepSize(
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
pub unsafe fn initialize_Std_Data_Iterators_Combinators_Monadic_StepSize(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Consumers_Monadic_Access(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Combinators_Monadic_StepSize(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_Iterators_Combinators_Monadic_StepSize(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Data_Iterators_Combinators_Monadic_StepSize(builtin);
}