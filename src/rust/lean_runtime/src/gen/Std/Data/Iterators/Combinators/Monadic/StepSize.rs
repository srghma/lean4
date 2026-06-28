// Lean compiler output
// Module: Std.Data.Iterators.Combinators.Monadic.StepSize
// Imports: Init.Data.Iterators.Consumers.Monadic.Access Init.Data.Iterators.Consumers.Monadic.Collect Init.Data.Iterators.Consumers.Monadic.Loop
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
use crate::lean_imports_rs::Init::Prelude::lean_nat_sub;
pub unsafe fn l_Std_IterM_stepSize___redArg(
    mut v_it_193_: *mut crate::leanh::LeanObject,
    mut v_n_194_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_195_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_196_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_197_ = lean_nat_sub(v_n_194_, v___x_196_);
    v___x_198_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_198_, 0, v___x_195_);
    crate::leanh::lean_ctor_set(v___x_198_, 1, v___x_197_);
    crate::leanh::lean_ctor_set(v___x_198_, 2, v_it_193_);
    return v___x_198_;
}
pub unsafe fn l_Std_IterM_stepSize___redArg___boxed(
    mut v_it_199_: *mut crate::leanh::LeanObject,
    mut v_n_200_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_201_ = l_Std_IterM_stepSize___redArg(v_it_199_, v_n_200_);
    crate::leanh::lean_dec(v_n_200_);
    return v_res_201_;
}
pub unsafe fn l_Std_IterM_stepSize(
    mut v_00_u03b1_202_: *mut crate::leanh::LeanObject,
    mut v_m_203_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_204_: *mut crate::leanh::LeanObject,
    mut v_inst_205_: *mut crate::leanh::LeanObject,
    mut v_inst_206_: *mut crate::leanh::LeanObject,
    mut v_inst_207_: *mut crate::leanh::LeanObject,
    mut v_it_208_: *mut crate::leanh::LeanObject,
    mut v_n_209_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_210_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_211_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_212_ = lean_nat_sub(v_n_209_, v___x_211_);
    v___x_213_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_213_, 0, v___x_210_);
    crate::leanh::lean_ctor_set(v___x_213_, 1, v___x_212_);
    crate::leanh::lean_ctor_set(v___x_213_, 2, v_it_208_);
    return v___x_213_;
}
pub unsafe fn l_Std_IterM_stepSize___boxed(
    mut v_00_u03b1_214_: *mut crate::leanh::LeanObject,
    mut v_m_215_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_216_: *mut crate::leanh::LeanObject,
    mut v_inst_217_: *mut crate::leanh::LeanObject,
    mut v_inst_218_: *mut crate::leanh::LeanObject,
    mut v_inst_219_: *mut crate::leanh::LeanObject,
    mut v_it_220_: *mut crate::leanh::LeanObject,
    mut v_n_221_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_n_221_);
    crate::leanh::lean_dec_ref(v_inst_219_);
    crate::leanh::lean_dec(v_inst_218_);
    crate::leanh::lean_dec(v_inst_217_);
    return v_res_222_;
}
pub unsafe fn l_Std_Iterators_Types_StepSizeIterator_instIterator___redArg___lam__0(
    mut v_n_223_: *mut crate::leanh::LeanObject,
    mut v_s_224_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_it_225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_229_: u8 = 0;
    let mut v___x_230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_234_: u8 = 0;
    let mut v_it_235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_238_: u8 = 0;
    let mut v___x_239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_243_: u8 = 0;
    let mut v___x_244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_s_224_) {
                0 => {
                    v_it_225_ = crate::leanh::lean_ctor_get(v_s_224_, 0);
                    v_out_226_ = crate::leanh::lean_ctor_get(v_s_224_, 1);
                    v_isSharedCheck_234_ = (!crate::leanh::lean_is_exclusive(v_s_224_)) as u8;
                    if v_isSharedCheck_234_ == 0 {
                        v___x_228_ = v_s_224_;
                        v_isShared_229_ = v_isSharedCheck_234_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_out_226_);
                        crate::leanh::lean_inc(v_it_225_);
                        crate::leanh::lean_dec(v_s_224_);
                        v___x_228_ = crate::leanh::lean_box(0);
                        v_isShared_229_ = v_isSharedCheck_234_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_it_235_ = crate::leanh::lean_ctor_get(v_s_224_, 0);
                    v_isSharedCheck_243_ = (!crate::leanh::lean_is_exclusive(v_s_224_)) as u8;
                    if v_isSharedCheck_243_ == 0 {
                        v___x_237_ = v_s_224_;
                        v_isShared_238_ = v_isSharedCheck_243_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_it_235_);
                        crate::leanh::lean_dec(v_s_224_);
                        v___x_237_ = crate::leanh::lean_box(0);
                        v_isShared_238_ = v_isSharedCheck_243_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    crate::leanh::lean_dec(v_n_223_);
                    v___x_244_ = crate::leanh::lean_box(2);
                    return v___x_244_;
                }
            },
            1 => {
                crate::leanh::lean_inc(v_n_223_);
                v___x_230_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_230_, 0, v_n_223_);
                crate::leanh::lean_ctor_set(v___x_230_, 1, v_n_223_);
                crate::leanh::lean_ctor_set(v___x_230_, 2, v_it_225_);
                if v_isShared_229_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_228_, 0, v___x_230_);
                    v___x_232_ = v___x_228_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_233_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_233_, 0, v___x_230_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_233_, 1, v_out_226_);
                    v___x_232_ = v_reuseFailAlloc_233_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_232_;
            }
            3 => {
                crate::leanh::lean_inc(v_n_223_);
                v___x_239_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_239_, 0, v_n_223_);
                crate::leanh::lean_ctor_set(v___x_239_, 1, v_n_223_);
                crate::leanh::lean_ctor_set(v___x_239_, 2, v_it_235_);
                if v_isShared_238_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_237_, 0, v___x_239_);
                    v___x_241_ = v___x_237_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_242_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_242_, 0, v___x_239_);
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
    mut v_toFunctor_245_: *mut crate::leanh::LeanObject,
    mut v_inst_246_: *mut crate::leanh::LeanObject,
    mut v_it_247_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIdx_249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inner_251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_248_ = crate::leanh::lean_ctor_get(v_toFunctor_245_, 0);
    crate::leanh::lean_inc(v_map_248_);
    crate::leanh::lean_dec_ref(v_toFunctor_245_);
    v_nextIdx_249_ = crate::leanh::lean_ctor_get(v_it_247_, 0);
    crate::leanh::lean_inc(v_nextIdx_249_);
    v_n_250_ = crate::leanh::lean_ctor_get(v_it_247_, 1);
    crate::leanh::lean_inc(v_n_250_);
    v_inner_251_ = crate::leanh::lean_ctor_get(v_it_247_, 2);
    crate::leanh::lean_inc(v_inner_251_);
    crate::leanh::lean_dec_ref(v_it_247_);
    v___f_252_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_Types_StepSizeIterator_instIterator___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_252_, 0, v_n_250_);
    v___x_253_ = crate::leanh::lean_apply_2(v_inst_246_, v_inner_251_, v_nextIdx_249_);
    v___x_254_ = crate::leanh::lean_apply_4(
        v_map_248_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_252_,
        v___x_253_,
    );
    return v___x_254_;
}
pub unsafe fn l_Std_Iterators_Types_StepSizeIterator_instIterator___redArg(
    mut v_inst_255_: *mut crate::leanh::LeanObject,
    mut v_inst_256_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_257_ = crate::leanh::lean_ctor_get(v_inst_256_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_257_);
    crate::leanh::lean_dec_ref(v_inst_256_);
    v_toFunctor_258_ = crate::leanh::lean_ctor_get(v_toApplicative_257_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_258_);
    crate::leanh::lean_dec_ref(v_toApplicative_257_);
    v___f_259_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_Types_StepSizeIterator_instIterator___redArg___lam__1
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_259_, 0, v_toFunctor_258_);
    crate::leanh::lean_closure_set(v___f_259_, 1, v_inst_255_);
    return v___f_259_;
}
pub unsafe fn l_Std_Iterators_Types_StepSizeIterator_instIterator(
    mut v_00_u03b1_260_: *mut crate::leanh::LeanObject,
    mut v_m_261_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_262_: *mut crate::leanh::LeanObject,
    mut v_inst_263_: *mut crate::leanh::LeanObject,
    mut v_inst_264_: *mut crate::leanh::LeanObject,
    mut v_inst_265_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_266_ =
        l_Std_Iterators_Types_StepSizeIterator_instIterator___redArg(v_inst_264_, v_inst_265_);
    return v___x_266_;
}
pub unsafe fn l_Std_Iterators_Types_StepSizeIterator_instIterator___boxed(
    mut v_00_u03b1_267_: *mut crate::leanh::LeanObject,
    mut v_m_268_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_269_: *mut crate::leanh::LeanObject,
    mut v_inst_270_: *mut crate::leanh::LeanObject,
    mut v_inst_271_: *mut crate::leanh::LeanObject,
    mut v_inst_272_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_273_ = l_Std_Iterators_Types_StepSizeIterator_instIterator(
        v_00_u03b1_267_,
        v_m_268_,
        v_00_u03b2_269_,
        v_inst_270_,
        v_inst_271_,
        v_inst_272_,
    );
    crate::leanh::lean_dec(v_inst_270_);
    return v_res_273_;
}
pub unsafe fn l_Std_Iterators_Types_StepSizeIterator_instFinitenessRelation(
    mut v_00_u03b1_274_: *mut crate::leanh::LeanObject,
    mut v_m_275_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_276_: *mut crate::leanh::LeanObject,
    mut v_inst_277_: *mut crate::leanh::LeanObject,
    mut v_inst_278_: *mut crate::leanh::LeanObject,
    mut v_inst_279_: *mut crate::leanh::LeanObject,
    mut v_inst_280_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_281_ = crate::leanh::lean_box(0);
    return v___x_281_;
}
pub unsafe fn l_Std_Iterators_Types_StepSizeIterator_instFinitenessRelation___boxed(
    mut v_00_u03b1_282_: *mut crate::leanh::LeanObject,
    mut v_m_283_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_284_: *mut crate::leanh::LeanObject,
    mut v_inst_285_: *mut crate::leanh::LeanObject,
    mut v_inst_286_: *mut crate::leanh::LeanObject,
    mut v_inst_287_: *mut crate::leanh::LeanObject,
    mut v_inst_288_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_289_ = l_Std_Iterators_Types_StepSizeIterator_instFinitenessRelation(
        v_00_u03b1_282_,
        v_m_283_,
        v_00_u03b2_284_,
        v_inst_285_,
        v_inst_286_,
        v_inst_287_,
        v_inst_288_,
    );
    crate::leanh::lean_dec_ref(v_inst_287_);
    crate::leanh::lean_dec(v_inst_286_);
    crate::leanh::lean_dec(v_inst_285_);
    return v_res_289_;
}
pub unsafe fn l_Std_Iterators_Types_StepSizeIterator_instProductivenessRelation(
    mut v_00_u03b1_290_: *mut crate::leanh::LeanObject,
    mut v_m_291_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_292_: *mut crate::leanh::LeanObject,
    mut v_inst_293_: *mut crate::leanh::LeanObject,
    mut v_inst_294_: *mut crate::leanh::LeanObject,
    mut v_inst_295_: *mut crate::leanh::LeanObject,
    mut v_inst_296_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_297_ = crate::leanh::lean_box(0);
    return v___x_297_;
}
pub unsafe fn l_Std_Iterators_Types_StepSizeIterator_instProductivenessRelation___boxed(
    mut v_00_u03b1_298_: *mut crate::leanh::LeanObject,
    mut v_m_299_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_300_: *mut crate::leanh::LeanObject,
    mut v_inst_301_: *mut crate::leanh::LeanObject,
    mut v_inst_302_: *mut crate::leanh::LeanObject,
    mut v_inst_303_: *mut crate::leanh::LeanObject,
    mut v_inst_304_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_305_ = l_Std_Iterators_Types_StepSizeIterator_instProductivenessRelation(
        v_00_u03b1_298_,
        v_m_299_,
        v_00_u03b2_300_,
        v_inst_301_,
        v_inst_302_,
        v_inst_303_,
        v_inst_304_,
    );
    crate::leanh::lean_dec_ref(v_inst_303_);
    crate::leanh::lean_dec(v_inst_302_);
    crate::leanh::lean_dec(v_inst_301_);
    return v_res_305_;
}
pub unsafe fn l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop___redArg___lam__0(
    mut v_toPure_306_: *mut crate::leanh::LeanObject,
    mut v_recur_307_: *mut crate::leanh::LeanObject,
    mut v_it_308_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_309_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_309_) == 0 {
        let mut v_a_310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_it_308_);
        crate::leanh::lean_dec(v_recur_307_);
        v_a_310_ = crate::leanh::lean_ctor_get(v_____do__lift_309_, 0);
        crate::leanh::lean_inc(v_a_310_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_309_, 1);
        v___x_311_ = crate::leanh::lean_apply_2(v_toPure_306_, crate::leanh::lean_box(0), v_a_310_);
        return v___x_311_;
    } else {
        let mut v_a_312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_306_);
        v_a_312_ = crate::leanh::lean_ctor_get(v_____do__lift_309_, 0);
        crate::leanh::lean_inc(v_a_312_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_309_, 1);
        v___x_313_ = crate::leanh::lean_apply_4(
            v_recur_307_,
            v_it_308_,
            v_a_312_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_313_;
    }
}
pub unsafe fn l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop___redArg___lam__1(
    mut v_toPure_314_: *mut crate::leanh::LeanObject,
    mut v_recur_315_: *mut crate::leanh::LeanObject,
    mut v___y_316_: *mut crate::leanh::LeanObject,
    mut v_acc_317_: *mut crate::leanh::LeanObject,
    mut v_toBind_318_: *mut crate::leanh::LeanObject,
    mut v_s_319_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_s_319_) {
        0 => {
            let mut v_it_320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_it_320_ = crate::leanh::lean_ctor_get(v_s_319_, 0);
            crate::leanh::lean_inc(v_it_320_);
            v_out_321_ = crate::leanh::lean_ctor_get(v_s_319_, 1);
            crate::leanh::lean_inc(v_out_321_);
            crate::leanh::lean_dec_ref_known(v_s_319_, 2);
            v___f_322_ = crate::leanh::lean_alloc_closure(
                l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop___redArg___lam__0
                    as *mut core::ffi::c_void,
                4,
                3,
            );
            crate::leanh::lean_closure_set(v___f_322_, 0, v_toPure_314_);
            crate::leanh::lean_closure_set(v___f_322_, 1, v_recur_315_);
            crate::leanh::lean_closure_set(v___f_322_, 2, v_it_320_);
            v___x_323_ = crate::leanh::lean_apply_3(
                v___y_316_,
                v_out_321_,
                crate::leanh::lean_box(0),
                v_acc_317_,
            );
            v___x_324_ = crate::leanh::lean_apply_4(
                v_toBind_318_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_323_,
                v___f_322_,
            );
            return v___x_324_;
        }
        1 => {
            let mut v_it_325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_toBind_318_);
            crate::leanh::lean_dec(v___y_316_);
            crate::leanh::lean_dec(v_toPure_314_);
            v_it_325_ = crate::leanh::lean_ctor_get(v_s_319_, 0);
            crate::leanh::lean_inc(v_it_325_);
            crate::leanh::lean_dec_ref_known(v_s_319_, 1);
            v___x_326_ = crate::leanh::lean_apply_4(
                v_recur_315_,
                v_it_325_,
                v_acc_317_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_326_;
        }
        _ => {
            let mut v___x_327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_toBind_318_);
            crate::leanh::lean_dec(v___y_316_);
            crate::leanh::lean_dec(v_recur_315_);
            v___x_327_ =
                crate::leanh::lean_apply_2(v_toPure_314_, crate::leanh::lean_box(0), v_acc_317_);
            return v___x_327_;
        }
    }
}
pub unsafe fn l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop___redArg___lam__3(
    mut v_inst_328_: *mut crate::leanh::LeanObject,
    mut v_toPure_329_: *mut crate::leanh::LeanObject,
    mut v___y_330_: *mut crate::leanh::LeanObject,
    mut v_toBind_331_: *mut crate::leanh::LeanObject,
    mut v_inst_332_: *mut crate::leanh::LeanObject,
    mut v_lift_333_: *mut crate::leanh::LeanObject,
    mut v_it_334_: *mut crate::leanh::LeanObject,
    mut v_acc_335_: *mut crate::leanh::LeanObject,
    mut v_hP_336_: *mut crate::leanh::LeanObject,
    mut v_recur_337_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIdx_341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inner_343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_338_ = crate::leanh::lean_ctor_get(v_inst_328_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_338_);
    crate::leanh::lean_dec_ref(v_inst_328_);
    v_toFunctor_339_ = crate::leanh::lean_ctor_get(v_toApplicative_338_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_339_);
    crate::leanh::lean_dec_ref(v_toApplicative_338_);
    v_map_340_ = crate::leanh::lean_ctor_get(v_toFunctor_339_, 0);
    crate::leanh::lean_inc(v_map_340_);
    crate::leanh::lean_dec_ref(v_toFunctor_339_);
    v_nextIdx_341_ = crate::leanh::lean_ctor_get(v_it_334_, 0);
    crate::leanh::lean_inc(v_nextIdx_341_);
    v_n_342_ = crate::leanh::lean_ctor_get(v_it_334_, 1);
    crate::leanh::lean_inc(v_n_342_);
    v_inner_343_ = crate::leanh::lean_ctor_get(v_it_334_, 2);
    crate::leanh::lean_inc(v_inner_343_);
    crate::leanh::lean_dec_ref(v_it_334_);
    v___f_344_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop___redArg___lam__1
            as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___f_344_, 0, v_toPure_329_);
    crate::leanh::lean_closure_set(v___f_344_, 1, v_recur_337_);
    crate::leanh::lean_closure_set(v___f_344_, 2, v___y_330_);
    crate::leanh::lean_closure_set(v___f_344_, 3, v_acc_335_);
    crate::leanh::lean_closure_set(v___f_344_, 4, v_toBind_331_);
    v___f_345_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_Types_StepSizeIterator_instIterator___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_345_, 0, v_n_342_);
    v___x_346_ = crate::leanh::lean_apply_2(v_inst_332_, v_inner_343_, v_nextIdx_341_);
    v___x_347_ = crate::leanh::lean_apply_4(
        v_map_340_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_345_,
        v___x_346_,
    );
    v___x_348_ = crate::leanh::lean_apply_4(
        v_lift_333_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_344_,
        v___x_347_,
    );
    return v___x_348_;
}
pub unsafe fn l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop___redArg___lam__2(
    mut v_inst_349_: *mut crate::leanh::LeanObject,
    mut v_inst_350_: *mut crate::leanh::LeanObject,
    mut v_inst_351_: *mut crate::leanh::LeanObject,
    mut v_lift_352_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_353_: *mut crate::leanh::LeanObject,
    mut v_Pl_354_: *mut crate::leanh::LeanObject,
    mut v_it_355_: *mut crate::leanh::LeanObject,
    mut v_init_356_: *mut crate::leanh::LeanObject,
    mut v___y_357_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_358_ = crate::leanh::lean_ctor_get(v_inst_349_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_358_);
    v_toBind_359_ = crate::leanh::lean_ctor_get(v_inst_349_, 1);
    crate::leanh::lean_inc(v_toBind_359_);
    crate::leanh::lean_dec_ref(v_inst_349_);
    v_toPure_360_ = crate::leanh::lean_ctor_get(v_toApplicative_358_, 1);
    crate::leanh::lean_inc(v_toPure_360_);
    crate::leanh::lean_dec_ref(v_toApplicative_358_);
    v___f_361_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop___redArg___lam__3
            as *mut core::ffi::c_void,
        10,
        6,
    );
    crate::leanh::lean_closure_set(v___f_361_, 0, v_inst_350_);
    crate::leanh::lean_closure_set(v___f_361_, 1, v_toPure_360_);
    crate::leanh::lean_closure_set(v___f_361_, 2, v___y_357_);
    crate::leanh::lean_closure_set(v___f_361_, 3, v_toBind_359_);
    crate::leanh::lean_closure_set(v___f_361_, 4, v_inst_351_);
    crate::leanh::lean_closure_set(v___f_361_, 5, v_lift_352_);
    v___x_362_ = l_WellFounded_opaqueFix_u2083___redArg(
        v___f_361_,
        v_it_355_,
        v_init_356_,
        crate::leanh::lean_box(0),
    );
    return v___x_362_;
}
pub unsafe fn l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop___redArg(
    mut v_inst_363_: *mut crate::leanh::LeanObject,
    mut v_inst_364_: *mut crate::leanh::LeanObject,
    mut v_inst_365_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_366_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop___redArg___lam__2
            as *mut core::ffi::c_void,
        9,
        3,
    );
    crate::leanh::lean_closure_set(v___f_366_, 0, v_inst_365_);
    crate::leanh::lean_closure_set(v___f_366_, 1, v_inst_364_);
    crate::leanh::lean_closure_set(v___f_366_, 2, v_inst_363_);
    return v___f_366_;
}
pub unsafe fn l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop(
    mut v_00_u03b1_367_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_368_: *mut crate::leanh::LeanObject,
    mut v_m_369_: *mut crate::leanh::LeanObject,
    mut v_n_370_: *mut crate::leanh::LeanObject,
    mut v_inst_371_: *mut crate::leanh::LeanObject,
    mut v_inst_372_: *mut crate::leanh::LeanObject,
    mut v_inst_373_: *mut crate::leanh::LeanObject,
    mut v_inst_374_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_375_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop___redArg___lam__2
            as *mut core::ffi::c_void,
        9,
        3,
    );
    crate::leanh::lean_closure_set(v___f_375_, 0, v_inst_374_);
    crate::leanh::lean_closure_set(v___f_375_, 1, v_inst_373_);
    crate::leanh::lean_closure_set(v___f_375_, 2, v_inst_372_);
    return v___f_375_;
}
pub unsafe fn l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop___boxed(
    mut v_00_u03b1_376_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_377_: *mut crate::leanh::LeanObject,
    mut v_m_378_: *mut crate::leanh::LeanObject,
    mut v_n_379_: *mut crate::leanh::LeanObject,
    mut v_inst_380_: *mut crate::leanh::LeanObject,
    mut v_inst_381_: *mut crate::leanh::LeanObject,
    mut v_inst_382_: *mut crate::leanh::LeanObject,
    mut v_inst_383_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_inst_380_);
    return v_res_384_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_Iterators_Combinators_Monadic_StepSize(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Access(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_Iterators_Combinators_Monadic_StepSize(
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
pub unsafe fn initialize_Std_Data_Iterators_Combinators_Monadic_StepSize(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Consumers_Monadic_Access(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Combinators_Monadic_StepSize(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_Iterators_Combinators_Monadic_StepSize(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Data_Iterators_Combinators_Monadic_StepSize(builtin);
}
