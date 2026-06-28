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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_2,
    lean_apply_3, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_tag, lean_unsigned_to_nat,
};
pub unsafe fn l_Std_IterM_stepSize___redArg(
    mut v_it_193_: *mut LeanObject,
    mut v_n_194_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_198_: *mut LeanObject = core::ptr::null_mut();
    v___x_195_ = lean_unsigned_to_nat(0);
    v___x_196_ = lean_unsigned_to_nat(1);
    v___x_197_ = lean_nat_sub(v_n_194_, v___x_196_);
    v___x_198_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_198_, 0, v___x_195_);
    lean_ctor_set(v___x_198_, 1, v___x_197_);
    lean_ctor_set(v___x_198_, 2, v_it_193_);
    return v___x_198_;
}
pub unsafe fn l_Std_IterM_stepSize___redArg___boxed(
    mut v_it_199_: *mut LeanObject,
    mut v_n_200_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_201_: *mut LeanObject = core::ptr::null_mut();
    v_res_201_ = l_Std_IterM_stepSize___redArg(v_it_199_, v_n_200_);
    lean_dec(v_n_200_);
    return v_res_201_;
}
pub unsafe fn l_Std_IterM_stepSize(
    mut v_00_u03b1_202_: *mut LeanObject,
    mut v_m_203_: *mut LeanObject,
    mut v_00_u03b2_204_: *mut LeanObject,
    mut v_inst_205_: *mut LeanObject,
    mut v_inst_206_: *mut LeanObject,
    mut v_inst_207_: *mut LeanObject,
    mut v_it_208_: *mut LeanObject,
    mut v_n_209_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_213_: *mut LeanObject = core::ptr::null_mut();
    v___x_210_ = lean_unsigned_to_nat(0);
    v___x_211_ = lean_unsigned_to_nat(1);
    v___x_212_ = lean_nat_sub(v_n_209_, v___x_211_);
    v___x_213_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_213_, 0, v___x_210_);
    lean_ctor_set(v___x_213_, 1, v___x_212_);
    lean_ctor_set(v___x_213_, 2, v_it_208_);
    return v___x_213_;
}
pub unsafe fn l_Std_IterM_stepSize___boxed(
    mut v_00_u03b1_214_: *mut LeanObject,
    mut v_m_215_: *mut LeanObject,
    mut v_00_u03b2_216_: *mut LeanObject,
    mut v_inst_217_: *mut LeanObject,
    mut v_inst_218_: *mut LeanObject,
    mut v_inst_219_: *mut LeanObject,
    mut v_it_220_: *mut LeanObject,
    mut v_n_221_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_222_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_n_221_);
    lean_dec_ref(v_inst_219_);
    lean_dec(v_inst_218_);
    lean_dec(v_inst_217_);
    return v_res_222_;
}
pub unsafe fn l_Std_Iterators_Types_StepSizeIterator_instIterator___redArg___lam__0(
    mut v_n_223_: *mut LeanObject,
    mut v_s_224_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_it_225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_out_226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_229_: u8 = 0;
    let mut v___x_230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_234_: u8 = 0;
    let mut v_it_235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_238_: u8 = 0;
    let mut v___x_239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_243_: u8 = 0;
    let mut v___x_244_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_s_224_) {
                0 => {
                    v_it_225_ = lean_ctor_get(v_s_224_, 0);
                    v_out_226_ = lean_ctor_get(v_s_224_, 1);
                    v_isSharedCheck_234_ = (!lean_is_exclusive(v_s_224_)) as u8;
                    if v_isSharedCheck_234_ == 0 {
                        v___x_228_ = v_s_224_;
                        v_isShared_229_ = v_isSharedCheck_234_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_out_226_);
                        lean_inc(v_it_225_);
                        lean_dec(v_s_224_);
                        v___x_228_ = lean_box(0);
                        v_isShared_229_ = v_isSharedCheck_234_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_it_235_ = lean_ctor_get(v_s_224_, 0);
                    v_isSharedCheck_243_ = (!lean_is_exclusive(v_s_224_)) as u8;
                    if v_isSharedCheck_243_ == 0 {
                        v___x_237_ = v_s_224_;
                        v_isShared_238_ = v_isSharedCheck_243_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_it_235_);
                        lean_dec(v_s_224_);
                        v___x_237_ = lean_box(0);
                        v_isShared_238_ = v_isSharedCheck_243_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    lean_dec(v_n_223_);
                    v___x_244_ = lean_box(2);
                    return v___x_244_;
                }
            },
            1 => {
                lean_inc(v_n_223_);
                v___x_230_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_230_, 0, v_n_223_);
                lean_ctor_set(v___x_230_, 1, v_n_223_);
                lean_ctor_set(v___x_230_, 2, v_it_225_);
                if v_isShared_229_ == 0 {
                    lean_ctor_set(v___x_228_, 0, v___x_230_);
                    v___x_232_ = v___x_228_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_233_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_233_, 0, v___x_230_);
                    lean_ctor_set(v_reuseFailAlloc_233_, 1, v_out_226_);
                    v___x_232_ = v_reuseFailAlloc_233_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_232_;
            }
            3 => {
                lean_inc(v_n_223_);
                v___x_239_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_239_, 0, v_n_223_);
                lean_ctor_set(v___x_239_, 1, v_n_223_);
                lean_ctor_set(v___x_239_, 2, v_it_235_);
                if v_isShared_238_ == 0 {
                    lean_ctor_set(v___x_237_, 0, v___x_239_);
                    v___x_241_ = v___x_237_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_242_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_242_, 0, v___x_239_);
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
    mut v_toFunctor_245_: *mut LeanObject,
    mut v_inst_246_: *mut LeanObject,
    mut v_it_247_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextIdx_249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inner_251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_254_: *mut LeanObject = core::ptr::null_mut();
    v_map_248_ = lean_ctor_get(v_toFunctor_245_, 0);
    lean_inc(v_map_248_);
    lean_dec_ref(v_toFunctor_245_);
    v_nextIdx_249_ = lean_ctor_get(v_it_247_, 0);
    lean_inc(v_nextIdx_249_);
    v_n_250_ = lean_ctor_get(v_it_247_, 1);
    lean_inc(v_n_250_);
    v_inner_251_ = lean_ctor_get(v_it_247_, 2);
    lean_inc(v_inner_251_);
    lean_dec_ref(v_it_247_);
    v___f_252_ = lean_alloc_closure(
        l_Std_Iterators_Types_StepSizeIterator_instIterator___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_252_, 0, v_n_250_);
    v___x_253_ = lean_apply_2(v_inst_246_, v_inner_251_, v_nextIdx_249_);
    v___x_254_ = lean_apply_4(v_map_248_, lean_box(0), lean_box(0), v___f_252_, v___x_253_);
    return v___x_254_;
}
pub unsafe fn l_Std_Iterators_Types_StepSizeIterator_instIterator___redArg(
    mut v_inst_255_: *mut LeanObject,
    mut v_inst_256_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_259_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_257_ = lean_ctor_get(v_inst_256_, 0);
    lean_inc_ref(v_toApplicative_257_);
    lean_dec_ref(v_inst_256_);
    v_toFunctor_258_ = lean_ctor_get(v_toApplicative_257_, 0);
    lean_inc_ref(v_toFunctor_258_);
    lean_dec_ref(v_toApplicative_257_);
    v___f_259_ = lean_alloc_closure(
        l_Std_Iterators_Types_StepSizeIterator_instIterator___redArg___lam__1
            as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_259_, 0, v_toFunctor_258_);
    lean_closure_set(v___f_259_, 1, v_inst_255_);
    return v___f_259_;
}
pub unsafe fn l_Std_Iterators_Types_StepSizeIterator_instIterator(
    mut v_00_u03b1_260_: *mut LeanObject,
    mut v_m_261_: *mut LeanObject,
    mut v_00_u03b2_262_: *mut LeanObject,
    mut v_inst_263_: *mut LeanObject,
    mut v_inst_264_: *mut LeanObject,
    mut v_inst_265_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_266_: *mut LeanObject = core::ptr::null_mut();
    v___x_266_ =
        l_Std_Iterators_Types_StepSizeIterator_instIterator___redArg(v_inst_264_, v_inst_265_);
    return v___x_266_;
}
pub unsafe fn l_Std_Iterators_Types_StepSizeIterator_instIterator___boxed(
    mut v_00_u03b1_267_: *mut LeanObject,
    mut v_m_268_: *mut LeanObject,
    mut v_00_u03b2_269_: *mut LeanObject,
    mut v_inst_270_: *mut LeanObject,
    mut v_inst_271_: *mut LeanObject,
    mut v_inst_272_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_273_: *mut LeanObject = core::ptr::null_mut();
    v_res_273_ = l_Std_Iterators_Types_StepSizeIterator_instIterator(
        v_00_u03b1_267_,
        v_m_268_,
        v_00_u03b2_269_,
        v_inst_270_,
        v_inst_271_,
        v_inst_272_,
    );
    lean_dec(v_inst_270_);
    return v_res_273_;
}
pub unsafe fn l_Std_Iterators_Types_StepSizeIterator_instFinitenessRelation(
    mut v_00_u03b1_274_: *mut LeanObject,
    mut v_m_275_: *mut LeanObject,
    mut v_00_u03b2_276_: *mut LeanObject,
    mut v_inst_277_: *mut LeanObject,
    mut v_inst_278_: *mut LeanObject,
    mut v_inst_279_: *mut LeanObject,
    mut v_inst_280_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_281_: *mut LeanObject = core::ptr::null_mut();
    v___x_281_ = lean_box(0);
    return v___x_281_;
}
pub unsafe fn l_Std_Iterators_Types_StepSizeIterator_instFinitenessRelation___boxed(
    mut v_00_u03b1_282_: *mut LeanObject,
    mut v_m_283_: *mut LeanObject,
    mut v_00_u03b2_284_: *mut LeanObject,
    mut v_inst_285_: *mut LeanObject,
    mut v_inst_286_: *mut LeanObject,
    mut v_inst_287_: *mut LeanObject,
    mut v_inst_288_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_289_: *mut LeanObject = core::ptr::null_mut();
    v_res_289_ = l_Std_Iterators_Types_StepSizeIterator_instFinitenessRelation(
        v_00_u03b1_282_,
        v_m_283_,
        v_00_u03b2_284_,
        v_inst_285_,
        v_inst_286_,
        v_inst_287_,
        v_inst_288_,
    );
    lean_dec_ref(v_inst_287_);
    lean_dec(v_inst_286_);
    lean_dec(v_inst_285_);
    return v_res_289_;
}
pub unsafe fn l_Std_Iterators_Types_StepSizeIterator_instProductivenessRelation(
    mut v_00_u03b1_290_: *mut LeanObject,
    mut v_m_291_: *mut LeanObject,
    mut v_00_u03b2_292_: *mut LeanObject,
    mut v_inst_293_: *mut LeanObject,
    mut v_inst_294_: *mut LeanObject,
    mut v_inst_295_: *mut LeanObject,
    mut v_inst_296_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_297_: *mut LeanObject = core::ptr::null_mut();
    v___x_297_ = lean_box(0);
    return v___x_297_;
}
pub unsafe fn l_Std_Iterators_Types_StepSizeIterator_instProductivenessRelation___boxed(
    mut v_00_u03b1_298_: *mut LeanObject,
    mut v_m_299_: *mut LeanObject,
    mut v_00_u03b2_300_: *mut LeanObject,
    mut v_inst_301_: *mut LeanObject,
    mut v_inst_302_: *mut LeanObject,
    mut v_inst_303_: *mut LeanObject,
    mut v_inst_304_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_305_: *mut LeanObject = core::ptr::null_mut();
    v_res_305_ = l_Std_Iterators_Types_StepSizeIterator_instProductivenessRelation(
        v_00_u03b1_298_,
        v_m_299_,
        v_00_u03b2_300_,
        v_inst_301_,
        v_inst_302_,
        v_inst_303_,
        v_inst_304_,
    );
    lean_dec_ref(v_inst_303_);
    lean_dec(v_inst_302_);
    lean_dec(v_inst_301_);
    return v_res_305_;
}
pub unsafe fn l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop___redArg___lam__0(
    mut v_toPure_306_: *mut LeanObject,
    mut v_recur_307_: *mut LeanObject,
    mut v_it_308_: *mut LeanObject,
    mut v_____do__lift_309_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_309_) == 0 {
        let mut v_a_310_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_311_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_it_308_);
        lean_dec(v_recur_307_);
        v_a_310_ = lean_ctor_get(v_____do__lift_309_, 0);
        lean_inc(v_a_310_);
        lean_dec_ref_known(v_____do__lift_309_, 1);
        v___x_311_ = lean_apply_2(v_toPure_306_, lean_box(0), v_a_310_);
        return v___x_311_;
    } else {
        let mut v_a_312_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_313_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_306_);
        v_a_312_ = lean_ctor_get(v_____do__lift_309_, 0);
        lean_inc(v_a_312_);
        lean_dec_ref_known(v_____do__lift_309_, 1);
        v___x_313_ = lean_apply_4(v_recur_307_, v_it_308_, v_a_312_, lean_box(0), lean_box(0));
        return v___x_313_;
    }
}
pub unsafe fn l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop___redArg___lam__1(
    mut v_toPure_314_: *mut LeanObject,
    mut v_recur_315_: *mut LeanObject,
    mut v___y_316_: *mut LeanObject,
    mut v_acc_317_: *mut LeanObject,
    mut v_toBind_318_: *mut LeanObject,
    mut v_s_319_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_s_319_) {
        0 => {
            let mut v_it_320_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_321_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_322_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_323_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_324_: *mut LeanObject = core::ptr::null_mut();
            v_it_320_ = lean_ctor_get(v_s_319_, 0);
            lean_inc(v_it_320_);
            v_out_321_ = lean_ctor_get(v_s_319_, 1);
            lean_inc(v_out_321_);
            lean_dec_ref_known(v_s_319_, 2);
            v___f_322_ = lean_alloc_closure(
                l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop___redArg___lam__0
                    as *mut core::ffi::c_void,
                4,
                3,
            );
            lean_closure_set(v___f_322_, 0, v_toPure_314_);
            lean_closure_set(v___f_322_, 1, v_recur_315_);
            lean_closure_set(v___f_322_, 2, v_it_320_);
            v___x_323_ = lean_apply_3(v___y_316_, v_out_321_, lean_box(0), v_acc_317_);
            v___x_324_ = lean_apply_4(
                v_toBind_318_,
                lean_box(0),
                lean_box(0),
                v___x_323_,
                v___f_322_,
            );
            return v___x_324_;
        }
        1 => {
            let mut v_it_325_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_326_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_toBind_318_);
            lean_dec(v___y_316_);
            lean_dec(v_toPure_314_);
            v_it_325_ = lean_ctor_get(v_s_319_, 0);
            lean_inc(v_it_325_);
            lean_dec_ref_known(v_s_319_, 1);
            v___x_326_ = lean_apply_4(
                v_recur_315_,
                v_it_325_,
                v_acc_317_,
                lean_box(0),
                lean_box(0),
            );
            return v___x_326_;
        }
        _ => {
            let mut v___x_327_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_toBind_318_);
            lean_dec(v___y_316_);
            lean_dec(v_recur_315_);
            v___x_327_ = lean_apply_2(v_toPure_314_, lean_box(0), v_acc_317_);
            return v___x_327_;
        }
    }
}
pub unsafe fn l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop___redArg___lam__3(
    mut v_inst_328_: *mut LeanObject,
    mut v_toPure_329_: *mut LeanObject,
    mut v___y_330_: *mut LeanObject,
    mut v_toBind_331_: *mut LeanObject,
    mut v_inst_332_: *mut LeanObject,
    mut v_lift_333_: *mut LeanObject,
    mut v_it_334_: *mut LeanObject,
    mut v_acc_335_: *mut LeanObject,
    mut v_hP_336_: *mut LeanObject,
    mut v_recur_337_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextIdx_341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inner_343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_348_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_338_ = lean_ctor_get(v_inst_328_, 0);
    lean_inc_ref(v_toApplicative_338_);
    lean_dec_ref(v_inst_328_);
    v_toFunctor_339_ = lean_ctor_get(v_toApplicative_338_, 0);
    lean_inc_ref(v_toFunctor_339_);
    lean_dec_ref(v_toApplicative_338_);
    v_map_340_ = lean_ctor_get(v_toFunctor_339_, 0);
    lean_inc(v_map_340_);
    lean_dec_ref(v_toFunctor_339_);
    v_nextIdx_341_ = lean_ctor_get(v_it_334_, 0);
    lean_inc(v_nextIdx_341_);
    v_n_342_ = lean_ctor_get(v_it_334_, 1);
    lean_inc(v_n_342_);
    v_inner_343_ = lean_ctor_get(v_it_334_, 2);
    lean_inc(v_inner_343_);
    lean_dec_ref(v_it_334_);
    v___f_344_ = lean_alloc_closure(
        l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop___redArg___lam__1
            as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_344_, 0, v_toPure_329_);
    lean_closure_set(v___f_344_, 1, v_recur_337_);
    lean_closure_set(v___f_344_, 2, v___y_330_);
    lean_closure_set(v___f_344_, 3, v_acc_335_);
    lean_closure_set(v___f_344_, 4, v_toBind_331_);
    v___f_345_ = lean_alloc_closure(
        l_Std_Iterators_Types_StepSizeIterator_instIterator___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_345_, 0, v_n_342_);
    v___x_346_ = lean_apply_2(v_inst_332_, v_inner_343_, v_nextIdx_341_);
    v___x_347_ = lean_apply_4(v_map_340_, lean_box(0), lean_box(0), v___f_345_, v___x_346_);
    v___x_348_ = lean_apply_4(
        v_lift_333_,
        lean_box(0),
        lean_box(0),
        v___f_344_,
        v___x_347_,
    );
    return v___x_348_;
}
pub unsafe fn l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop___redArg___lam__2(
    mut v_inst_349_: *mut LeanObject,
    mut v_inst_350_: *mut LeanObject,
    mut v_inst_351_: *mut LeanObject,
    mut v_lift_352_: *mut LeanObject,
    mut v_00_u03b3_353_: *mut LeanObject,
    mut v_Pl_354_: *mut LeanObject,
    mut v_it_355_: *mut LeanObject,
    mut v_init_356_: *mut LeanObject,
    mut v___y_357_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_362_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_358_ = lean_ctor_get(v_inst_349_, 0);
    lean_inc_ref(v_toApplicative_358_);
    v_toBind_359_ = lean_ctor_get(v_inst_349_, 1);
    lean_inc(v_toBind_359_);
    lean_dec_ref(v_inst_349_);
    v_toPure_360_ = lean_ctor_get(v_toApplicative_358_, 1);
    lean_inc(v_toPure_360_);
    lean_dec_ref(v_toApplicative_358_);
    v___f_361_ = lean_alloc_closure(
        l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop___redArg___lam__3
            as *mut core::ffi::c_void,
        10,
        6,
    );
    lean_closure_set(v___f_361_, 0, v_inst_350_);
    lean_closure_set(v___f_361_, 1, v_toPure_360_);
    lean_closure_set(v___f_361_, 2, v___y_357_);
    lean_closure_set(v___f_361_, 3, v_toBind_359_);
    lean_closure_set(v___f_361_, 4, v_inst_351_);
    lean_closure_set(v___f_361_, 5, v_lift_352_);
    v___x_362_ =
        l_WellFounded_opaqueFix_u2083___redArg(v___f_361_, v_it_355_, v_init_356_, lean_box(0));
    return v___x_362_;
}
pub unsafe fn l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop___redArg(
    mut v_inst_363_: *mut LeanObject,
    mut v_inst_364_: *mut LeanObject,
    mut v_inst_365_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_366_: *mut LeanObject = core::ptr::null_mut();
    v___f_366_ = lean_alloc_closure(
        l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop___redArg___lam__2
            as *mut core::ffi::c_void,
        9,
        3,
    );
    lean_closure_set(v___f_366_, 0, v_inst_365_);
    lean_closure_set(v___f_366_, 1, v_inst_364_);
    lean_closure_set(v___f_366_, 2, v_inst_363_);
    return v___f_366_;
}
pub unsafe fn l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop(
    mut v_00_u03b1_367_: *mut LeanObject,
    mut v_00_u03b2_368_: *mut LeanObject,
    mut v_m_369_: *mut LeanObject,
    mut v_n_370_: *mut LeanObject,
    mut v_inst_371_: *mut LeanObject,
    mut v_inst_372_: *mut LeanObject,
    mut v_inst_373_: *mut LeanObject,
    mut v_inst_374_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_375_: *mut LeanObject = core::ptr::null_mut();
    v___f_375_ = lean_alloc_closure(
        l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop___redArg___lam__2
            as *mut core::ffi::c_void,
        9,
        3,
    );
    lean_closure_set(v___f_375_, 0, v_inst_374_);
    lean_closure_set(v___f_375_, 1, v_inst_373_);
    lean_closure_set(v___f_375_, 2, v_inst_372_);
    return v___f_375_;
}
pub unsafe fn l_Std_Iterators_Types_StepSizeIterator_instIteratorLoop___boxed(
    mut v_00_u03b1_376_: *mut LeanObject,
    mut v_00_u03b2_377_: *mut LeanObject,
    mut v_m_378_: *mut LeanObject,
    mut v_n_379_: *mut LeanObject,
    mut v_inst_380_: *mut LeanObject,
    mut v_inst_381_: *mut LeanObject,
    mut v_inst_382_: *mut LeanObject,
    mut v_inst_383_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_384_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_inst_380_);
    return v_res_384_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_Iterators_Combinators_Monadic_StepSize(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Access(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_Iterators_Combinators_Monadic_StepSize(
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
pub unsafe fn initialize_Std_Data_Iterators_Combinators_Monadic_StepSize(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Consumers_Monadic_Access(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Combinators_Monadic_StepSize(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Data_Iterators_Combinators_Monadic_StepSize(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Data_Iterators_Combinators_Monadic_StepSize(builtin);
}
