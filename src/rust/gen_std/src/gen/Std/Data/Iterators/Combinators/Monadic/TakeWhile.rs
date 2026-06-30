// Lean compiler output
// Module: Std.Data.Iterators.Combinators.Monadic.TakeWhile
// Imports: Init.Data.Nat.Lemmas Init.Data.Iterators.Consumers.Monadic.Collect Init.Data.Iterators.Consumers.Monadic.Loop Init.Data.Iterators.PostconditionMonad
use crate::r#gen::Init::Data::Iterators::Consumers::Monadic::Collect::{
    initialize_Init_Data_Iterators_Consumers_Monadic_Collect,
    runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect,
};
use crate::r#gen::Init::Data::Iterators::Consumers::Monadic::Loop::{
    initialize_Init_Data_Iterators_Consumers_Monadic_Loop,
    runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop,
};
use crate::r#gen::Init::Data::Iterators::PostconditionMonad::{
    initialize_Init_Data_Iterators_PostconditionMonad,
    runtime_initialize_Init_Data_Iterators_PostconditionMonad,
};
use crate::r#gen::Init::Data::Nat::Lemmas::{
    initialize_Init_Data_Nat_Lemmas, runtime_initialize_Init_Data_Nat_Lemmas,
};
use crate::r#gen::Init::WFExtrinsicFix::l_WellFounded_opaqueFix_u2083___redArg;
pub unsafe fn l_Std_IterM_takeWhileWithPostcondition___redArg(
    mut v_it_221_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_it_221_);
    return v_it_221_;
}
pub unsafe fn l_Std_IterM_takeWhileWithPostcondition___redArg___boxed(
    mut v_it_222_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_223_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_223_ = l_Std_IterM_takeWhileWithPostcondition___redArg(v_it_222_);
    leanh::lean_dec(v_it_222_);
    return v_res_223_;
}
pub unsafe fn l_Std_IterM_takeWhileWithPostcondition(
    mut v_00_u03b1_224_: *mut leanh::LeanObject,
    mut v_m_225_: *mut leanh::LeanObject,
    mut v_00_u03b2_226_: *mut leanh::LeanObject,
    mut v_P_227_: *mut leanh::LeanObject,
    mut v_it_228_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_it_228_);
    return v_it_228_;
}
pub unsafe fn l_Std_IterM_takeWhileWithPostcondition___boxed(
    mut v_00_u03b1_229_: *mut leanh::LeanObject,
    mut v_m_230_: *mut leanh::LeanObject,
    mut v_00_u03b2_231_: *mut leanh::LeanObject,
    mut v_P_232_: *mut leanh::LeanObject,
    mut v_it_233_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_234_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_234_ = l_Std_IterM_takeWhileWithPostcondition(
        v_00_u03b1_229_,
        v_m_230_,
        v_00_u03b2_231_,
        v_P_232_,
        v_it_233_,
    );
    leanh::lean_dec(v_it_233_);
    leanh::lean_dec(v_P_232_);
    return v_res_234_;
}
pub unsafe fn l_Std_IterM_takeWhileM___redArg(
    mut v_it_235_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_it_235_);
    return v_it_235_;
}
pub unsafe fn l_Std_IterM_takeWhileM___redArg___boxed(
    mut v_it_236_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_237_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_237_ = l_Std_IterM_takeWhileM___redArg(v_it_236_);
    leanh::lean_dec(v_it_236_);
    return v_res_237_;
}
pub unsafe fn l_Std_IterM_takeWhileM(
    mut v_00_u03b1_238_: *mut leanh::LeanObject,
    mut v_m_239_: *mut leanh::LeanObject,
    mut v_00_u03b2_240_: *mut leanh::LeanObject,
    mut v_inst_241_: *mut leanh::LeanObject,
    mut v_inst_242_: *mut leanh::LeanObject,
    mut v_P_243_: *mut leanh::LeanObject,
    mut v_it_244_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_it_244_);
    return v_it_244_;
}
pub unsafe fn l_Std_IterM_takeWhileM___boxed(
    mut v_00_u03b1_245_: *mut leanh::LeanObject,
    mut v_m_246_: *mut leanh::LeanObject,
    mut v_00_u03b2_247_: *mut leanh::LeanObject,
    mut v_inst_248_: *mut leanh::LeanObject,
    mut v_inst_249_: *mut leanh::LeanObject,
    mut v_P_250_: *mut leanh::LeanObject,
    mut v_it_251_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_252_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_252_ = l_Std_IterM_takeWhileM(
        v_00_u03b1_245_,
        v_m_246_,
        v_00_u03b2_247_,
        v_inst_248_,
        v_inst_249_,
        v_P_250_,
        v_it_251_,
    );
    leanh::lean_dec(v_it_251_);
    leanh::lean_dec(v_P_250_);
    leanh::lean_dec(v_inst_249_);
    leanh::lean_dec_ref(v_inst_248_);
    return v_res_252_;
}
pub unsafe fn l_Std_IterM_takeWhile___redArg(
    mut v_it_253_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_it_253_);
    return v_it_253_;
}
pub unsafe fn l_Std_IterM_takeWhile___redArg___boxed(
    mut v_it_254_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_255_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_255_ = l_Std_IterM_takeWhile___redArg(v_it_254_);
    leanh::lean_dec(v_it_254_);
    return v_res_255_;
}
pub unsafe fn l_Std_IterM_takeWhile(
    mut v_00_u03b1_256_: *mut leanh::LeanObject,
    mut v_m_257_: *mut leanh::LeanObject,
    mut v_00_u03b2_258_: *mut leanh::LeanObject,
    mut v_inst_259_: *mut leanh::LeanObject,
    mut v_P_260_: *mut leanh::LeanObject,
    mut v_it_261_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_it_261_);
    return v_it_261_;
}
pub unsafe fn l_Std_IterM_takeWhile___boxed(
    mut v_00_u03b1_262_: *mut leanh::LeanObject,
    mut v_m_263_: *mut leanh::LeanObject,
    mut v_00_u03b2_264_: *mut leanh::LeanObject,
    mut v_inst_265_: *mut leanh::LeanObject,
    mut v_P_266_: *mut leanh::LeanObject,
    mut v_it_267_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_268_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_268_ = l_Std_IterM_takeWhile(
        v_00_u03b1_262_,
        v_m_263_,
        v_00_u03b2_264_,
        v_inst_265_,
        v_P_266_,
        v_it_267_,
    );
    leanh::lean_dec(v_it_267_);
    leanh::lean_dec_ref(v_P_266_);
    leanh::lean_dec_ref(v_inst_265_);
    return v_res_268_;
}
pub unsafe fn l_Std_Iterators_Types_TakeWhile_instIterator___redArg___lam__0(
    mut v_toPure_269_: *mut leanh::LeanObject,
    mut v_it_270_: *mut leanh::LeanObject,
    mut v_out_271_: *mut leanh::LeanObject,
    mut v_____do__lift_272_: u8,
) -> *mut leanh::LeanObject {
    if v_____do__lift_272_ == 0 {
        let mut v___x_273_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_274_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_out_271_);
        leanh::lean_dec(v_it_270_);
        v___x_273_ = leanh::lean_box(2);
        v___x_274_ =
            leanh::lean_apply_2(v_toPure_269_, leanh::lean_box(0), v___x_273_);
        return v___x_274_;
    } else {
        let mut v___x_275_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_276_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_275_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_275_, 0, v_it_270_);
        leanh::lean_ctor_set(v___x_275_, 1, v_out_271_);
        v___x_276_ =
            leanh::lean_apply_2(v_toPure_269_, leanh::lean_box(0), v___x_275_);
        return v___x_276_;
    }
}
pub unsafe fn l_Std_Iterators_Types_TakeWhile_instIterator___redArg___lam__0___boxed(
    mut v_toPure_277_: *mut leanh::LeanObject,
    mut v_it_278_: *mut leanh::LeanObject,
    mut v_out_279_: *mut leanh::LeanObject,
    mut v_____do__lift_280_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_____do__lift_267__boxed_281_: u8 = 0;
    let mut v_res_282_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_267__boxed_281_ = (leanh::lean_unbox(v_____do__lift_280_) as u8);
    v_res_282_ = l_Std_Iterators_Types_TakeWhile_instIterator___redArg___lam__0(
        v_toPure_277_,
        v_it_278_,
        v_out_279_,
        v_____do__lift_267__boxed_281_,
    );
    return v_res_282_;
}
pub unsafe fn l_Std_Iterators_Types_TakeWhile_instIterator___redArg___lam__1(
    mut v_toPure_283_: *mut leanh::LeanObject,
    mut v_P_284_: *mut leanh::LeanObject,
    mut v_toBind_285_: *mut leanh::LeanObject,
    mut v_____do__lift_286_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_it_287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_295_: u8 = 0;
    let mut v___x_297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_300_: u8 = 0;
    let mut v___x_301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_____do__lift_286_) {
                0 => {
                    v_it_287_ = leanh::lean_ctor_get(v_____do__lift_286_, 0);
                    leanh::lean_inc(v_it_287_);
                    v_out_288_ = leanh::lean_ctor_get(v_____do__lift_286_, 1);
                    leanh::lean_inc_n(v_out_288_, 2);
                    leanh::lean_dec_ref_known(v_____do__lift_286_, 2);
                    v___f_289_ = leanh::lean_alloc_closure(
                        l_Std_Iterators_Types_TakeWhile_instIterator___redArg___lam__0___boxed
                            as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    leanh::lean_closure_set(v___f_289_, 0, v_toPure_283_);
                    leanh::lean_closure_set(v___f_289_, 1, v_it_287_);
                    leanh::lean_closure_set(v___f_289_, 2, v_out_288_);
                    v___x_290_ = leanh::lean_apply_1(v_P_284_, v_out_288_);
                    v___x_291_ = leanh::lean_apply_4(
                        v_toBind_285_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_290_,
                        v___f_289_,
                    );
                    return v___x_291_;
                }
                1 => {
                    leanh::lean_dec(v_toBind_285_);
                    leanh::lean_dec(v_P_284_);
                    v_it_292_ = leanh::lean_ctor_get(v_____do__lift_286_, 0);
                    v_isSharedCheck_300_ =
                        (!leanh::lean_is_exclusive(v_____do__lift_286_)) as u8;
                    if v_isSharedCheck_300_ == 0 {
                        v___x_294_ = v_____do__lift_286_;
                        v_isShared_295_ = v_isSharedCheck_300_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_it_292_);
                        leanh::lean_dec(v_____do__lift_286_);
                        v___x_294_ = leanh::lean_box(0);
                        v_isShared_295_ = v_isSharedCheck_300_;
                        state = 1;
                        continue;
                    }
                }
                _ => {
                    leanh::lean_dec(v_toBind_285_);
                    leanh::lean_dec(v_P_284_);
                    v___x_301_ = leanh::lean_box(2);
                    v___x_302_ = leanh::lean_apply_2(
                        v_toPure_283_,
                        leanh::lean_box(0),
                        v___x_301_,
                    );
                    return v___x_302_;
                }
            },
            1 => {
                if v_isShared_295_ == 0 {
                    v___x_297_ = v___x_294_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_299_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_299_, 0, v_it_292_);
                    v___x_297_ = v_reuseFailAlloc_299_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_298_ = leanh::lean_apply_2(
                    v_toPure_283_,
                    leanh::lean_box(0),
                    v___x_297_,
                );
                return v___x_298_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Iterators_Types_TakeWhile_instIterator___redArg___lam__2(
    mut v_inst_303_: *mut leanh::LeanObject,
    mut v_toBind_304_: *mut leanh::LeanObject,
    mut v___f_305_: *mut leanh::LeanObject,
    mut v_it_306_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_308_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_307_ = leanh::lean_apply_1(v_inst_303_, v_it_306_);
    v___x_308_ = leanh::lean_apply_4(
        v_toBind_304_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_307_,
        v___f_305_,
    );
    return v___x_308_;
}
pub unsafe fn l_Std_Iterators_Types_TakeWhile_instIterator___redArg(
    mut v_inst_309_: *mut leanh::LeanObject,
    mut v_inst_310_: *mut leanh::LeanObject,
    mut v_P_311_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_316_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_312_ = leanh::lean_ctor_get(v_inst_309_, 0);
    leanh::lean_inc_ref(v_toApplicative_312_);
    v_toBind_313_ = leanh::lean_ctor_get(v_inst_309_, 1);
    leanh::lean_inc_n(v_toBind_313_, 2);
    leanh::lean_dec_ref(v_inst_309_);
    v_toPure_314_ = leanh::lean_ctor_get(v_toApplicative_312_, 1);
    leanh::lean_inc(v_toPure_314_);
    leanh::lean_dec_ref(v_toApplicative_312_);
    v___f_315_ = leanh::lean_alloc_closure(
        l_Std_Iterators_Types_TakeWhile_instIterator___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_315_, 0, v_toPure_314_);
    leanh::lean_closure_set(v___f_315_, 1, v_P_311_);
    leanh::lean_closure_set(v___f_315_, 2, v_toBind_313_);
    v___f_316_ = leanh::lean_alloc_closure(
        l_Std_Iterators_Types_TakeWhile_instIterator___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_316_, 0, v_inst_310_);
    leanh::lean_closure_set(v___f_316_, 1, v_toBind_313_);
    leanh::lean_closure_set(v___f_316_, 2, v___f_315_);
    return v___f_316_;
}
pub unsafe fn l_Std_Iterators_Types_TakeWhile_instIterator(
    mut v_00_u03b1_317_: *mut leanh::LeanObject,
    mut v_m_318_: *mut leanh::LeanObject,
    mut v_00_u03b2_319_: *mut leanh::LeanObject,
    mut v_inst_320_: *mut leanh::LeanObject,
    mut v_inst_321_: *mut leanh::LeanObject,
    mut v_P_322_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_327_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_323_ = leanh::lean_ctor_get(v_inst_320_, 0);
    leanh::lean_inc_ref(v_toApplicative_323_);
    v_toBind_324_ = leanh::lean_ctor_get(v_inst_320_, 1);
    leanh::lean_inc_n(v_toBind_324_, 2);
    leanh::lean_dec_ref(v_inst_320_);
    v_toPure_325_ = leanh::lean_ctor_get(v_toApplicative_323_, 1);
    leanh::lean_inc(v_toPure_325_);
    leanh::lean_dec_ref(v_toApplicative_323_);
    v___f_326_ = leanh::lean_alloc_closure(
        l_Std_Iterators_Types_TakeWhile_instIterator___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_326_, 0, v_toPure_325_);
    leanh::lean_closure_set(v___f_326_, 1, v_P_322_);
    leanh::lean_closure_set(v___f_326_, 2, v_toBind_324_);
    v___f_327_ = leanh::lean_alloc_closure(
        l_Std_Iterators_Types_TakeWhile_instIterator___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_327_, 0, v_inst_321_);
    leanh::lean_closure_set(v___f_327_, 1, v_toBind_324_);
    leanh::lean_closure_set(v___f_327_, 2, v___f_326_);
    return v___f_327_;
}
pub unsafe fn l___private_Std_Data_Iterators_Combinators_Monadic_TakeWhile_0__Std_Iterators_Types_TakeWhile_instFinitenessRelation(
    mut v_00_u03b1_328_: *mut leanh::LeanObject,
    mut v_m_329_: *mut leanh::LeanObject,
    mut v_00_u03b2_330_: *mut leanh::LeanObject,
    mut v_inst_331_: *mut leanh::LeanObject,
    mut v_inst_332_: *mut leanh::LeanObject,
    mut v_inst_333_: *mut leanh::LeanObject,
    mut v_P_334_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_335_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_335_ = leanh::lean_box(0);
    return v___x_335_;
}
pub unsafe fn l___private_Std_Data_Iterators_Combinators_Monadic_TakeWhile_0__Std_Iterators_Types_TakeWhile_instFinitenessRelation___boxed(
    mut v_00_u03b1_336_: *mut leanh::LeanObject,
    mut v_m_337_: *mut leanh::LeanObject,
    mut v_00_u03b2_338_: *mut leanh::LeanObject,
    mut v_inst_339_: *mut leanh::LeanObject,
    mut v_inst_340_: *mut leanh::LeanObject,
    mut v_inst_341_: *mut leanh::LeanObject,
    mut v_P_342_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_343_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_343_ = l___private_Std_Data_Iterators_Combinators_Monadic_TakeWhile_0__Std_Iterators_Types_TakeWhile_instFinitenessRelation(v_00_u03b1_336_, v_m_337_, v_00_u03b2_338_, v_inst_339_, v_inst_340_, v_inst_341_, v_P_342_);
    leanh::lean_dec(v_P_342_);
    leanh::lean_dec(v_inst_340_);
    leanh::lean_dec_ref(v_inst_339_);
    return v_res_343_;
}
pub unsafe fn l___private_Std_Data_Iterators_Combinators_Monadic_TakeWhile_0__Std_Iterators_Types_TakeWhile_instProductivenessRelation(
    mut v_00_u03b1_344_: *mut leanh::LeanObject,
    mut v_m_345_: *mut leanh::LeanObject,
    mut v_00_u03b2_346_: *mut leanh::LeanObject,
    mut v_inst_347_: *mut leanh::LeanObject,
    mut v_inst_348_: *mut leanh::LeanObject,
    mut v_inst_349_: *mut leanh::LeanObject,
    mut v_P_350_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_351_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_351_ = leanh::lean_box(0);
    return v___x_351_;
}
pub unsafe fn l___private_Std_Data_Iterators_Combinators_Monadic_TakeWhile_0__Std_Iterators_Types_TakeWhile_instProductivenessRelation___boxed(
    mut v_00_u03b1_352_: *mut leanh::LeanObject,
    mut v_m_353_: *mut leanh::LeanObject,
    mut v_00_u03b2_354_: *mut leanh::LeanObject,
    mut v_inst_355_: *mut leanh::LeanObject,
    mut v_inst_356_: *mut leanh::LeanObject,
    mut v_inst_357_: *mut leanh::LeanObject,
    mut v_P_358_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_359_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_359_ = l___private_Std_Data_Iterators_Combinators_Monadic_TakeWhile_0__Std_Iterators_Types_TakeWhile_instProductivenessRelation(v_00_u03b1_352_, v_m_353_, v_00_u03b2_354_, v_inst_355_, v_inst_356_, v_inst_357_, v_P_358_);
    leanh::lean_dec(v_P_358_);
    leanh::lean_dec(v_inst_356_);
    leanh::lean_dec_ref(v_inst_355_);
    return v_res_359_;
}
pub unsafe fn l_Std_Iterators_Types_TakeWhile_instIteratorLoop___redArg___lam__0(
    mut v_toPure_360_: *mut leanh::LeanObject,
    mut v_recur_361_: *mut leanh::LeanObject,
    mut v_it_362_: *mut leanh::LeanObject,
    mut v_____do__lift_363_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_363_) == 0 {
        let mut v_a_364_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_365_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_it_362_);
        leanh::lean_dec(v_recur_361_);
        v_a_364_ = leanh::lean_ctor_get(v_____do__lift_363_, 0);
        leanh::lean_inc(v_a_364_);
        leanh::lean_dec_ref_known(v_____do__lift_363_, 1);
        v___x_365_ = leanh::lean_apply_2(v_toPure_360_, leanh::lean_box(0), v_a_364_);
        return v___x_365_;
    } else {
        let mut v_a_366_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_367_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_toPure_360_);
        v_a_366_ = leanh::lean_ctor_get(v_____do__lift_363_, 0);
        leanh::lean_inc(v_a_366_);
        leanh::lean_dec_ref_known(v_____do__lift_363_, 1);
        v___x_367_ = leanh::lean_apply_4(
            v_recur_361_,
            v_it_362_,
            v_a_366_,
            leanh::lean_box(0),
            leanh::lean_box(0),
        );
        return v___x_367_;
    }
}
pub unsafe fn l_Std_Iterators_Types_TakeWhile_instIteratorLoop___redArg___lam__1(
    mut v_toPure_368_: *mut leanh::LeanObject,
    mut v_recur_369_: *mut leanh::LeanObject,
    mut v___y_370_: *mut leanh::LeanObject,
    mut v_acc_371_: *mut leanh::LeanObject,
    mut v_toBind_372_: *mut leanh::LeanObject,
    mut v_s_373_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_s_373_) {
        0 => {
            let mut v_it_374_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_375_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_376_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_377_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_378_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_it_374_ = leanh::lean_ctor_get(v_s_373_, 0);
            leanh::lean_inc(v_it_374_);
            v_out_375_ = leanh::lean_ctor_get(v_s_373_, 1);
            leanh::lean_inc(v_out_375_);
            leanh::lean_dec_ref_known(v_s_373_, 2);
            v___f_376_ = leanh::lean_alloc_closure(
                l_Std_Iterators_Types_TakeWhile_instIteratorLoop___redArg___lam__0
                    as *mut core::ffi::c_void,
                4,
                3,
            );
            leanh::lean_closure_set(v___f_376_, 0, v_toPure_368_);
            leanh::lean_closure_set(v___f_376_, 1, v_recur_369_);
            leanh::lean_closure_set(v___f_376_, 2, v_it_374_);
            v___x_377_ = leanh::lean_apply_3(
                v___y_370_,
                v_out_375_,
                leanh::lean_box(0),
                v_acc_371_,
            );
            v___x_378_ = leanh::lean_apply_4(
                v_toBind_372_,
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_377_,
                v___f_376_,
            );
            return v___x_378_;
        }
        1 => {
            let mut v_it_379_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_380_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_toBind_372_);
            leanh::lean_dec(v___y_370_);
            leanh::lean_dec(v_toPure_368_);
            v_it_379_ = leanh::lean_ctor_get(v_s_373_, 0);
            leanh::lean_inc(v_it_379_);
            leanh::lean_dec_ref_known(v_s_373_, 1);
            v___x_380_ = leanh::lean_apply_4(
                v_recur_369_,
                v_it_379_,
                v_acc_371_,
                leanh::lean_box(0),
                leanh::lean_box(0),
            );
            return v___x_380_;
        }
        _ => {
            let mut v___x_381_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_toBind_372_);
            leanh::lean_dec(v___y_370_);
            leanh::lean_dec(v_recur_369_);
            v___x_381_ =
                leanh::lean_apply_2(v_toPure_368_, leanh::lean_box(0), v_acc_371_);
            return v___x_381_;
        }
    }
}
pub unsafe fn l_Std_Iterators_Types_TakeWhile_instIteratorLoop___redArg___lam__4(
    mut v_inst_382_: *mut leanh::LeanObject,
    mut v_toPure_383_: *mut leanh::LeanObject,
    mut v___y_384_: *mut leanh::LeanObject,
    mut v_toBind_385_: *mut leanh::LeanObject,
    mut v_P_386_: *mut leanh::LeanObject,
    mut v_inst_387_: *mut leanh::LeanObject,
    mut v_lift_388_: *mut leanh::LeanObject,
    mut v_it_389_: *mut leanh::LeanObject,
    mut v_acc_390_: *mut leanh::LeanObject,
    mut v_hP_391_: *mut leanh::LeanObject,
    mut v_recur_392_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_400_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_393_ = leanh::lean_ctor_get(v_inst_382_, 0);
    leanh::lean_inc_ref(v_toApplicative_393_);
    v_toBind_394_ = leanh::lean_ctor_get(v_inst_382_, 1);
    leanh::lean_inc_n(v_toBind_394_, 2);
    leanh::lean_dec_ref(v_inst_382_);
    v_toPure_395_ = leanh::lean_ctor_get(v_toApplicative_393_, 1);
    leanh::lean_inc(v_toPure_395_);
    leanh::lean_dec_ref(v_toApplicative_393_);
    v___f_396_ = leanh::lean_alloc_closure(
        l_Std_Iterators_Types_TakeWhile_instIteratorLoop___redArg___lam__1
            as *mut core::ffi::c_void,
        6,
        5,
    );
    leanh::lean_closure_set(v___f_396_, 0, v_toPure_383_);
    leanh::lean_closure_set(v___f_396_, 1, v_recur_392_);
    leanh::lean_closure_set(v___f_396_, 2, v___y_384_);
    leanh::lean_closure_set(v___f_396_, 3, v_acc_390_);
    leanh::lean_closure_set(v___f_396_, 4, v_toBind_385_);
    v___f_397_ = leanh::lean_alloc_closure(
        l_Std_Iterators_Types_TakeWhile_instIterator___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_397_, 0, v_toPure_395_);
    leanh::lean_closure_set(v___f_397_, 1, v_P_386_);
    leanh::lean_closure_set(v___f_397_, 2, v_toBind_394_);
    v___x_398_ = leanh::lean_apply_1(v_inst_387_, v_it_389_);
    v___x_399_ = leanh::lean_apply_4(
        v_toBind_394_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_398_,
        v___f_397_,
    );
    v___x_400_ = leanh::lean_apply_4(
        v_lift_388_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_396_,
        v___x_399_,
    );
    return v___x_400_;
}
pub unsafe fn l_Std_Iterators_Types_TakeWhile_instIteratorLoop___redArg___lam__2(
    mut v_inst_401_: *mut leanh::LeanObject,
    mut v_inst_402_: *mut leanh::LeanObject,
    mut v_P_403_: *mut leanh::LeanObject,
    mut v_inst_404_: *mut leanh::LeanObject,
    mut v_lift_405_: *mut leanh::LeanObject,
    mut v_00_u03b3_406_: *mut leanh::LeanObject,
    mut v_Pl_407_: *mut leanh::LeanObject,
    mut v_it_408_: *mut leanh::LeanObject,
    mut v_init_409_: *mut leanh::LeanObject,
    mut v___y_410_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_415_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_411_ = leanh::lean_ctor_get(v_inst_401_, 0);
    leanh::lean_inc_ref(v_toApplicative_411_);
    v_toBind_412_ = leanh::lean_ctor_get(v_inst_401_, 1);
    leanh::lean_inc(v_toBind_412_);
    leanh::lean_dec_ref(v_inst_401_);
    v_toPure_413_ = leanh::lean_ctor_get(v_toApplicative_411_, 1);
    leanh::lean_inc(v_toPure_413_);
    leanh::lean_dec_ref(v_toApplicative_411_);
    v___f_414_ = leanh::lean_alloc_closure(
        l_Std_Iterators_Types_TakeWhile_instIteratorLoop___redArg___lam__4
            as *mut core::ffi::c_void,
        11,
        7,
    );
    leanh::lean_closure_set(v___f_414_, 0, v_inst_402_);
    leanh::lean_closure_set(v___f_414_, 1, v_toPure_413_);
    leanh::lean_closure_set(v___f_414_, 2, v___y_410_);
    leanh::lean_closure_set(v___f_414_, 3, v_toBind_412_);
    leanh::lean_closure_set(v___f_414_, 4, v_P_403_);
    leanh::lean_closure_set(v___f_414_, 5, v_inst_404_);
    leanh::lean_closure_set(v___f_414_, 6, v_lift_405_);
    v___x_415_ = l_WellFounded_opaqueFix_u2083___redArg(
        v___f_414_,
        v_it_408_,
        v_init_409_,
        leanh::lean_box(0),
    );
    return v___x_415_;
}
pub unsafe fn l_Std_Iterators_Types_TakeWhile_instIteratorLoop___redArg(
    mut v_P_416_: *mut leanh::LeanObject,
    mut v_inst_417_: *mut leanh::LeanObject,
    mut v_inst_418_: *mut leanh::LeanObject,
    mut v_inst_419_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_420_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_420_ = leanh::lean_alloc_closure(
        l_Std_Iterators_Types_TakeWhile_instIteratorLoop___redArg___lam__2
            as *mut core::ffi::c_void,
        10,
        4,
    );
    leanh::lean_closure_set(v___f_420_, 0, v_inst_418_);
    leanh::lean_closure_set(v___f_420_, 1, v_inst_417_);
    leanh::lean_closure_set(v___f_420_, 2, v_P_416_);
    leanh::lean_closure_set(v___f_420_, 3, v_inst_419_);
    return v___f_420_;
}
pub unsafe fn l_Std_Iterators_Types_TakeWhile_instIteratorLoop(
    mut v_00_u03b1_421_: *mut leanh::LeanObject,
    mut v_m_422_: *mut leanh::LeanObject,
    mut v_00_u03b2_423_: *mut leanh::LeanObject,
    mut v_n_424_: *mut leanh::LeanObject,
    mut v_P_425_: *mut leanh::LeanObject,
    mut v_inst_426_: *mut leanh::LeanObject,
    mut v_inst_427_: *mut leanh::LeanObject,
    mut v_inst_428_: *mut leanh::LeanObject,
    mut v_inst_429_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_430_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_430_ = leanh::lean_alloc_closure(
        l_Std_Iterators_Types_TakeWhile_instIteratorLoop___redArg___lam__2
            as *mut core::ffi::c_void,
        10,
        4,
    );
    leanh::lean_closure_set(v___f_430_, 0, v_inst_427_);
    leanh::lean_closure_set(v___f_430_, 1, v_inst_426_);
    leanh::lean_closure_set(v___f_430_, 2, v_P_425_);
    leanh::lean_closure_set(v___f_430_, 3, v_inst_428_);
    return v___f_430_;
}
pub unsafe fn l_Std_Iterators_Types_TakeWhile_instIteratorLoop___boxed(
    mut v_00_u03b1_431_: *mut leanh::LeanObject,
    mut v_m_432_: *mut leanh::LeanObject,
    mut v_00_u03b2_433_: *mut leanh::LeanObject,
    mut v_n_434_: *mut leanh::LeanObject,
    mut v_P_435_: *mut leanh::LeanObject,
    mut v_inst_436_: *mut leanh::LeanObject,
    mut v_inst_437_: *mut leanh::LeanObject,
    mut v_inst_438_: *mut leanh::LeanObject,
    mut v_inst_439_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_440_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_440_ = l_Std_Iterators_Types_TakeWhile_instIteratorLoop(
        v_00_u03b1_431_,
        v_m_432_,
        v_00_u03b2_433_,
        v_n_434_,
        v_P_435_,
        v_inst_436_,
        v_inst_437_,
        v_inst_438_,
        v_inst_439_,
    );
    leanh::lean_dec(v_inst_439_);
    return v_res_440_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_Iterators_Combinators_Monadic_TakeWhile(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
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
    res = runtime_initialize_Init_Data_Iterators_PostconditionMonad(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_Iterators_Combinators_Monadic_TakeWhile(
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
pub unsafe fn initialize_Std_Data_Iterators_Combinators_Monadic_TakeWhile(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Nat_Lemmas(builtin);
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
    res = initialize_Init_Data_Iterators_PostconditionMonad(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Combinators_Monadic_TakeWhile(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_Iterators_Combinators_Monadic_TakeWhile(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Data_Iterators_Combinators_Monadic_TakeWhile(builtin);
}