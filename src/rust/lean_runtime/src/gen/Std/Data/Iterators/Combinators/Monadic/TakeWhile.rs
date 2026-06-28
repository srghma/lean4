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
    mut v_it_221_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_it_221_);
    return v_it_221_;
}
pub unsafe fn l_Std_IterM_takeWhileWithPostcondition___redArg___boxed(
    mut v_it_222_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_223_ = l_Std_IterM_takeWhileWithPostcondition___redArg(v_it_222_);
    crate::leanh::lean_dec(v_it_222_);
    return v_res_223_;
}
pub unsafe fn l_Std_IterM_takeWhileWithPostcondition(
    mut v_00_u03b1_224_: *mut crate::leanh::LeanObject,
    mut v_m_225_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_226_: *mut crate::leanh::LeanObject,
    mut v_P_227_: *mut crate::leanh::LeanObject,
    mut v_it_228_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_it_228_);
    return v_it_228_;
}
pub unsafe fn l_Std_IterM_takeWhileWithPostcondition___boxed(
    mut v_00_u03b1_229_: *mut crate::leanh::LeanObject,
    mut v_m_230_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_231_: *mut crate::leanh::LeanObject,
    mut v_P_232_: *mut crate::leanh::LeanObject,
    mut v_it_233_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_234_ = l_Std_IterM_takeWhileWithPostcondition(
        v_00_u03b1_229_,
        v_m_230_,
        v_00_u03b2_231_,
        v_P_232_,
        v_it_233_,
    );
    crate::leanh::lean_dec(v_it_233_);
    crate::leanh::lean_dec(v_P_232_);
    return v_res_234_;
}
pub unsafe fn l_Std_IterM_takeWhileM___redArg(
    mut v_it_235_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_it_235_);
    return v_it_235_;
}
pub unsafe fn l_Std_IterM_takeWhileM___redArg___boxed(
    mut v_it_236_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_237_ = l_Std_IterM_takeWhileM___redArg(v_it_236_);
    crate::leanh::lean_dec(v_it_236_);
    return v_res_237_;
}
pub unsafe fn l_Std_IterM_takeWhileM(
    mut v_00_u03b1_238_: *mut crate::leanh::LeanObject,
    mut v_m_239_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_240_: *mut crate::leanh::LeanObject,
    mut v_inst_241_: *mut crate::leanh::LeanObject,
    mut v_inst_242_: *mut crate::leanh::LeanObject,
    mut v_P_243_: *mut crate::leanh::LeanObject,
    mut v_it_244_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_it_244_);
    return v_it_244_;
}
pub unsafe fn l_Std_IterM_takeWhileM___boxed(
    mut v_00_u03b1_245_: *mut crate::leanh::LeanObject,
    mut v_m_246_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_247_: *mut crate::leanh::LeanObject,
    mut v_inst_248_: *mut crate::leanh::LeanObject,
    mut v_inst_249_: *mut crate::leanh::LeanObject,
    mut v_P_250_: *mut crate::leanh::LeanObject,
    mut v_it_251_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_252_ = l_Std_IterM_takeWhileM(
        v_00_u03b1_245_,
        v_m_246_,
        v_00_u03b2_247_,
        v_inst_248_,
        v_inst_249_,
        v_P_250_,
        v_it_251_,
    );
    crate::leanh::lean_dec(v_it_251_);
    crate::leanh::lean_dec(v_P_250_);
    crate::leanh::lean_dec(v_inst_249_);
    crate::leanh::lean_dec_ref(v_inst_248_);
    return v_res_252_;
}
pub unsafe fn l_Std_IterM_takeWhile___redArg(
    mut v_it_253_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_it_253_);
    return v_it_253_;
}
pub unsafe fn l_Std_IterM_takeWhile___redArg___boxed(
    mut v_it_254_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_255_ = l_Std_IterM_takeWhile___redArg(v_it_254_);
    crate::leanh::lean_dec(v_it_254_);
    return v_res_255_;
}
pub unsafe fn l_Std_IterM_takeWhile(
    mut v_00_u03b1_256_: *mut crate::leanh::LeanObject,
    mut v_m_257_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_258_: *mut crate::leanh::LeanObject,
    mut v_inst_259_: *mut crate::leanh::LeanObject,
    mut v_P_260_: *mut crate::leanh::LeanObject,
    mut v_it_261_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_it_261_);
    return v_it_261_;
}
pub unsafe fn l_Std_IterM_takeWhile___boxed(
    mut v_00_u03b1_262_: *mut crate::leanh::LeanObject,
    mut v_m_263_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_264_: *mut crate::leanh::LeanObject,
    mut v_inst_265_: *mut crate::leanh::LeanObject,
    mut v_P_266_: *mut crate::leanh::LeanObject,
    mut v_it_267_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_268_ = l_Std_IterM_takeWhile(
        v_00_u03b1_262_,
        v_m_263_,
        v_00_u03b2_264_,
        v_inst_265_,
        v_P_266_,
        v_it_267_,
    );
    crate::leanh::lean_dec(v_it_267_);
    crate::leanh::lean_dec_ref(v_P_266_);
    crate::leanh::lean_dec_ref(v_inst_265_);
    return v_res_268_;
}
pub unsafe fn l_Std_Iterators_Types_TakeWhile_instIterator___redArg___lam__0(
    mut v_toPure_269_: *mut crate::leanh::LeanObject,
    mut v_it_270_: *mut crate::leanh::LeanObject,
    mut v_out_271_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_272_: u8,
) -> *mut crate::leanh::LeanObject {
    if v_____do__lift_272_ == 0 {
        let mut v___x_273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_out_271_);
        crate::leanh::lean_dec(v_it_270_);
        v___x_273_ = crate::leanh::lean_box(2);
        v___x_274_ =
            crate::leanh::lean_apply_2(v_toPure_269_, crate::leanh::lean_box(0), v___x_273_);
        return v___x_274_;
    } else {
        let mut v___x_275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_275_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_275_, 0, v_it_270_);
        crate::leanh::lean_ctor_set(v___x_275_, 1, v_out_271_);
        v___x_276_ =
            crate::leanh::lean_apply_2(v_toPure_269_, crate::leanh::lean_box(0), v___x_275_);
        return v___x_276_;
    }
}
pub unsafe fn l_Std_Iterators_Types_TakeWhile_instIterator___redArg___lam__0___boxed(
    mut v_toPure_277_: *mut crate::leanh::LeanObject,
    mut v_it_278_: *mut crate::leanh::LeanObject,
    mut v_out_279_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_280_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_____do__lift_267__boxed_281_: u8 = 0;
    let mut v_res_282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_267__boxed_281_ = (crate::leanh::lean_unbox(v_____do__lift_280_) as u8);
    v_res_282_ = l_Std_Iterators_Types_TakeWhile_instIterator___redArg___lam__0(
        v_toPure_277_,
        v_it_278_,
        v_out_279_,
        v_____do__lift_267__boxed_281_,
    );
    return v_res_282_;
}
pub unsafe fn l_Std_Iterators_Types_TakeWhile_instIterator___redArg___lam__1(
    mut v_toPure_283_: *mut crate::leanh::LeanObject,
    mut v_P_284_: *mut crate::leanh::LeanObject,
    mut v_toBind_285_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_286_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_it_287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_295_: u8 = 0;
    let mut v___x_297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_300_: u8 = 0;
    let mut v___x_301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_____do__lift_286_) {
                0 => {
                    v_it_287_ = crate::leanh::lean_ctor_get(v_____do__lift_286_, 0);
                    crate::leanh::lean_inc(v_it_287_);
                    v_out_288_ = crate::leanh::lean_ctor_get(v_____do__lift_286_, 1);
                    crate::leanh::lean_inc_n(v_out_288_, 2);
                    crate::leanh::lean_dec_ref_known(v_____do__lift_286_, 2);
                    v___f_289_ = crate::leanh::lean_alloc_closure(
                        l_Std_Iterators_Types_TakeWhile_instIterator___redArg___lam__0___boxed
                            as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    crate::leanh::lean_closure_set(v___f_289_, 0, v_toPure_283_);
                    crate::leanh::lean_closure_set(v___f_289_, 1, v_it_287_);
                    crate::leanh::lean_closure_set(v___f_289_, 2, v_out_288_);
                    v___x_290_ = crate::leanh::lean_apply_1(v_P_284_, v_out_288_);
                    v___x_291_ = crate::leanh::lean_apply_4(
                        v_toBind_285_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___x_290_,
                        v___f_289_,
                    );
                    return v___x_291_;
                }
                1 => {
                    crate::leanh::lean_dec(v_toBind_285_);
                    crate::leanh::lean_dec(v_P_284_);
                    v_it_292_ = crate::leanh::lean_ctor_get(v_____do__lift_286_, 0);
                    v_isSharedCheck_300_ =
                        (!crate::leanh::lean_is_exclusive(v_____do__lift_286_)) as u8;
                    if v_isSharedCheck_300_ == 0 {
                        v___x_294_ = v_____do__lift_286_;
                        v_isShared_295_ = v_isSharedCheck_300_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_it_292_);
                        crate::leanh::lean_dec(v_____do__lift_286_);
                        v___x_294_ = crate::leanh::lean_box(0);
                        v_isShared_295_ = v_isSharedCheck_300_;
                        state = 1;
                        continue;
                    }
                }
                _ => {
                    crate::leanh::lean_dec(v_toBind_285_);
                    crate::leanh::lean_dec(v_P_284_);
                    v___x_301_ = crate::leanh::lean_box(2);
                    v___x_302_ = crate::leanh::lean_apply_2(
                        v_toPure_283_,
                        crate::leanh::lean_box(0),
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
                    v_reuseFailAlloc_299_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_299_, 0, v_it_292_);
                    v___x_297_ = v_reuseFailAlloc_299_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_298_ = crate::leanh::lean_apply_2(
                    v_toPure_283_,
                    crate::leanh::lean_box(0),
                    v___x_297_,
                );
                return v___x_298_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Iterators_Types_TakeWhile_instIterator___redArg___lam__2(
    mut v_inst_303_: *mut crate::leanh::LeanObject,
    mut v_toBind_304_: *mut crate::leanh::LeanObject,
    mut v___f_305_: *mut crate::leanh::LeanObject,
    mut v_it_306_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_307_ = crate::leanh::lean_apply_1(v_inst_303_, v_it_306_);
    v___x_308_ = crate::leanh::lean_apply_4(
        v_toBind_304_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_307_,
        v___f_305_,
    );
    return v___x_308_;
}
pub unsafe fn l_Std_Iterators_Types_TakeWhile_instIterator___redArg(
    mut v_inst_309_: *mut crate::leanh::LeanObject,
    mut v_inst_310_: *mut crate::leanh::LeanObject,
    mut v_P_311_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_312_ = crate::leanh::lean_ctor_get(v_inst_309_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_312_);
    v_toBind_313_ = crate::leanh::lean_ctor_get(v_inst_309_, 1);
    crate::leanh::lean_inc_n(v_toBind_313_, 2);
    crate::leanh::lean_dec_ref(v_inst_309_);
    v_toPure_314_ = crate::leanh::lean_ctor_get(v_toApplicative_312_, 1);
    crate::leanh::lean_inc(v_toPure_314_);
    crate::leanh::lean_dec_ref(v_toApplicative_312_);
    v___f_315_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_Types_TakeWhile_instIterator___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_315_, 0, v_toPure_314_);
    crate::leanh::lean_closure_set(v___f_315_, 1, v_P_311_);
    crate::leanh::lean_closure_set(v___f_315_, 2, v_toBind_313_);
    v___f_316_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_Types_TakeWhile_instIterator___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_316_, 0, v_inst_310_);
    crate::leanh::lean_closure_set(v___f_316_, 1, v_toBind_313_);
    crate::leanh::lean_closure_set(v___f_316_, 2, v___f_315_);
    return v___f_316_;
}
pub unsafe fn l_Std_Iterators_Types_TakeWhile_instIterator(
    mut v_00_u03b1_317_: *mut crate::leanh::LeanObject,
    mut v_m_318_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_319_: *mut crate::leanh::LeanObject,
    mut v_inst_320_: *mut crate::leanh::LeanObject,
    mut v_inst_321_: *mut crate::leanh::LeanObject,
    mut v_P_322_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_323_ = crate::leanh::lean_ctor_get(v_inst_320_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_323_);
    v_toBind_324_ = crate::leanh::lean_ctor_get(v_inst_320_, 1);
    crate::leanh::lean_inc_n(v_toBind_324_, 2);
    crate::leanh::lean_dec_ref(v_inst_320_);
    v_toPure_325_ = crate::leanh::lean_ctor_get(v_toApplicative_323_, 1);
    crate::leanh::lean_inc(v_toPure_325_);
    crate::leanh::lean_dec_ref(v_toApplicative_323_);
    v___f_326_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_Types_TakeWhile_instIterator___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_326_, 0, v_toPure_325_);
    crate::leanh::lean_closure_set(v___f_326_, 1, v_P_322_);
    crate::leanh::lean_closure_set(v___f_326_, 2, v_toBind_324_);
    v___f_327_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_Types_TakeWhile_instIterator___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_327_, 0, v_inst_321_);
    crate::leanh::lean_closure_set(v___f_327_, 1, v_toBind_324_);
    crate::leanh::lean_closure_set(v___f_327_, 2, v___f_326_);
    return v___f_327_;
}
pub unsafe fn l___private_Std_Data_Iterators_Combinators_Monadic_TakeWhile_0__Std_Iterators_Types_TakeWhile_instFinitenessRelation(
    mut v_00_u03b1_328_: *mut crate::leanh::LeanObject,
    mut v_m_329_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_330_: *mut crate::leanh::LeanObject,
    mut v_inst_331_: *mut crate::leanh::LeanObject,
    mut v_inst_332_: *mut crate::leanh::LeanObject,
    mut v_inst_333_: *mut crate::leanh::LeanObject,
    mut v_P_334_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_335_ = crate::leanh::lean_box(0);
    return v___x_335_;
}
pub unsafe fn l___private_Std_Data_Iterators_Combinators_Monadic_TakeWhile_0__Std_Iterators_Types_TakeWhile_instFinitenessRelation___boxed(
    mut v_00_u03b1_336_: *mut crate::leanh::LeanObject,
    mut v_m_337_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_338_: *mut crate::leanh::LeanObject,
    mut v_inst_339_: *mut crate::leanh::LeanObject,
    mut v_inst_340_: *mut crate::leanh::LeanObject,
    mut v_inst_341_: *mut crate::leanh::LeanObject,
    mut v_P_342_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_343_ = l___private_Std_Data_Iterators_Combinators_Monadic_TakeWhile_0__Std_Iterators_Types_TakeWhile_instFinitenessRelation(v_00_u03b1_336_, v_m_337_, v_00_u03b2_338_, v_inst_339_, v_inst_340_, v_inst_341_, v_P_342_);
    crate::leanh::lean_dec(v_P_342_);
    crate::leanh::lean_dec(v_inst_340_);
    crate::leanh::lean_dec_ref(v_inst_339_);
    return v_res_343_;
}
pub unsafe fn l___private_Std_Data_Iterators_Combinators_Monadic_TakeWhile_0__Std_Iterators_Types_TakeWhile_instProductivenessRelation(
    mut v_00_u03b1_344_: *mut crate::leanh::LeanObject,
    mut v_m_345_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_346_: *mut crate::leanh::LeanObject,
    mut v_inst_347_: *mut crate::leanh::LeanObject,
    mut v_inst_348_: *mut crate::leanh::LeanObject,
    mut v_inst_349_: *mut crate::leanh::LeanObject,
    mut v_P_350_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_351_ = crate::leanh::lean_box(0);
    return v___x_351_;
}
pub unsafe fn l___private_Std_Data_Iterators_Combinators_Monadic_TakeWhile_0__Std_Iterators_Types_TakeWhile_instProductivenessRelation___boxed(
    mut v_00_u03b1_352_: *mut crate::leanh::LeanObject,
    mut v_m_353_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_354_: *mut crate::leanh::LeanObject,
    mut v_inst_355_: *mut crate::leanh::LeanObject,
    mut v_inst_356_: *mut crate::leanh::LeanObject,
    mut v_inst_357_: *mut crate::leanh::LeanObject,
    mut v_P_358_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_359_ = l___private_Std_Data_Iterators_Combinators_Monadic_TakeWhile_0__Std_Iterators_Types_TakeWhile_instProductivenessRelation(v_00_u03b1_352_, v_m_353_, v_00_u03b2_354_, v_inst_355_, v_inst_356_, v_inst_357_, v_P_358_);
    crate::leanh::lean_dec(v_P_358_);
    crate::leanh::lean_dec(v_inst_356_);
    crate::leanh::lean_dec_ref(v_inst_355_);
    return v_res_359_;
}
pub unsafe fn l_Std_Iterators_Types_TakeWhile_instIteratorLoop___redArg___lam__0(
    mut v_toPure_360_: *mut crate::leanh::LeanObject,
    mut v_recur_361_: *mut crate::leanh::LeanObject,
    mut v_it_362_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_363_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_363_) == 0 {
        let mut v_a_364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_it_362_);
        crate::leanh::lean_dec(v_recur_361_);
        v_a_364_ = crate::leanh::lean_ctor_get(v_____do__lift_363_, 0);
        crate::leanh::lean_inc(v_a_364_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_363_, 1);
        v___x_365_ = crate::leanh::lean_apply_2(v_toPure_360_, crate::leanh::lean_box(0), v_a_364_);
        return v___x_365_;
    } else {
        let mut v_a_366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_360_);
        v_a_366_ = crate::leanh::lean_ctor_get(v_____do__lift_363_, 0);
        crate::leanh::lean_inc(v_a_366_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_363_, 1);
        v___x_367_ = crate::leanh::lean_apply_4(
            v_recur_361_,
            v_it_362_,
            v_a_366_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_367_;
    }
}
pub unsafe fn l_Std_Iterators_Types_TakeWhile_instIteratorLoop___redArg___lam__1(
    mut v_toPure_368_: *mut crate::leanh::LeanObject,
    mut v_recur_369_: *mut crate::leanh::LeanObject,
    mut v___y_370_: *mut crate::leanh::LeanObject,
    mut v_acc_371_: *mut crate::leanh::LeanObject,
    mut v_toBind_372_: *mut crate::leanh::LeanObject,
    mut v_s_373_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_s_373_) {
        0 => {
            let mut v_it_374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_it_374_ = crate::leanh::lean_ctor_get(v_s_373_, 0);
            crate::leanh::lean_inc(v_it_374_);
            v_out_375_ = crate::leanh::lean_ctor_get(v_s_373_, 1);
            crate::leanh::lean_inc(v_out_375_);
            crate::leanh::lean_dec_ref_known(v_s_373_, 2);
            v___f_376_ = crate::leanh::lean_alloc_closure(
                l_Std_Iterators_Types_TakeWhile_instIteratorLoop___redArg___lam__0
                    as *mut core::ffi::c_void,
                4,
                3,
            );
            crate::leanh::lean_closure_set(v___f_376_, 0, v_toPure_368_);
            crate::leanh::lean_closure_set(v___f_376_, 1, v_recur_369_);
            crate::leanh::lean_closure_set(v___f_376_, 2, v_it_374_);
            v___x_377_ = crate::leanh::lean_apply_3(
                v___y_370_,
                v_out_375_,
                crate::leanh::lean_box(0),
                v_acc_371_,
            );
            v___x_378_ = crate::leanh::lean_apply_4(
                v_toBind_372_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_377_,
                v___f_376_,
            );
            return v___x_378_;
        }
        1 => {
            let mut v_it_379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_toBind_372_);
            crate::leanh::lean_dec(v___y_370_);
            crate::leanh::lean_dec(v_toPure_368_);
            v_it_379_ = crate::leanh::lean_ctor_get(v_s_373_, 0);
            crate::leanh::lean_inc(v_it_379_);
            crate::leanh::lean_dec_ref_known(v_s_373_, 1);
            v___x_380_ = crate::leanh::lean_apply_4(
                v_recur_369_,
                v_it_379_,
                v_acc_371_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_380_;
        }
        _ => {
            let mut v___x_381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_toBind_372_);
            crate::leanh::lean_dec(v___y_370_);
            crate::leanh::lean_dec(v_recur_369_);
            v___x_381_ =
                crate::leanh::lean_apply_2(v_toPure_368_, crate::leanh::lean_box(0), v_acc_371_);
            return v___x_381_;
        }
    }
}
pub unsafe fn l_Std_Iterators_Types_TakeWhile_instIteratorLoop___redArg___lam__4(
    mut v_inst_382_: *mut crate::leanh::LeanObject,
    mut v_toPure_383_: *mut crate::leanh::LeanObject,
    mut v___y_384_: *mut crate::leanh::LeanObject,
    mut v_toBind_385_: *mut crate::leanh::LeanObject,
    mut v_P_386_: *mut crate::leanh::LeanObject,
    mut v_inst_387_: *mut crate::leanh::LeanObject,
    mut v_lift_388_: *mut crate::leanh::LeanObject,
    mut v_it_389_: *mut crate::leanh::LeanObject,
    mut v_acc_390_: *mut crate::leanh::LeanObject,
    mut v_hP_391_: *mut crate::leanh::LeanObject,
    mut v_recur_392_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_393_ = crate::leanh::lean_ctor_get(v_inst_382_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_393_);
    v_toBind_394_ = crate::leanh::lean_ctor_get(v_inst_382_, 1);
    crate::leanh::lean_inc_n(v_toBind_394_, 2);
    crate::leanh::lean_dec_ref(v_inst_382_);
    v_toPure_395_ = crate::leanh::lean_ctor_get(v_toApplicative_393_, 1);
    crate::leanh::lean_inc(v_toPure_395_);
    crate::leanh::lean_dec_ref(v_toApplicative_393_);
    v___f_396_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_Types_TakeWhile_instIteratorLoop___redArg___lam__1
            as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___f_396_, 0, v_toPure_383_);
    crate::leanh::lean_closure_set(v___f_396_, 1, v_recur_392_);
    crate::leanh::lean_closure_set(v___f_396_, 2, v___y_384_);
    crate::leanh::lean_closure_set(v___f_396_, 3, v_acc_390_);
    crate::leanh::lean_closure_set(v___f_396_, 4, v_toBind_385_);
    v___f_397_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_Types_TakeWhile_instIterator___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_397_, 0, v_toPure_395_);
    crate::leanh::lean_closure_set(v___f_397_, 1, v_P_386_);
    crate::leanh::lean_closure_set(v___f_397_, 2, v_toBind_394_);
    v___x_398_ = crate::leanh::lean_apply_1(v_inst_387_, v_it_389_);
    v___x_399_ = crate::leanh::lean_apply_4(
        v_toBind_394_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_398_,
        v___f_397_,
    );
    v___x_400_ = crate::leanh::lean_apply_4(
        v_lift_388_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_396_,
        v___x_399_,
    );
    return v___x_400_;
}
pub unsafe fn l_Std_Iterators_Types_TakeWhile_instIteratorLoop___redArg___lam__2(
    mut v_inst_401_: *mut crate::leanh::LeanObject,
    mut v_inst_402_: *mut crate::leanh::LeanObject,
    mut v_P_403_: *mut crate::leanh::LeanObject,
    mut v_inst_404_: *mut crate::leanh::LeanObject,
    mut v_lift_405_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_406_: *mut crate::leanh::LeanObject,
    mut v_Pl_407_: *mut crate::leanh::LeanObject,
    mut v_it_408_: *mut crate::leanh::LeanObject,
    mut v_init_409_: *mut crate::leanh::LeanObject,
    mut v___y_410_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_411_ = crate::leanh::lean_ctor_get(v_inst_401_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_411_);
    v_toBind_412_ = crate::leanh::lean_ctor_get(v_inst_401_, 1);
    crate::leanh::lean_inc(v_toBind_412_);
    crate::leanh::lean_dec_ref(v_inst_401_);
    v_toPure_413_ = crate::leanh::lean_ctor_get(v_toApplicative_411_, 1);
    crate::leanh::lean_inc(v_toPure_413_);
    crate::leanh::lean_dec_ref(v_toApplicative_411_);
    v___f_414_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_Types_TakeWhile_instIteratorLoop___redArg___lam__4
            as *mut core::ffi::c_void,
        11,
        7,
    );
    crate::leanh::lean_closure_set(v___f_414_, 0, v_inst_402_);
    crate::leanh::lean_closure_set(v___f_414_, 1, v_toPure_413_);
    crate::leanh::lean_closure_set(v___f_414_, 2, v___y_410_);
    crate::leanh::lean_closure_set(v___f_414_, 3, v_toBind_412_);
    crate::leanh::lean_closure_set(v___f_414_, 4, v_P_403_);
    crate::leanh::lean_closure_set(v___f_414_, 5, v_inst_404_);
    crate::leanh::lean_closure_set(v___f_414_, 6, v_lift_405_);
    v___x_415_ = l_WellFounded_opaqueFix_u2083___redArg(
        v___f_414_,
        v_it_408_,
        v_init_409_,
        crate::leanh::lean_box(0),
    );
    return v___x_415_;
}
pub unsafe fn l_Std_Iterators_Types_TakeWhile_instIteratorLoop___redArg(
    mut v_P_416_: *mut crate::leanh::LeanObject,
    mut v_inst_417_: *mut crate::leanh::LeanObject,
    mut v_inst_418_: *mut crate::leanh::LeanObject,
    mut v_inst_419_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_420_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_Types_TakeWhile_instIteratorLoop___redArg___lam__2
            as *mut core::ffi::c_void,
        10,
        4,
    );
    crate::leanh::lean_closure_set(v___f_420_, 0, v_inst_418_);
    crate::leanh::lean_closure_set(v___f_420_, 1, v_inst_417_);
    crate::leanh::lean_closure_set(v___f_420_, 2, v_P_416_);
    crate::leanh::lean_closure_set(v___f_420_, 3, v_inst_419_);
    return v___f_420_;
}
pub unsafe fn l_Std_Iterators_Types_TakeWhile_instIteratorLoop(
    mut v_00_u03b1_421_: *mut crate::leanh::LeanObject,
    mut v_m_422_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_423_: *mut crate::leanh::LeanObject,
    mut v_n_424_: *mut crate::leanh::LeanObject,
    mut v_P_425_: *mut crate::leanh::LeanObject,
    mut v_inst_426_: *mut crate::leanh::LeanObject,
    mut v_inst_427_: *mut crate::leanh::LeanObject,
    mut v_inst_428_: *mut crate::leanh::LeanObject,
    mut v_inst_429_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_430_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_Types_TakeWhile_instIteratorLoop___redArg___lam__2
            as *mut core::ffi::c_void,
        10,
        4,
    );
    crate::leanh::lean_closure_set(v___f_430_, 0, v_inst_427_);
    crate::leanh::lean_closure_set(v___f_430_, 1, v_inst_426_);
    crate::leanh::lean_closure_set(v___f_430_, 2, v_P_425_);
    crate::leanh::lean_closure_set(v___f_430_, 3, v_inst_428_);
    return v___f_430_;
}
pub unsafe fn l_Std_Iterators_Types_TakeWhile_instIteratorLoop___boxed(
    mut v_00_u03b1_431_: *mut crate::leanh::LeanObject,
    mut v_m_432_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_433_: *mut crate::leanh::LeanObject,
    mut v_n_434_: *mut crate::leanh::LeanObject,
    mut v_P_435_: *mut crate::leanh::LeanObject,
    mut v_inst_436_: *mut crate::leanh::LeanObject,
    mut v_inst_437_: *mut crate::leanh::LeanObject,
    mut v_inst_438_: *mut crate::leanh::LeanObject,
    mut v_inst_439_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_inst_439_);
    return v_res_440_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_Iterators_Combinators_Monadic_TakeWhile(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
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
    res = runtime_initialize_Init_Data_Iterators_PostconditionMonad(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_Iterators_Combinators_Monadic_TakeWhile(
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
pub unsafe fn initialize_Std_Data_Iterators_Combinators_Monadic_TakeWhile(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Nat_Lemmas(builtin);
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
    res = initialize_Init_Data_Iterators_PostconditionMonad(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Combinators_Monadic_TakeWhile(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_Iterators_Combinators_Monadic_TakeWhile(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Data_Iterators_Combinators_Monadic_TakeWhile(builtin);
}
