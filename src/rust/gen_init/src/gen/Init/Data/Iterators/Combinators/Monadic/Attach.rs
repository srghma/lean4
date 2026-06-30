// Lean compiler output
// Module: Init.Data.Iterators.Combinators.Monadic.Attach
// Imports: Init.Data.Iterators.Consumers.Monadic.Loop
use crate::r#gen::Init::Data::Iterators::Consumers::Monadic::Loop::{
    initialize_Init_Data_Iterators_Consumers_Monadic_Loop,
    runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop,
};
use crate::r#gen::Init::WFExtrinsicFix::l_WellFounded_opaqueFix_u2083___redArg;
pub static l_Std_Iterators_Types_Attach_instIterator___redArg___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Iterators_Types_Attach_instIterator___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Iterators_Types_Attach_instIterator___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Iterators_Types_Attach_instIterator___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Std_Iterators_Types_Attach_Monadic_modifyStep___redArg(
    mut v_step_253_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_it_254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_258_: u8 = 0;
    let mut v___x_260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_262_: u8 = 0;
    let mut v_it_263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_266_: u8 = 0;
    let mut v___x_268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_270_: u8 = 0;
    let mut v___x_271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_step_253_) {
                0 => {
                    v_it_254_ = leanh::lean_ctor_get(v_step_253_, 0);
                    v_out_255_ = leanh::lean_ctor_get(v_step_253_, 1);
                    v_isSharedCheck_262_ = (!leanh::lean_is_exclusive(v_step_253_)) as u8;
                    if v_isSharedCheck_262_ == 0 {
                        v___x_257_ = v_step_253_;
                        v_isShared_258_ = v_isSharedCheck_262_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_out_255_);
                        leanh::lean_inc(v_it_254_);
                        leanh::lean_dec(v_step_253_);
                        v___x_257_ = leanh::lean_box(0);
                        v_isShared_258_ = v_isSharedCheck_262_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_it_263_ = leanh::lean_ctor_get(v_step_253_, 0);
                    v_isSharedCheck_270_ = (!leanh::lean_is_exclusive(v_step_253_)) as u8;
                    if v_isSharedCheck_270_ == 0 {
                        v___x_265_ = v_step_253_;
                        v_isShared_266_ = v_isSharedCheck_270_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_it_263_);
                        leanh::lean_dec(v_step_253_);
                        v___x_265_ = leanh::lean_box(0);
                        v_isShared_266_ = v_isSharedCheck_270_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    v___x_271_ = leanh::lean_box(2);
                    return v___x_271_;
                }
            },
            1 => {
                if v_isShared_258_ == 0 {
                    v___x_260_ = v___x_257_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_261_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_261_, 0, v_it_254_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_261_, 1, v_out_255_);
                    v___x_260_ = v_reuseFailAlloc_261_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_260_;
            }
            3 => {
                if v_isShared_266_ == 0 {
                    v___x_268_ = v___x_265_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_269_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_269_, 0, v_it_263_);
                    v___x_268_ = v_reuseFailAlloc_269_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_268_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Iterators_Types_Attach_Monadic_modifyStep(
    mut v_00_u03b1_272_: *mut leanh::LeanObject,
    mut v_m_273_: *mut leanh::LeanObject,
    mut v_00_u03b2_274_: *mut leanh::LeanObject,
    mut v_inst_275_: *mut leanh::LeanObject,
    mut v_P_276_: *mut leanh::LeanObject,
    mut v_it_277_: *mut leanh::LeanObject,
    mut v_step_278_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_it_279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_283_: u8 = 0;
    let mut v___x_285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_287_: u8 = 0;
    let mut v_it_288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_291_: u8 = 0;
    let mut v___x_293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_295_: u8 = 0;
    let mut v___x_296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_step_278_) {
                0 => {
                    v_it_279_ = leanh::lean_ctor_get(v_step_278_, 0);
                    v_out_280_ = leanh::lean_ctor_get(v_step_278_, 1);
                    v_isSharedCheck_287_ = (!leanh::lean_is_exclusive(v_step_278_)) as u8;
                    if v_isSharedCheck_287_ == 0 {
                        v___x_282_ = v_step_278_;
                        v_isShared_283_ = v_isSharedCheck_287_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_out_280_);
                        leanh::lean_inc(v_it_279_);
                        leanh::lean_dec(v_step_278_);
                        v___x_282_ = leanh::lean_box(0);
                        v_isShared_283_ = v_isSharedCheck_287_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_it_288_ = leanh::lean_ctor_get(v_step_278_, 0);
                    v_isSharedCheck_295_ = (!leanh::lean_is_exclusive(v_step_278_)) as u8;
                    if v_isSharedCheck_295_ == 0 {
                        v___x_290_ = v_step_278_;
                        v_isShared_291_ = v_isSharedCheck_295_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_it_288_);
                        leanh::lean_dec(v_step_278_);
                        v___x_290_ = leanh::lean_box(0);
                        v_isShared_291_ = v_isSharedCheck_295_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    v___x_296_ = leanh::lean_box(2);
                    return v___x_296_;
                }
            },
            1 => {
                if v_isShared_283_ == 0 {
                    v___x_285_ = v___x_282_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_286_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_286_, 0, v_it_279_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_286_, 1, v_out_280_);
                    v___x_285_ = v_reuseFailAlloc_286_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_285_;
            }
            3 => {
                if v_isShared_291_ == 0 {
                    v___x_293_ = v___x_290_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_294_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_294_, 0, v_it_288_);
                    v___x_293_ = v_reuseFailAlloc_294_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_293_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Iterators_Types_Attach_Monadic_modifyStep___boxed(
    mut v_00_u03b1_297_: *mut leanh::LeanObject,
    mut v_m_298_: *mut leanh::LeanObject,
    mut v_00_u03b2_299_: *mut leanh::LeanObject,
    mut v_inst_300_: *mut leanh::LeanObject,
    mut v_P_301_: *mut leanh::LeanObject,
    mut v_it_302_: *mut leanh::LeanObject,
    mut v_step_303_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_304_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_304_ = l_Std_Iterators_Types_Attach_Monadic_modifyStep(
        v_00_u03b1_297_,
        v_m_298_,
        v_00_u03b2_299_,
        v_inst_300_,
        v_P_301_,
        v_it_302_,
        v_step_303_,
    );
    leanh::lean_dec(v_it_302_);
    leanh::lean_dec(v_inst_300_);
    return v_res_304_;
}
pub unsafe fn l_Std_Iterators_Types_Attach_instIterator___redArg___lam__0(
    mut v_step_305_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_it_306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_310_: u8 = 0;
    let mut v___x_312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_314_: u8 = 0;
    let mut v_it_315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_318_: u8 = 0;
    let mut v___x_320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_322_: u8 = 0;
    let mut v___x_323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_step_305_) {
                0 => {
                    v_it_306_ = leanh::lean_ctor_get(v_step_305_, 0);
                    v_out_307_ = leanh::lean_ctor_get(v_step_305_, 1);
                    v_isSharedCheck_314_ = (!leanh::lean_is_exclusive(v_step_305_)) as u8;
                    if v_isSharedCheck_314_ == 0 {
                        v___x_309_ = v_step_305_;
                        v_isShared_310_ = v_isSharedCheck_314_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_out_307_);
                        leanh::lean_inc(v_it_306_);
                        leanh::lean_dec(v_step_305_);
                        v___x_309_ = leanh::lean_box(0);
                        v_isShared_310_ = v_isSharedCheck_314_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_it_315_ = leanh::lean_ctor_get(v_step_305_, 0);
                    v_isSharedCheck_322_ = (!leanh::lean_is_exclusive(v_step_305_)) as u8;
                    if v_isSharedCheck_322_ == 0 {
                        v___x_317_ = v_step_305_;
                        v_isShared_318_ = v_isSharedCheck_322_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_it_315_);
                        leanh::lean_dec(v_step_305_);
                        v___x_317_ = leanh::lean_box(0);
                        v_isShared_318_ = v_isSharedCheck_322_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    v___x_323_ = leanh::lean_box(2);
                    return v___x_323_;
                }
            },
            1 => {
                if v_isShared_310_ == 0 {
                    v___x_312_ = v___x_309_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_313_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_313_, 0, v_it_306_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_313_, 1, v_out_307_);
                    v___x_312_ = v_reuseFailAlloc_313_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_312_;
            }
            3 => {
                if v_isShared_318_ == 0 {
                    v___x_320_ = v___x_317_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_321_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_321_, 0, v_it_315_);
                    v___x_320_ = v_reuseFailAlloc_321_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_320_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Iterators_Types_Attach_instIterator___redArg___lam__1(
    mut v_toFunctor_324_: *mut leanh::LeanObject,
    mut v_inst_325_: *mut leanh::LeanObject,
    mut v___f_326_: *mut leanh::LeanObject,
    mut v_it_327_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_map_328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_330_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_map_328_ = leanh::lean_ctor_get(v_toFunctor_324_, 0);
    leanh::lean_inc(v_map_328_);
    leanh::lean_dec_ref(v_toFunctor_324_);
    v___x_329_ = leanh::lean_apply_1(v_inst_325_, v_it_327_);
    v___x_330_ = leanh::lean_apply_4(
        v_map_328_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_326_,
        v___x_329_,
    );
    return v___x_330_;
}
pub unsafe fn l_Std_Iterators_Types_Attach_instIterator___redArg(
    mut v_inst_332_: *mut leanh::LeanObject,
    mut v_inst_333_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_337_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_334_ = leanh::lean_ctor_get(v_inst_332_, 0);
    leanh::lean_inc_ref(v_toApplicative_334_);
    leanh::lean_dec_ref(v_inst_332_);
    v_toFunctor_335_ = leanh::lean_ctor_get(v_toApplicative_334_, 0);
    leanh::lean_inc_ref(v_toFunctor_335_);
    leanh::lean_dec_ref(v_toApplicative_334_);
    v___f_336_ = l_Std_Iterators_Types_Attach_instIterator___redArg___closed__0;
    v___f_337_ = leanh::lean_alloc_closure(
        l_Std_Iterators_Types_Attach_instIterator___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_337_, 0, v_toFunctor_335_);
    leanh::lean_closure_set(v___f_337_, 1, v_inst_333_);
    leanh::lean_closure_set(v___f_337_, 2, v___f_336_);
    return v___f_337_;
}
pub unsafe fn l_Std_Iterators_Types_Attach_instIterator(
    mut v_00_u03b1_338_: *mut leanh::LeanObject,
    mut v_00_u03b2_339_: *mut leanh::LeanObject,
    mut v_m_340_: *mut leanh::LeanObject,
    mut v_inst_341_: *mut leanh::LeanObject,
    mut v_inst_342_: *mut leanh::LeanObject,
    mut v_P_343_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_344_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_344_ = l_Std_Iterators_Types_Attach_instIterator___redArg(v_inst_341_, v_inst_342_);
    return v___x_344_;
}
pub unsafe fn l___private_Init_Data_Iterators_Combinators_Monadic_Attach_0__Std_Iterators_Types_Attach_Monadic_modifyStep_match__1_splitter___redArg(
    mut v_step_345_: *mut leanh::LeanObject,
    mut v_h__1_346_: *mut leanh::LeanObject,
    mut v_h__2_347_: *mut leanh::LeanObject,
    mut v_h__3_348_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_step_345_) {
        0 => {
            let mut v_it_349_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_350_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_351_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_348_);
            leanh::lean_dec(v_h__2_347_);
            v_it_349_ = leanh::lean_ctor_get(v_step_345_, 0);
            leanh::lean_inc(v_it_349_);
            v_out_350_ = leanh::lean_ctor_get(v_step_345_, 1);
            leanh::lean_inc(v_out_350_);
            leanh::lean_dec_ref_known(v_step_345_, 2);
            v___x_351_ = leanh::lean_apply_3(
                v_h__1_346_,
                v_it_349_,
                v_out_350_,
                leanh::lean_box(0),
            );
            return v___x_351_;
        }
        1 => {
            let mut v_it_352_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_353_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_348_);
            leanh::lean_dec(v_h__1_346_);
            v_it_352_ = leanh::lean_ctor_get(v_step_345_, 0);
            leanh::lean_inc(v_it_352_);
            leanh::lean_dec_ref_known(v_step_345_, 1);
            v___x_353_ =
                leanh::lean_apply_2(v_h__2_347_, v_it_352_, leanh::lean_box(0));
            return v___x_353_;
        }
        _ => {
            let mut v___x_354_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_347_);
            leanh::lean_dec(v_h__1_346_);
            v___x_354_ = leanh::lean_apply_1(v_h__3_348_, leanh::lean_box(0));
            return v___x_354_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Combinators_Monadic_Attach_0__Std_Iterators_Types_Attach_Monadic_modifyStep_match__1_splitter(
    mut v_00_u03b1_355_: *mut leanh::LeanObject,
    mut v_m_356_: *mut leanh::LeanObject,
    mut v_00_u03b2_357_: *mut leanh::LeanObject,
    mut v_inst_358_: *mut leanh::LeanObject,
    mut v_P_359_: *mut leanh::LeanObject,
    mut v_it_360_: *mut leanh::LeanObject,
    mut v_motive_361_: *mut leanh::LeanObject,
    mut v_step_362_: *mut leanh::LeanObject,
    mut v_h__1_363_: *mut leanh::LeanObject,
    mut v_h__2_364_: *mut leanh::LeanObject,
    mut v_h__3_365_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_step_362_) {
        0 => {
            let mut v_it_366_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_367_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_368_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_365_);
            leanh::lean_dec(v_h__2_364_);
            v_it_366_ = leanh::lean_ctor_get(v_step_362_, 0);
            leanh::lean_inc(v_it_366_);
            v_out_367_ = leanh::lean_ctor_get(v_step_362_, 1);
            leanh::lean_inc(v_out_367_);
            leanh::lean_dec_ref_known(v_step_362_, 2);
            v___x_368_ = leanh::lean_apply_3(
                v_h__1_363_,
                v_it_366_,
                v_out_367_,
                leanh::lean_box(0),
            );
            return v___x_368_;
        }
        1 => {
            let mut v_it_369_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_370_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_365_);
            leanh::lean_dec(v_h__1_363_);
            v_it_369_ = leanh::lean_ctor_get(v_step_362_, 0);
            leanh::lean_inc(v_it_369_);
            leanh::lean_dec_ref_known(v_step_362_, 1);
            v___x_370_ =
                leanh::lean_apply_2(v_h__2_364_, v_it_369_, leanh::lean_box(0));
            return v___x_370_;
        }
        _ => {
            let mut v___x_371_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_364_);
            leanh::lean_dec(v_h__1_363_);
            v___x_371_ = leanh::lean_apply_1(v_h__3_365_, leanh::lean_box(0));
            return v___x_371_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Combinators_Monadic_Attach_0__Std_Iterators_Types_Attach_Monadic_modifyStep_match__1_splitter___boxed(
    mut v_00_u03b1_372_: *mut leanh::LeanObject,
    mut v_m_373_: *mut leanh::LeanObject,
    mut v_00_u03b2_374_: *mut leanh::LeanObject,
    mut v_inst_375_: *mut leanh::LeanObject,
    mut v_P_376_: *mut leanh::LeanObject,
    mut v_it_377_: *mut leanh::LeanObject,
    mut v_motive_378_: *mut leanh::LeanObject,
    mut v_step_379_: *mut leanh::LeanObject,
    mut v_h__1_380_: *mut leanh::LeanObject,
    mut v_h__2_381_: *mut leanh::LeanObject,
    mut v_h__3_382_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_383_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_383_ = l___private_Init_Data_Iterators_Combinators_Monadic_Attach_0__Std_Iterators_Types_Attach_Monadic_modifyStep_match__1_splitter(v_00_u03b1_372_, v_m_373_, v_00_u03b2_374_, v_inst_375_, v_P_376_, v_it_377_, v_motive_378_, v_step_379_, v_h__1_380_, v_h__2_381_, v_h__3_382_);
    leanh::lean_dec(v_it_377_);
    leanh::lean_dec(v_inst_375_);
    return v_res_383_;
}
pub unsafe fn l_Std_Iterators_Types_Attach_instFinitenessRelation(
    mut v_00_u03b1_384_: *mut leanh::LeanObject,
    mut v_00_u03b2_385_: *mut leanh::LeanObject,
    mut v_m_386_: *mut leanh::LeanObject,
    mut v_inst_387_: *mut leanh::LeanObject,
    mut v_inst_388_: *mut leanh::LeanObject,
    mut v_inst_389_: *mut leanh::LeanObject,
    mut v_P_390_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_391_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_391_ = leanh::lean_box(0);
    return v___x_391_;
}
pub unsafe fn l_Std_Iterators_Types_Attach_instFinitenessRelation___boxed(
    mut v_00_u03b1_392_: *mut leanh::LeanObject,
    mut v_00_u03b2_393_: *mut leanh::LeanObject,
    mut v_m_394_: *mut leanh::LeanObject,
    mut v_inst_395_: *mut leanh::LeanObject,
    mut v_inst_396_: *mut leanh::LeanObject,
    mut v_inst_397_: *mut leanh::LeanObject,
    mut v_P_398_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_399_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_399_ = l_Std_Iterators_Types_Attach_instFinitenessRelation(
        v_00_u03b1_392_,
        v_00_u03b2_393_,
        v_m_394_,
        v_inst_395_,
        v_inst_396_,
        v_inst_397_,
        v_P_398_,
    );
    leanh::lean_dec(v_inst_396_);
    leanh::lean_dec_ref(v_inst_395_);
    return v_res_399_;
}
pub unsafe fn l_Std_Iterators_Types_Attach_instProductivenessRelation(
    mut v_00_u03b1_400_: *mut leanh::LeanObject,
    mut v_00_u03b2_401_: *mut leanh::LeanObject,
    mut v_m_402_: *mut leanh::LeanObject,
    mut v_inst_403_: *mut leanh::LeanObject,
    mut v_inst_404_: *mut leanh::LeanObject,
    mut v_inst_405_: *mut leanh::LeanObject,
    mut v_P_406_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_407_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_407_ = leanh::lean_box(0);
    return v___x_407_;
}
pub unsafe fn l_Std_Iterators_Types_Attach_instProductivenessRelation___boxed(
    mut v_00_u03b1_408_: *mut leanh::LeanObject,
    mut v_00_u03b2_409_: *mut leanh::LeanObject,
    mut v_m_410_: *mut leanh::LeanObject,
    mut v_inst_411_: *mut leanh::LeanObject,
    mut v_inst_412_: *mut leanh::LeanObject,
    mut v_inst_413_: *mut leanh::LeanObject,
    mut v_P_414_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_415_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_415_ = l_Std_Iterators_Types_Attach_instProductivenessRelation(
        v_00_u03b1_408_,
        v_00_u03b2_409_,
        v_m_410_,
        v_inst_411_,
        v_inst_412_,
        v_inst_413_,
        v_P_414_,
    );
    leanh::lean_dec(v_inst_412_);
    leanh::lean_dec_ref(v_inst_411_);
    return v_res_415_;
}
pub unsafe fn l_Std_Iterators_Types_Attach_instIteratorLoop___redArg___lam__1(
    mut v_toPure_416_: *mut leanh::LeanObject,
    mut v_recur_417_: *mut leanh::LeanObject,
    mut v_it_418_: *mut leanh::LeanObject,
    mut v_____do__lift_419_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_419_) == 0 {
        let mut v_a_420_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_421_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_it_418_);
        leanh::lean_dec(v_recur_417_);
        v_a_420_ = leanh::lean_ctor_get(v_____do__lift_419_, 0);
        leanh::lean_inc(v_a_420_);
        leanh::lean_dec_ref_known(v_____do__lift_419_, 1);
        v___x_421_ = leanh::lean_apply_2(v_toPure_416_, leanh::lean_box(0), v_a_420_);
        return v___x_421_;
    } else {
        let mut v_a_422_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_423_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_toPure_416_);
        v_a_422_ = leanh::lean_ctor_get(v_____do__lift_419_, 0);
        leanh::lean_inc(v_a_422_);
        leanh::lean_dec_ref_known(v_____do__lift_419_, 1);
        v___x_423_ = leanh::lean_apply_4(
            v_recur_417_,
            v_it_418_,
            v_a_422_,
            leanh::lean_box(0),
            leanh::lean_box(0),
        );
        return v___x_423_;
    }
}
pub unsafe fn l_Std_Iterators_Types_Attach_instIteratorLoop___redArg___lam__0(
    mut v_toPure_424_: *mut leanh::LeanObject,
    mut v_recur_425_: *mut leanh::LeanObject,
    mut v___y_426_: *mut leanh::LeanObject,
    mut v_acc_427_: *mut leanh::LeanObject,
    mut v_toBind_428_: *mut leanh::LeanObject,
    mut v_s_429_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_s_429_) {
        0 => {
            let mut v_it_430_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_431_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_432_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_433_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_434_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_it_430_ = leanh::lean_ctor_get(v_s_429_, 0);
            leanh::lean_inc(v_it_430_);
            v_out_431_ = leanh::lean_ctor_get(v_s_429_, 1);
            leanh::lean_inc(v_out_431_);
            leanh::lean_dec_ref_known(v_s_429_, 2);
            v___f_432_ = leanh::lean_alloc_closure(
                l_Std_Iterators_Types_Attach_instIteratorLoop___redArg___lam__1
                    as *mut core::ffi::c_void,
                4,
                3,
            );
            leanh::lean_closure_set(v___f_432_, 0, v_toPure_424_);
            leanh::lean_closure_set(v___f_432_, 1, v_recur_425_);
            leanh::lean_closure_set(v___f_432_, 2, v_it_430_);
            v___x_433_ = leanh::lean_apply_3(
                v___y_426_,
                v_out_431_,
                leanh::lean_box(0),
                v_acc_427_,
            );
            v___x_434_ = leanh::lean_apply_4(
                v_toBind_428_,
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_433_,
                v___f_432_,
            );
            return v___x_434_;
        }
        1 => {
            let mut v_it_435_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_436_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_toBind_428_);
            leanh::lean_dec(v___y_426_);
            leanh::lean_dec(v_toPure_424_);
            v_it_435_ = leanh::lean_ctor_get(v_s_429_, 0);
            leanh::lean_inc(v_it_435_);
            leanh::lean_dec_ref_known(v_s_429_, 1);
            v___x_436_ = leanh::lean_apply_4(
                v_recur_425_,
                v_it_435_,
                v_acc_427_,
                leanh::lean_box(0),
                leanh::lean_box(0),
            );
            return v___x_436_;
        }
        _ => {
            let mut v___x_437_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_toBind_428_);
            leanh::lean_dec(v___y_426_);
            leanh::lean_dec(v_recur_425_);
            v___x_437_ =
                leanh::lean_apply_2(v_toPure_424_, leanh::lean_box(0), v_acc_427_);
            return v___x_437_;
        }
    }
}
pub unsafe fn l_Std_Iterators_Types_Attach_instIteratorLoop___redArg___lam__2(
    mut v_inst_438_: *mut leanh::LeanObject,
    mut v_toPure_439_: *mut leanh::LeanObject,
    mut v___y_440_: *mut leanh::LeanObject,
    mut v_toBind_441_: *mut leanh::LeanObject,
    mut v_inst_442_: *mut leanh::LeanObject,
    mut v___f_443_: *mut leanh::LeanObject,
    mut v_lift_444_: *mut leanh::LeanObject,
    mut v_it_445_: *mut leanh::LeanObject,
    mut v_acc_446_: *mut leanh::LeanObject,
    mut v_hP_447_: *mut leanh::LeanObject,
    mut v_recur_448_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_455_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_449_ = leanh::lean_ctor_get(v_inst_438_, 0);
    leanh::lean_inc_ref(v_toApplicative_449_);
    leanh::lean_dec_ref(v_inst_438_);
    v_toFunctor_450_ = leanh::lean_ctor_get(v_toApplicative_449_, 0);
    leanh::lean_inc_ref(v_toFunctor_450_);
    leanh::lean_dec_ref(v_toApplicative_449_);
    v_map_451_ = leanh::lean_ctor_get(v_toFunctor_450_, 0);
    leanh::lean_inc(v_map_451_);
    leanh::lean_dec_ref(v_toFunctor_450_);
    v___f_452_ = leanh::lean_alloc_closure(
        l_Std_Iterators_Types_Attach_instIteratorLoop___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        5,
    );
    leanh::lean_closure_set(v___f_452_, 0, v_toPure_439_);
    leanh::lean_closure_set(v___f_452_, 1, v_recur_448_);
    leanh::lean_closure_set(v___f_452_, 2, v___y_440_);
    leanh::lean_closure_set(v___f_452_, 3, v_acc_446_);
    leanh::lean_closure_set(v___f_452_, 4, v_toBind_441_);
    v___x_453_ = leanh::lean_apply_1(v_inst_442_, v_it_445_);
    v___x_454_ = leanh::lean_apply_4(
        v_map_451_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_443_,
        v___x_453_,
    );
    v___x_455_ = leanh::lean_apply_4(
        v_lift_444_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_452_,
        v___x_454_,
    );
    return v___x_455_;
}
pub unsafe fn l_Std_Iterators_Types_Attach_instIteratorLoop___redArg___lam__3(
    mut v_inst_456_: *mut leanh::LeanObject,
    mut v_inst_457_: *mut leanh::LeanObject,
    mut v_inst_458_: *mut leanh::LeanObject,
    mut v___f_459_: *mut leanh::LeanObject,
    mut v_lift_460_: *mut leanh::LeanObject,
    mut v_00_u03b3_461_: *mut leanh::LeanObject,
    mut v_Pl_462_: *mut leanh::LeanObject,
    mut v_it_463_: *mut leanh::LeanObject,
    mut v_init_464_: *mut leanh::LeanObject,
    mut v___y_465_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_470_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_466_ = leanh::lean_ctor_get(v_inst_456_, 0);
    leanh::lean_inc_ref(v_toApplicative_466_);
    v_toBind_467_ = leanh::lean_ctor_get(v_inst_456_, 1);
    leanh::lean_inc(v_toBind_467_);
    leanh::lean_dec_ref(v_inst_456_);
    v_toPure_468_ = leanh::lean_ctor_get(v_toApplicative_466_, 1);
    leanh::lean_inc(v_toPure_468_);
    leanh::lean_dec_ref(v_toApplicative_466_);
    v___f_469_ = leanh::lean_alloc_closure(
        l_Std_Iterators_Types_Attach_instIteratorLoop___redArg___lam__2 as *mut core::ffi::c_void,
        11,
        7,
    );
    leanh::lean_closure_set(v___f_469_, 0, v_inst_457_);
    leanh::lean_closure_set(v___f_469_, 1, v_toPure_468_);
    leanh::lean_closure_set(v___f_469_, 2, v___y_465_);
    leanh::lean_closure_set(v___f_469_, 3, v_toBind_467_);
    leanh::lean_closure_set(v___f_469_, 4, v_inst_458_);
    leanh::lean_closure_set(v___f_469_, 5, v___f_459_);
    leanh::lean_closure_set(v___f_469_, 6, v_lift_460_);
    v___x_470_ = l_WellFounded_opaqueFix_u2083___redArg(
        v___f_469_,
        v_it_463_,
        v_init_464_,
        leanh::lean_box(0),
    );
    return v___x_470_;
}
pub unsafe fn l_Std_Iterators_Types_Attach_instIteratorLoop___redArg(
    mut v_inst_471_: *mut leanh::LeanObject,
    mut v_inst_472_: *mut leanh::LeanObject,
    mut v_inst_473_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_475_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_474_ = l_Std_Iterators_Types_Attach_instIterator___redArg___closed__0;
    v___f_475_ = leanh::lean_alloc_closure(
        l_Std_Iterators_Types_Attach_instIteratorLoop___redArg___lam__3 as *mut core::ffi::c_void,
        10,
        4,
    );
    leanh::lean_closure_set(v___f_475_, 0, v_inst_472_);
    leanh::lean_closure_set(v___f_475_, 1, v_inst_471_);
    leanh::lean_closure_set(v___f_475_, 2, v_inst_473_);
    leanh::lean_closure_set(v___f_475_, 3, v___f_474_);
    return v___f_475_;
}
pub unsafe fn l_Std_Iterators_Types_Attach_instIteratorLoop(
    mut v_00_u03b1_476_: *mut leanh::LeanObject,
    mut v_00_u03b2_477_: *mut leanh::LeanObject,
    mut v_m_478_: *mut leanh::LeanObject,
    mut v_inst_479_: *mut leanh::LeanObject,
    mut v_n_480_: *mut leanh::LeanObject,
    mut v_inst_481_: *mut leanh::LeanObject,
    mut v_P_482_: *mut leanh::LeanObject,
    mut v_inst_483_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_484_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_484_ = l_Std_Iterators_Types_Attach_instIteratorLoop___redArg(
        v_inst_479_,
        v_inst_481_,
        v_inst_483_,
    );
    return v___x_484_;
}
pub unsafe fn l_Std_IterM_attachWith___redArg(
    mut v_it_485_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_it_485_);
    return v_it_485_;
}
pub unsafe fn l_Std_IterM_attachWith___redArg___boxed(
    mut v_it_486_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_487_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_487_ = l_Std_IterM_attachWith___redArg(v_it_486_);
    leanh::lean_dec(v_it_486_);
    return v_res_487_;
}
pub unsafe fn l_Std_IterM_attachWith(
    mut v_00_u03b1_488_: *mut leanh::LeanObject,
    mut v_00_u03b2_489_: *mut leanh::LeanObject,
    mut v_m_490_: *mut leanh::LeanObject,
    mut v_inst_491_: *mut leanh::LeanObject,
    mut v_inst_492_: *mut leanh::LeanObject,
    mut v_it_493_: *mut leanh::LeanObject,
    mut v_P_494_: *mut leanh::LeanObject,
    mut v_h_495_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_it_493_);
    return v_it_493_;
}
pub unsafe fn l_Std_IterM_attachWith___boxed(
    mut v_00_u03b1_496_: *mut leanh::LeanObject,
    mut v_00_u03b2_497_: *mut leanh::LeanObject,
    mut v_m_498_: *mut leanh::LeanObject,
    mut v_inst_499_: *mut leanh::LeanObject,
    mut v_inst_500_: *mut leanh::LeanObject,
    mut v_it_501_: *mut leanh::LeanObject,
    mut v_P_502_: *mut leanh::LeanObject,
    mut v_h_503_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_504_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_504_ = l_Std_IterM_attachWith(
        v_00_u03b1_496_,
        v_00_u03b2_497_,
        v_m_498_,
        v_inst_499_,
        v_inst_500_,
        v_it_501_,
        v_P_502_,
        v_h_503_,
    );
    leanh::lean_dec(v_it_501_);
    leanh::lean_dec(v_inst_500_);
    leanh::lean_dec_ref(v_inst_499_);
    return v_res_504_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_Combinators_Monadic_Attach(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Iterators_Combinators_Monadic_Attach(
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
pub unsafe fn initialize_Init_Data_Iterators_Combinators_Monadic_Attach(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Combinators_Monadic_Attach(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_Combinators_Monadic_Attach(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Iterators_Combinators_Monadic_Attach(builtin);
}