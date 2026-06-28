// Lean compiler output
// Module: Init.Data.Iterators.Combinators.Monadic.Attach
// Imports: Init.Data.Iterators.Consumers.Monadic.Loop
use crate::r#gen::Init::Data::Iterators::Consumers::Monadic::Loop::{
    initialize_Init_Data_Iterators_Consumers_Monadic_Loop,
    runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop,
};
use crate::r#gen::Init::WFExtrinsicFix::l_WellFounded_opaqueFix_u2083___redArg;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get,
    lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_tag,
};
pub static l_Std_Iterators_Types_Attach_instIterator___redArg___closed__0_value: LeanClosureObject<
    0,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Iterators_Types_Attach_instIterator___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Iterators_Types_Attach_instIterator___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Iterators_Types_Attach_instIterator___redArg___closed__0_value)
        as *mut LeanObject;
pub unsafe fn l_Std_Iterators_Types_Attach_Monadic_modifyStep___redArg(
    mut v_step_253_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_it_254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_out_255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_258_: u8 = 0;
    let mut v___x_260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_262_: u8 = 0;
    let mut v_it_263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_266_: u8 = 0;
    let mut v___x_268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_270_: u8 = 0;
    let mut v___x_271_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_step_253_) {
                0 => {
                    v_it_254_ = lean_ctor_get(v_step_253_, 0);
                    v_out_255_ = lean_ctor_get(v_step_253_, 1);
                    v_isSharedCheck_262_ = (!lean_is_exclusive(v_step_253_)) as u8;
                    if v_isSharedCheck_262_ == 0 {
                        v___x_257_ = v_step_253_;
                        v_isShared_258_ = v_isSharedCheck_262_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_out_255_);
                        lean_inc(v_it_254_);
                        lean_dec(v_step_253_);
                        v___x_257_ = lean_box(0);
                        v_isShared_258_ = v_isSharedCheck_262_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_it_263_ = lean_ctor_get(v_step_253_, 0);
                    v_isSharedCheck_270_ = (!lean_is_exclusive(v_step_253_)) as u8;
                    if v_isSharedCheck_270_ == 0 {
                        v___x_265_ = v_step_253_;
                        v_isShared_266_ = v_isSharedCheck_270_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_it_263_);
                        lean_dec(v_step_253_);
                        v___x_265_ = lean_box(0);
                        v_isShared_266_ = v_isSharedCheck_270_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    v___x_271_ = lean_box(2);
                    return v___x_271_;
                }
            },
            1 => {
                if v_isShared_258_ == 0 {
                    v___x_260_ = v___x_257_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_261_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_261_, 0, v_it_254_);
                    lean_ctor_set(v_reuseFailAlloc_261_, 1, v_out_255_);
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
                    v_reuseFailAlloc_269_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_269_, 0, v_it_263_);
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
    mut v_00_u03b1_272_: *mut LeanObject,
    mut v_m_273_: *mut LeanObject,
    mut v_00_u03b2_274_: *mut LeanObject,
    mut v_inst_275_: *mut LeanObject,
    mut v_P_276_: *mut LeanObject,
    mut v_it_277_: *mut LeanObject,
    mut v_step_278_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_it_279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_out_280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_283_: u8 = 0;
    let mut v___x_285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_287_: u8 = 0;
    let mut v_it_288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_291_: u8 = 0;
    let mut v___x_293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_295_: u8 = 0;
    let mut v___x_296_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_step_278_) {
                0 => {
                    v_it_279_ = lean_ctor_get(v_step_278_, 0);
                    v_out_280_ = lean_ctor_get(v_step_278_, 1);
                    v_isSharedCheck_287_ = (!lean_is_exclusive(v_step_278_)) as u8;
                    if v_isSharedCheck_287_ == 0 {
                        v___x_282_ = v_step_278_;
                        v_isShared_283_ = v_isSharedCheck_287_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_out_280_);
                        lean_inc(v_it_279_);
                        lean_dec(v_step_278_);
                        v___x_282_ = lean_box(0);
                        v_isShared_283_ = v_isSharedCheck_287_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_it_288_ = lean_ctor_get(v_step_278_, 0);
                    v_isSharedCheck_295_ = (!lean_is_exclusive(v_step_278_)) as u8;
                    if v_isSharedCheck_295_ == 0 {
                        v___x_290_ = v_step_278_;
                        v_isShared_291_ = v_isSharedCheck_295_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_it_288_);
                        lean_dec(v_step_278_);
                        v___x_290_ = lean_box(0);
                        v_isShared_291_ = v_isSharedCheck_295_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    v___x_296_ = lean_box(2);
                    return v___x_296_;
                }
            },
            1 => {
                if v_isShared_283_ == 0 {
                    v___x_285_ = v___x_282_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_286_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_286_, 0, v_it_279_);
                    lean_ctor_set(v_reuseFailAlloc_286_, 1, v_out_280_);
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
                    v_reuseFailAlloc_294_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_294_, 0, v_it_288_);
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
    mut v_00_u03b1_297_: *mut LeanObject,
    mut v_m_298_: *mut LeanObject,
    mut v_00_u03b2_299_: *mut LeanObject,
    mut v_inst_300_: *mut LeanObject,
    mut v_P_301_: *mut LeanObject,
    mut v_it_302_: *mut LeanObject,
    mut v_step_303_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_304_: *mut LeanObject = core::ptr::null_mut();
    v_res_304_ = l_Std_Iterators_Types_Attach_Monadic_modifyStep(
        v_00_u03b1_297_,
        v_m_298_,
        v_00_u03b2_299_,
        v_inst_300_,
        v_P_301_,
        v_it_302_,
        v_step_303_,
    );
    lean_dec(v_it_302_);
    lean_dec(v_inst_300_);
    return v_res_304_;
}
pub unsafe fn l_Std_Iterators_Types_Attach_instIterator___redArg___lam__0(
    mut v_step_305_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_it_306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_out_307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_310_: u8 = 0;
    let mut v___x_312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_314_: u8 = 0;
    let mut v_it_315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_318_: u8 = 0;
    let mut v___x_320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_322_: u8 = 0;
    let mut v___x_323_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_step_305_) {
                0 => {
                    v_it_306_ = lean_ctor_get(v_step_305_, 0);
                    v_out_307_ = lean_ctor_get(v_step_305_, 1);
                    v_isSharedCheck_314_ = (!lean_is_exclusive(v_step_305_)) as u8;
                    if v_isSharedCheck_314_ == 0 {
                        v___x_309_ = v_step_305_;
                        v_isShared_310_ = v_isSharedCheck_314_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_out_307_);
                        lean_inc(v_it_306_);
                        lean_dec(v_step_305_);
                        v___x_309_ = lean_box(0);
                        v_isShared_310_ = v_isSharedCheck_314_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_it_315_ = lean_ctor_get(v_step_305_, 0);
                    v_isSharedCheck_322_ = (!lean_is_exclusive(v_step_305_)) as u8;
                    if v_isSharedCheck_322_ == 0 {
                        v___x_317_ = v_step_305_;
                        v_isShared_318_ = v_isSharedCheck_322_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_it_315_);
                        lean_dec(v_step_305_);
                        v___x_317_ = lean_box(0);
                        v_isShared_318_ = v_isSharedCheck_322_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    v___x_323_ = lean_box(2);
                    return v___x_323_;
                }
            },
            1 => {
                if v_isShared_310_ == 0 {
                    v___x_312_ = v___x_309_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_313_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_313_, 0, v_it_306_);
                    lean_ctor_set(v_reuseFailAlloc_313_, 1, v_out_307_);
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
                    v_reuseFailAlloc_321_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_321_, 0, v_it_315_);
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
    mut v_toFunctor_324_: *mut LeanObject,
    mut v_inst_325_: *mut LeanObject,
    mut v___f_326_: *mut LeanObject,
    mut v_it_327_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_330_: *mut LeanObject = core::ptr::null_mut();
    v_map_328_ = lean_ctor_get(v_toFunctor_324_, 0);
    lean_inc(v_map_328_);
    lean_dec_ref(v_toFunctor_324_);
    v___x_329_ = lean_apply_1(v_inst_325_, v_it_327_);
    v___x_330_ = lean_apply_4(v_map_328_, lean_box(0), lean_box(0), v___f_326_, v___x_329_);
    return v___x_330_;
}
pub unsafe fn l_Std_Iterators_Types_Attach_instIterator___redArg(
    mut v_inst_332_: *mut LeanObject,
    mut v_inst_333_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_337_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_334_ = lean_ctor_get(v_inst_332_, 0);
    lean_inc_ref(v_toApplicative_334_);
    lean_dec_ref(v_inst_332_);
    v_toFunctor_335_ = lean_ctor_get(v_toApplicative_334_, 0);
    lean_inc_ref(v_toFunctor_335_);
    lean_dec_ref(v_toApplicative_334_);
    v___f_336_ = l_Std_Iterators_Types_Attach_instIterator___redArg___closed__0;
    v___f_337_ = lean_alloc_closure(
        l_Std_Iterators_Types_Attach_instIterator___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_337_, 0, v_toFunctor_335_);
    lean_closure_set(v___f_337_, 1, v_inst_333_);
    lean_closure_set(v___f_337_, 2, v___f_336_);
    return v___f_337_;
}
pub unsafe fn l_Std_Iterators_Types_Attach_instIterator(
    mut v_00_u03b1_338_: *mut LeanObject,
    mut v_00_u03b2_339_: *mut LeanObject,
    mut v_m_340_: *mut LeanObject,
    mut v_inst_341_: *mut LeanObject,
    mut v_inst_342_: *mut LeanObject,
    mut v_P_343_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_344_: *mut LeanObject = core::ptr::null_mut();
    v___x_344_ = l_Std_Iterators_Types_Attach_instIterator___redArg(v_inst_341_, v_inst_342_);
    return v___x_344_;
}
pub unsafe fn l___private_Init_Data_Iterators_Combinators_Monadic_Attach_0__Std_Iterators_Types_Attach_Monadic_modifyStep_match__1_splitter___redArg(
    mut v_step_345_: *mut LeanObject,
    mut v_h__1_346_: *mut LeanObject,
    mut v_h__2_347_: *mut LeanObject,
    mut v_h__3_348_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_step_345_) {
        0 => {
            let mut v_it_349_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_350_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_351_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_348_);
            lean_dec(v_h__2_347_);
            v_it_349_ = lean_ctor_get(v_step_345_, 0);
            lean_inc(v_it_349_);
            v_out_350_ = lean_ctor_get(v_step_345_, 1);
            lean_inc(v_out_350_);
            lean_dec_ref_known(v_step_345_, 2);
            v___x_351_ = lean_apply_3(v_h__1_346_, v_it_349_, v_out_350_, lean_box(0));
            return v___x_351_;
        }
        1 => {
            let mut v_it_352_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_353_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_348_);
            lean_dec(v_h__1_346_);
            v_it_352_ = lean_ctor_get(v_step_345_, 0);
            lean_inc(v_it_352_);
            lean_dec_ref_known(v_step_345_, 1);
            v___x_353_ = lean_apply_2(v_h__2_347_, v_it_352_, lean_box(0));
            return v___x_353_;
        }
        _ => {
            let mut v___x_354_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_347_);
            lean_dec(v_h__1_346_);
            v___x_354_ = lean_apply_1(v_h__3_348_, lean_box(0));
            return v___x_354_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Combinators_Monadic_Attach_0__Std_Iterators_Types_Attach_Monadic_modifyStep_match__1_splitter(
    mut v_00_u03b1_355_: *mut LeanObject,
    mut v_m_356_: *mut LeanObject,
    mut v_00_u03b2_357_: *mut LeanObject,
    mut v_inst_358_: *mut LeanObject,
    mut v_P_359_: *mut LeanObject,
    mut v_it_360_: *mut LeanObject,
    mut v_motive_361_: *mut LeanObject,
    mut v_step_362_: *mut LeanObject,
    mut v_h__1_363_: *mut LeanObject,
    mut v_h__2_364_: *mut LeanObject,
    mut v_h__3_365_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_step_362_) {
        0 => {
            let mut v_it_366_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_367_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_368_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_365_);
            lean_dec(v_h__2_364_);
            v_it_366_ = lean_ctor_get(v_step_362_, 0);
            lean_inc(v_it_366_);
            v_out_367_ = lean_ctor_get(v_step_362_, 1);
            lean_inc(v_out_367_);
            lean_dec_ref_known(v_step_362_, 2);
            v___x_368_ = lean_apply_3(v_h__1_363_, v_it_366_, v_out_367_, lean_box(0));
            return v___x_368_;
        }
        1 => {
            let mut v_it_369_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_370_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_365_);
            lean_dec(v_h__1_363_);
            v_it_369_ = lean_ctor_get(v_step_362_, 0);
            lean_inc(v_it_369_);
            lean_dec_ref_known(v_step_362_, 1);
            v___x_370_ = lean_apply_2(v_h__2_364_, v_it_369_, lean_box(0));
            return v___x_370_;
        }
        _ => {
            let mut v___x_371_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_364_);
            lean_dec(v_h__1_363_);
            v___x_371_ = lean_apply_1(v_h__3_365_, lean_box(0));
            return v___x_371_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Combinators_Monadic_Attach_0__Std_Iterators_Types_Attach_Monadic_modifyStep_match__1_splitter___boxed(
    mut v_00_u03b1_372_: *mut LeanObject,
    mut v_m_373_: *mut LeanObject,
    mut v_00_u03b2_374_: *mut LeanObject,
    mut v_inst_375_: *mut LeanObject,
    mut v_P_376_: *mut LeanObject,
    mut v_it_377_: *mut LeanObject,
    mut v_motive_378_: *mut LeanObject,
    mut v_step_379_: *mut LeanObject,
    mut v_h__1_380_: *mut LeanObject,
    mut v_h__2_381_: *mut LeanObject,
    mut v_h__3_382_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_383_: *mut LeanObject = core::ptr::null_mut();
    v_res_383_ = l___private_Init_Data_Iterators_Combinators_Monadic_Attach_0__Std_Iterators_Types_Attach_Monadic_modifyStep_match__1_splitter(v_00_u03b1_372_, v_m_373_, v_00_u03b2_374_, v_inst_375_, v_P_376_, v_it_377_, v_motive_378_, v_step_379_, v_h__1_380_, v_h__2_381_, v_h__3_382_);
    lean_dec(v_it_377_);
    lean_dec(v_inst_375_);
    return v_res_383_;
}
pub unsafe fn l_Std_Iterators_Types_Attach_instFinitenessRelation(
    mut v_00_u03b1_384_: *mut LeanObject,
    mut v_00_u03b2_385_: *mut LeanObject,
    mut v_m_386_: *mut LeanObject,
    mut v_inst_387_: *mut LeanObject,
    mut v_inst_388_: *mut LeanObject,
    mut v_inst_389_: *mut LeanObject,
    mut v_P_390_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_391_: *mut LeanObject = core::ptr::null_mut();
    v___x_391_ = lean_box(0);
    return v___x_391_;
}
pub unsafe fn l_Std_Iterators_Types_Attach_instFinitenessRelation___boxed(
    mut v_00_u03b1_392_: *mut LeanObject,
    mut v_00_u03b2_393_: *mut LeanObject,
    mut v_m_394_: *mut LeanObject,
    mut v_inst_395_: *mut LeanObject,
    mut v_inst_396_: *mut LeanObject,
    mut v_inst_397_: *mut LeanObject,
    mut v_P_398_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_399_: *mut LeanObject = core::ptr::null_mut();
    v_res_399_ = l_Std_Iterators_Types_Attach_instFinitenessRelation(
        v_00_u03b1_392_,
        v_00_u03b2_393_,
        v_m_394_,
        v_inst_395_,
        v_inst_396_,
        v_inst_397_,
        v_P_398_,
    );
    lean_dec(v_inst_396_);
    lean_dec_ref(v_inst_395_);
    return v_res_399_;
}
pub unsafe fn l_Std_Iterators_Types_Attach_instProductivenessRelation(
    mut v_00_u03b1_400_: *mut LeanObject,
    mut v_00_u03b2_401_: *mut LeanObject,
    mut v_m_402_: *mut LeanObject,
    mut v_inst_403_: *mut LeanObject,
    mut v_inst_404_: *mut LeanObject,
    mut v_inst_405_: *mut LeanObject,
    mut v_P_406_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_407_: *mut LeanObject = core::ptr::null_mut();
    v___x_407_ = lean_box(0);
    return v___x_407_;
}
pub unsafe fn l_Std_Iterators_Types_Attach_instProductivenessRelation___boxed(
    mut v_00_u03b1_408_: *mut LeanObject,
    mut v_00_u03b2_409_: *mut LeanObject,
    mut v_m_410_: *mut LeanObject,
    mut v_inst_411_: *mut LeanObject,
    mut v_inst_412_: *mut LeanObject,
    mut v_inst_413_: *mut LeanObject,
    mut v_P_414_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_415_: *mut LeanObject = core::ptr::null_mut();
    v_res_415_ = l_Std_Iterators_Types_Attach_instProductivenessRelation(
        v_00_u03b1_408_,
        v_00_u03b2_409_,
        v_m_410_,
        v_inst_411_,
        v_inst_412_,
        v_inst_413_,
        v_P_414_,
    );
    lean_dec(v_inst_412_);
    lean_dec_ref(v_inst_411_);
    return v_res_415_;
}
pub unsafe fn l_Std_Iterators_Types_Attach_instIteratorLoop___redArg___lam__1(
    mut v_toPure_416_: *mut LeanObject,
    mut v_recur_417_: *mut LeanObject,
    mut v_it_418_: *mut LeanObject,
    mut v_____do__lift_419_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_419_) == 0 {
        let mut v_a_420_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_421_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_it_418_);
        lean_dec(v_recur_417_);
        v_a_420_ = lean_ctor_get(v_____do__lift_419_, 0);
        lean_inc(v_a_420_);
        lean_dec_ref_known(v_____do__lift_419_, 1);
        v___x_421_ = lean_apply_2(v_toPure_416_, lean_box(0), v_a_420_);
        return v___x_421_;
    } else {
        let mut v_a_422_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_423_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_416_);
        v_a_422_ = lean_ctor_get(v_____do__lift_419_, 0);
        lean_inc(v_a_422_);
        lean_dec_ref_known(v_____do__lift_419_, 1);
        v___x_423_ = lean_apply_4(v_recur_417_, v_it_418_, v_a_422_, lean_box(0), lean_box(0));
        return v___x_423_;
    }
}
pub unsafe fn l_Std_Iterators_Types_Attach_instIteratorLoop___redArg___lam__0(
    mut v_toPure_424_: *mut LeanObject,
    mut v_recur_425_: *mut LeanObject,
    mut v___y_426_: *mut LeanObject,
    mut v_acc_427_: *mut LeanObject,
    mut v_toBind_428_: *mut LeanObject,
    mut v_s_429_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_s_429_) {
        0 => {
            let mut v_it_430_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_431_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_432_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_433_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_434_: *mut LeanObject = core::ptr::null_mut();
            v_it_430_ = lean_ctor_get(v_s_429_, 0);
            lean_inc(v_it_430_);
            v_out_431_ = lean_ctor_get(v_s_429_, 1);
            lean_inc(v_out_431_);
            lean_dec_ref_known(v_s_429_, 2);
            v___f_432_ = lean_alloc_closure(
                l_Std_Iterators_Types_Attach_instIteratorLoop___redArg___lam__1
                    as *mut core::ffi::c_void,
                4,
                3,
            );
            lean_closure_set(v___f_432_, 0, v_toPure_424_);
            lean_closure_set(v___f_432_, 1, v_recur_425_);
            lean_closure_set(v___f_432_, 2, v_it_430_);
            v___x_433_ = lean_apply_3(v___y_426_, v_out_431_, lean_box(0), v_acc_427_);
            v___x_434_ = lean_apply_4(
                v_toBind_428_,
                lean_box(0),
                lean_box(0),
                v___x_433_,
                v___f_432_,
            );
            return v___x_434_;
        }
        1 => {
            let mut v_it_435_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_436_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_toBind_428_);
            lean_dec(v___y_426_);
            lean_dec(v_toPure_424_);
            v_it_435_ = lean_ctor_get(v_s_429_, 0);
            lean_inc(v_it_435_);
            lean_dec_ref_known(v_s_429_, 1);
            v___x_436_ = lean_apply_4(
                v_recur_425_,
                v_it_435_,
                v_acc_427_,
                lean_box(0),
                lean_box(0),
            );
            return v___x_436_;
        }
        _ => {
            let mut v___x_437_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_toBind_428_);
            lean_dec(v___y_426_);
            lean_dec(v_recur_425_);
            v___x_437_ = lean_apply_2(v_toPure_424_, lean_box(0), v_acc_427_);
            return v___x_437_;
        }
    }
}
pub unsafe fn l_Std_Iterators_Types_Attach_instIteratorLoop___redArg___lam__2(
    mut v_inst_438_: *mut LeanObject,
    mut v_toPure_439_: *mut LeanObject,
    mut v___y_440_: *mut LeanObject,
    mut v_toBind_441_: *mut LeanObject,
    mut v_inst_442_: *mut LeanObject,
    mut v___f_443_: *mut LeanObject,
    mut v_lift_444_: *mut LeanObject,
    mut v_it_445_: *mut LeanObject,
    mut v_acc_446_: *mut LeanObject,
    mut v_hP_447_: *mut LeanObject,
    mut v_recur_448_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_455_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_449_ = lean_ctor_get(v_inst_438_, 0);
    lean_inc_ref(v_toApplicative_449_);
    lean_dec_ref(v_inst_438_);
    v_toFunctor_450_ = lean_ctor_get(v_toApplicative_449_, 0);
    lean_inc_ref(v_toFunctor_450_);
    lean_dec_ref(v_toApplicative_449_);
    v_map_451_ = lean_ctor_get(v_toFunctor_450_, 0);
    lean_inc(v_map_451_);
    lean_dec_ref(v_toFunctor_450_);
    v___f_452_ = lean_alloc_closure(
        l_Std_Iterators_Types_Attach_instIteratorLoop___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_452_, 0, v_toPure_439_);
    lean_closure_set(v___f_452_, 1, v_recur_448_);
    lean_closure_set(v___f_452_, 2, v___y_440_);
    lean_closure_set(v___f_452_, 3, v_acc_446_);
    lean_closure_set(v___f_452_, 4, v_toBind_441_);
    v___x_453_ = lean_apply_1(v_inst_442_, v_it_445_);
    v___x_454_ = lean_apply_4(v_map_451_, lean_box(0), lean_box(0), v___f_443_, v___x_453_);
    v___x_455_ = lean_apply_4(
        v_lift_444_,
        lean_box(0),
        lean_box(0),
        v___f_452_,
        v___x_454_,
    );
    return v___x_455_;
}
pub unsafe fn l_Std_Iterators_Types_Attach_instIteratorLoop___redArg___lam__3(
    mut v_inst_456_: *mut LeanObject,
    mut v_inst_457_: *mut LeanObject,
    mut v_inst_458_: *mut LeanObject,
    mut v___f_459_: *mut LeanObject,
    mut v_lift_460_: *mut LeanObject,
    mut v_00_u03b3_461_: *mut LeanObject,
    mut v_Pl_462_: *mut LeanObject,
    mut v_it_463_: *mut LeanObject,
    mut v_init_464_: *mut LeanObject,
    mut v___y_465_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_470_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_466_ = lean_ctor_get(v_inst_456_, 0);
    lean_inc_ref(v_toApplicative_466_);
    v_toBind_467_ = lean_ctor_get(v_inst_456_, 1);
    lean_inc(v_toBind_467_);
    lean_dec_ref(v_inst_456_);
    v_toPure_468_ = lean_ctor_get(v_toApplicative_466_, 1);
    lean_inc(v_toPure_468_);
    lean_dec_ref(v_toApplicative_466_);
    v___f_469_ = lean_alloc_closure(
        l_Std_Iterators_Types_Attach_instIteratorLoop___redArg___lam__2 as *mut core::ffi::c_void,
        11,
        7,
    );
    lean_closure_set(v___f_469_, 0, v_inst_457_);
    lean_closure_set(v___f_469_, 1, v_toPure_468_);
    lean_closure_set(v___f_469_, 2, v___y_465_);
    lean_closure_set(v___f_469_, 3, v_toBind_467_);
    lean_closure_set(v___f_469_, 4, v_inst_458_);
    lean_closure_set(v___f_469_, 5, v___f_459_);
    lean_closure_set(v___f_469_, 6, v_lift_460_);
    v___x_470_ =
        l_WellFounded_opaqueFix_u2083___redArg(v___f_469_, v_it_463_, v_init_464_, lean_box(0));
    return v___x_470_;
}
pub unsafe fn l_Std_Iterators_Types_Attach_instIteratorLoop___redArg(
    mut v_inst_471_: *mut LeanObject,
    mut v_inst_472_: *mut LeanObject,
    mut v_inst_473_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_475_: *mut LeanObject = core::ptr::null_mut();
    v___f_474_ = l_Std_Iterators_Types_Attach_instIterator___redArg___closed__0;
    v___f_475_ = lean_alloc_closure(
        l_Std_Iterators_Types_Attach_instIteratorLoop___redArg___lam__3 as *mut core::ffi::c_void,
        10,
        4,
    );
    lean_closure_set(v___f_475_, 0, v_inst_472_);
    lean_closure_set(v___f_475_, 1, v_inst_471_);
    lean_closure_set(v___f_475_, 2, v_inst_473_);
    lean_closure_set(v___f_475_, 3, v___f_474_);
    return v___f_475_;
}
pub unsafe fn l_Std_Iterators_Types_Attach_instIteratorLoop(
    mut v_00_u03b1_476_: *mut LeanObject,
    mut v_00_u03b2_477_: *mut LeanObject,
    mut v_m_478_: *mut LeanObject,
    mut v_inst_479_: *mut LeanObject,
    mut v_n_480_: *mut LeanObject,
    mut v_inst_481_: *mut LeanObject,
    mut v_P_482_: *mut LeanObject,
    mut v_inst_483_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_484_: *mut LeanObject = core::ptr::null_mut();
    v___x_484_ = l_Std_Iterators_Types_Attach_instIteratorLoop___redArg(
        v_inst_479_,
        v_inst_481_,
        v_inst_483_,
    );
    return v___x_484_;
}
pub unsafe fn l_Std_IterM_attachWith___redArg(mut v_it_485_: *mut LeanObject) -> *mut LeanObject {
    lean_inc(v_it_485_);
    return v_it_485_;
}
pub unsafe fn l_Std_IterM_attachWith___redArg___boxed(
    mut v_it_486_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_487_: *mut LeanObject = core::ptr::null_mut();
    v_res_487_ = l_Std_IterM_attachWith___redArg(v_it_486_);
    lean_dec(v_it_486_);
    return v_res_487_;
}
pub unsafe fn l_Std_IterM_attachWith(
    mut v_00_u03b1_488_: *mut LeanObject,
    mut v_00_u03b2_489_: *mut LeanObject,
    mut v_m_490_: *mut LeanObject,
    mut v_inst_491_: *mut LeanObject,
    mut v_inst_492_: *mut LeanObject,
    mut v_it_493_: *mut LeanObject,
    mut v_P_494_: *mut LeanObject,
    mut v_h_495_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_it_493_);
    return v_it_493_;
}
pub unsafe fn l_Std_IterM_attachWith___boxed(
    mut v_00_u03b1_496_: *mut LeanObject,
    mut v_00_u03b2_497_: *mut LeanObject,
    mut v_m_498_: *mut LeanObject,
    mut v_inst_499_: *mut LeanObject,
    mut v_inst_500_: *mut LeanObject,
    mut v_it_501_: *mut LeanObject,
    mut v_P_502_: *mut LeanObject,
    mut v_h_503_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_504_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_it_501_);
    lean_dec(v_inst_500_);
    lean_dec_ref(v_inst_499_);
    return v_res_504_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_Combinators_Monadic_Attach(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Iterators_Combinators_Monadic_Attach(
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
pub unsafe fn initialize_Init_Data_Iterators_Combinators_Monadic_Attach(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Combinators_Monadic_Attach(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_Combinators_Monadic_Attach(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Iterators_Combinators_Monadic_Attach(builtin);
}
