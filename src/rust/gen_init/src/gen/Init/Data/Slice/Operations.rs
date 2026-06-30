// Lean compiler output
// Module: Init.Data.Slice.Operations
// Imports: Init.Data.Slice.Basic Init.Data.Iterators.ToIterator Init.Data.Iterators.Consumers.Loop Init.Data.Iterators.Consumers.Collect
use crate::ffi::{lean_array_push, lean_array_to_list};
use crate::r#gen::Init::Data::Iterators::Consumers::Collect::{
    initialize_Init_Data_Iterators_Consumers_Collect,
    runtime_initialize_Init_Data_Iterators_Consumers_Collect,
};
use crate::r#gen::Init::Data::Iterators::Consumers::Loop::{
    initialize_Init_Data_Iterators_Consumers_Loop,
    runtime_initialize_Init_Data_Iterators_Consumers_Loop,
};
use crate::r#gen::Init::Data::Iterators::ToIterator::{
    initialize_Init_Data_Iterators_ToIterator, runtime_initialize_Init_Data_Iterators_ToIterator,
};
use crate::r#gen::Init::Data::Slice::Basic::{
    initialize_Init_Data_Slice_Basic, runtime_initialize_Init_Data_Slice_Basic,
};
use crate::r#gen::Init::WFExtrinsicFix::l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg;
pub static l_Std_Slice_toArray___redArg___closed__0_value: leanh::LeanArrayObject<0> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Std_Slice_toArray___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Slice_toArray___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___redArg___closed__0_value:
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
    m_fun: l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___redArg___lam__0
        as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___redArg___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Std_Slice_foldlM___redArg___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Slice_foldlM___redArg___lam__1 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Slice_foldlM___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Slice_foldlM___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Std_Slice_instToIterator___redArg___lam__0(
    mut v_inst_272_: *mut leanh::LeanObject,
    mut v_x_273_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_274_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_274_ = leanh::lean_apply_1(v_inst_272_, v_x_273_);
    return v___x_274_;
}
pub unsafe fn l_Std_Slice_instToIterator___redArg(
    mut v_inst_275_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_276_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_276_ = leanh::lean_alloc_closure(
        l_Std_Slice_instToIterator___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_276_, 0, v_inst_275_);
    return v___f_276_;
}
pub unsafe fn l_Std_Slice_instToIterator(
    mut v_00_u03b3_277_: *mut leanh::LeanObject,
    mut v_m_278_: *mut leanh::LeanObject,
    mut v_00_u03b1_279_: *mut leanh::LeanObject,
    mut v_00_u03b2_280_: *mut leanh::LeanObject,
    mut v_inst_281_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_282_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_282_ = leanh::lean_alloc_closure(
        l_Std_Slice_instToIterator___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_282_, 0, v_inst_281_);
    return v___f_282_;
}
pub unsafe fn l_Std_Slice_Internal_iter___redArg(
    mut v_inst_283_: *mut leanh::LeanObject,
    mut v_s_284_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_285_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_285_ = leanh::lean_apply_1(v_inst_283_, v_s_284_);
    return v___x_285_;
}
pub unsafe fn l_Std_Slice_Internal_iter(
    mut v_00_u03b3_286_: *mut leanh::LeanObject,
    mut v_00_u03b1_287_: *mut leanh::LeanObject,
    mut v_00_u03b2_288_: *mut leanh::LeanObject,
    mut v_inst_289_: *mut leanh::LeanObject,
    mut v_s_290_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_291_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_291_ = leanh::lean_apply_1(v_inst_289_, v_s_290_);
    return v___x_291_;
}
pub unsafe fn l_Std_Slice_size___redArg(
    mut v_s_292_: *mut leanh::LeanObject,
    mut v_inst_293_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_294_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_294_ = leanh::lean_apply_1(v_inst_293_, v_s_292_);
    return v___x_294_;
}
pub unsafe fn l_Std_Slice_size(
    mut v_00_u03b3_295_: *mut leanh::LeanObject,
    mut v_s_296_: *mut leanh::LeanObject,
    mut v_inst_297_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_298_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_298_ = leanh::lean_apply_1(v_inst_297_, v_s_296_);
    return v___x_298_;
}
pub unsafe fn l_Std_Slice_toArray___redArg___lam__0(
    mut v_inst_299_: *mut leanh::LeanObject,
    mut v_it_300_: *mut leanh::LeanObject,
    mut v_acc_301_: *mut leanh::LeanObject,
    mut v_recur_302_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_val_303_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_val_303_ = leanh::lean_apply_1(v_inst_299_, v_it_300_);
    match leanh::lean_obj_tag(v_val_303_) {
        0 => {
            let mut v_it_304_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_305_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_306_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_307_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_it_304_ = leanh::lean_ctor_get(v_val_303_, 0);
            leanh::lean_inc(v_it_304_);
            v_out_305_ = leanh::lean_ctor_get(v_val_303_, 1);
            leanh::lean_inc(v_out_305_);
            leanh::lean_dec_ref_known(v_val_303_, 2);
            v___x_306_ = lean_array_push(v_acc_301_, v_out_305_);
            v___x_307_ = leanh::lean_apply_3(
                v_recur_302_,
                v_it_304_,
                v___x_306_,
                leanh::lean_box(0),
            );
            return v___x_307_;
        }
        1 => {
            let mut v_it_308_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_309_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_it_308_ = leanh::lean_ctor_get(v_val_303_, 0);
            leanh::lean_inc(v_it_308_);
            leanh::lean_dec_ref_known(v_val_303_, 1);
            v___x_309_ = leanh::lean_apply_3(
                v_recur_302_,
                v_it_308_,
                v_acc_301_,
                leanh::lean_box(0),
            );
            return v___x_309_;
        }
        _ => {
            leanh::lean_dec_ref(v_recur_302_);
            return v_acc_301_;
        }
    }
}
pub unsafe fn l_Std_Slice_toArray___redArg(
    mut v_inst_312_: *mut leanh::LeanObject,
    mut v_inst_313_: *mut leanh::LeanObject,
    mut v_s_314_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_318_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_315_ = leanh::lean_alloc_closure(
        l_Std_Slice_toArray___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_315_, 0, v_inst_313_);
    v___x_316_ = leanh::lean_apply_1(v_inst_312_, v_s_314_);
    v___x_317_ = l_Std_Slice_toArray___redArg___closed__0;
    v___x_318_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_315_, v___x_316_, v___x_317_,
    );
    return v___x_318_;
}
pub unsafe fn l_Std_Slice_toArray(
    mut v_00_u03b3_319_: *mut leanh::LeanObject,
    mut v_00_u03b1_320_: *mut leanh::LeanObject,
    mut v_00_u03b2_321_: *mut leanh::LeanObject,
    mut v_inst_322_: *mut leanh::LeanObject,
    mut v_inst_323_: *mut leanh::LeanObject,
    mut v_s_324_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_328_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_325_ = leanh::lean_alloc_closure(
        l_Std_Slice_toArray___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_325_, 0, v_inst_323_);
    v___x_326_ = leanh::lean_apply_1(v_inst_322_, v_s_324_);
    v___x_327_ = l_Std_Slice_toArray___redArg___closed__0;
    v___x_328_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_325_, v___x_326_, v___x_327_,
    );
    return v___x_328_;
}
pub unsafe fn l_Std_Slice_toList___redArg(
    mut v_inst_329_: *mut leanh::LeanObject,
    mut v_inst_330_: *mut leanh::LeanObject,
    mut v_s_331_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_336_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_332_ = leanh::lean_alloc_closure(
        l_Std_Slice_toArray___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_332_, 0, v_inst_330_);
    v___x_333_ = leanh::lean_apply_1(v_inst_329_, v_s_331_);
    v___x_334_ = l_Std_Slice_toArray___redArg___closed__0;
    v___x_335_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_332_, v___x_333_, v___x_334_,
    );
    v___x_336_ = lean_array_to_list(v___x_335_);
    return v___x_336_;
}
pub unsafe fn l_Std_Slice_toList(
    mut v_00_u03b3_337_: *mut leanh::LeanObject,
    mut v_00_u03b1_338_: *mut leanh::LeanObject,
    mut v_00_u03b2_339_: *mut leanh::LeanObject,
    mut v_inst_340_: *mut leanh::LeanObject,
    mut v_inst_341_: *mut leanh::LeanObject,
    mut v_s_342_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_347_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_343_ = leanh::lean_alloc_closure(
        l_Std_Slice_toArray___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_343_, 0, v_inst_341_);
    v___x_344_ = leanh::lean_apply_1(v_inst_340_, v_s_342_);
    v___x_345_ = l_Std_Slice_toArray___redArg___closed__0;
    v___x_346_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_343_, v___x_344_, v___x_345_,
    );
    v___x_347_ = lean_array_to_list(v___x_346_);
    return v___x_347_;
}
pub unsafe fn l_Std_Slice_toListRev___redArg___lam__0(
    mut v_inst_348_: *mut leanh::LeanObject,
    mut v_it_349_: *mut leanh::LeanObject,
    mut v_acc_350_: *mut leanh::LeanObject,
    mut v_recur_351_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_val_352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_357_: u8 = 0;
    let mut v___x_359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_362_: u8 = 0;
    let mut v_it_363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_val_352_ = leanh::lean_apply_1(v_inst_348_, v_it_349_);
                match leanh::lean_obj_tag(v_val_352_) {
                    0 => {
                        v_it_353_ = leanh::lean_ctor_get(v_val_352_, 0);
                        v_out_354_ = leanh::lean_ctor_get(v_val_352_, 1);
                        v_isSharedCheck_362_ = (!leanh::lean_is_exclusive(v_val_352_)) as u8;
                        if v_isSharedCheck_362_ == 0 {
                            v___x_356_ = v_val_352_;
                            v_isShared_357_ = v_isSharedCheck_362_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_out_354_);
                            leanh::lean_inc(v_it_353_);
                            leanh::lean_dec(v_val_352_);
                            v___x_356_ = leanh::lean_box(0);
                            v_isShared_357_ = v_isSharedCheck_362_;
                            state = 1;
                            continue;
                        }
                    }
                    1 => {
                        v_it_363_ = leanh::lean_ctor_get(v_val_352_, 0);
                        leanh::lean_inc(v_it_363_);
                        leanh::lean_dec_ref_known(v_val_352_, 1);
                        v___x_364_ = leanh::lean_apply_3(
                            v_recur_351_,
                            v_it_363_,
                            v_acc_350_,
                            leanh::lean_box(0),
                        );
                        return v___x_364_;
                    }
                    _ => {
                        leanh::lean_dec_ref(v_recur_351_);
                        return v_acc_350_;
                    }
                }
            }
            1 => {
                if v_isShared_357_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_356_, 1);
                    leanh::lean_ctor_set(v___x_356_, 1, v_acc_350_);
                    leanh::lean_ctor_set(v___x_356_, 0, v_out_354_);
                    v___x_359_ = v___x_356_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_361_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_361_, 0, v_out_354_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_361_, 1, v_acc_350_);
                    v___x_359_ = v_reuseFailAlloc_361_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_360_ = leanh::lean_apply_3(
                    v_recur_351_,
                    v_it_353_,
                    v___x_359_,
                    leanh::lean_box(0),
                );
                return v___x_360_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Slice_toListRev___redArg(
    mut v_inst_365_: *mut leanh::LeanObject,
    mut v_inst_366_: *mut leanh::LeanObject,
    mut v_s_367_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_371_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_368_ = leanh::lean_alloc_closure(
        l_Std_Slice_toListRev___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_368_, 0, v_inst_366_);
    v___x_369_ = leanh::lean_apply_1(v_inst_365_, v_s_367_);
    v___x_370_ = leanh::lean_box(0);
    v___x_371_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_368_, v___x_369_, v___x_370_,
    );
    return v___x_371_;
}
pub unsafe fn l_Std_Slice_toListRev(
    mut v_00_u03b3_372_: *mut leanh::LeanObject,
    mut v_00_u03b1_373_: *mut leanh::LeanObject,
    mut v_00_u03b2_374_: *mut leanh::LeanObject,
    mut v_inst_375_: *mut leanh::LeanObject,
    mut v_inst_376_: *mut leanh::LeanObject,
    mut v_s_377_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_381_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_378_ = leanh::lean_alloc_closure(
        l_Std_Slice_toListRev___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_378_, 0, v_inst_376_);
    v___x_379_ = leanh::lean_apply_1(v_inst_375_, v_s_377_);
    v___x_380_ = leanh::lean_box(0);
    v___x_381_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_378_, v___x_379_, v___x_380_,
    );
    return v___x_381_;
}
pub unsafe fn l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___redArg___lam__0(
    mut v_x_382_: *mut leanh::LeanObject,
    mut v_x_383_: *mut leanh::LeanObject,
    mut v_f_384_: *mut leanh::LeanObject,
    mut v_c_385_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_386_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_386_ = leanh::lean_apply_1(v_f_384_, v_c_385_);
    return v___x_386_;
}
pub unsafe fn l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___redArg___lam__1(
    mut v_toPure_387_: *mut leanh::LeanObject,
    mut v_____do__lift_388_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_389_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_389_ = leanh::lean_apply_2(
        v_toPure_387_,
        leanh::lean_box(0),
        v_____do__lift_388_,
    );
    return v___x_389_;
}
pub unsafe fn l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___redArg___lam__2(
    mut v_f_390_: *mut leanh::LeanObject,
    mut v_toBind_391_: *mut leanh::LeanObject,
    mut v___f_392_: *mut leanh::LeanObject,
    mut v_x1_393_: *mut leanh::LeanObject,
    mut v_x2_394_: *mut leanh::LeanObject,
    mut v_x3_395_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_397_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_396_ = leanh::lean_apply_2(v_f_390_, v_x1_393_, v_x3_395_);
    v___x_397_ = leanh::lean_apply_4(
        v_toBind_391_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_396_,
        v___f_392_,
    );
    return v___x_397_;
}
pub unsafe fn l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___redArg___lam__3(
    mut v_inst_398_: *mut leanh::LeanObject,
    mut v_inst_399_: *mut leanh::LeanObject,
    mut v_inst_400_: *mut leanh::LeanObject,
    mut v___f_401_: *mut leanh::LeanObject,
    mut v_00_u03b2_402_: *mut leanh::LeanObject,
    mut v_s_403_: *mut leanh::LeanObject,
    mut v_init_404_: *mut leanh::LeanObject,
    mut v_f_405_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_412_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_406_ = leanh::lean_ctor_get(v_inst_398_, 0);
    leanh::lean_inc_ref(v_toApplicative_406_);
    v_toBind_407_ = leanh::lean_ctor_get(v_inst_398_, 1);
    leanh::lean_inc(v_toBind_407_);
    leanh::lean_dec_ref(v_inst_398_);
    v_toPure_408_ = leanh::lean_ctor_get(v_toApplicative_406_, 1);
    leanh::lean_inc(v_toPure_408_);
    leanh::lean_dec_ref(v_toApplicative_406_);
    v___x_409_ = leanh::lean_apply_1(v_inst_399_, v_s_403_);
    v___f_410_ = leanh::lean_alloc_closure(
        l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___redArg___lam__1
            as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_410_, 0, v_toPure_408_);
    v___f_411_ = leanh::lean_alloc_closure(
        l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___redArg___lam__2
            as *mut core::ffi::c_void,
        6,
        3,
    );
    leanh::lean_closure_set(v___f_411_, 0, v_f_405_);
    leanh::lean_closure_set(v___f_411_, 1, v_toBind_407_);
    leanh::lean_closure_set(v___f_411_, 2, v___f_410_);
    v___x_412_ = leanh::lean_apply_6(
        v_inst_400_,
        v___f_401_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_409_,
        v_init_404_,
        v___f_411_,
    );
    return v___x_412_;
}
pub unsafe fn l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___redArg(
    mut v_inst_414_: *mut leanh::LeanObject,
    mut v_inst_415_: *mut leanh::LeanObject,
    mut v_inst_416_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_418_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_417_ = l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___redArg___closed__0;
    v___f_418_ = leanh::lean_alloc_closure(
        l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___redArg___lam__3
            as *mut core::ffi::c_void,
        8,
        4,
    );
    leanh::lean_closure_set(v___f_418_, 0, v_inst_414_);
    leanh::lean_closure_set(v___f_418_, 1, v_inst_415_);
    leanh::lean_closure_set(v___f_418_, 2, v_inst_416_);
    leanh::lean_closure_set(v___f_418_, 3, v___f_417_);
    return v___f_418_;
}
pub unsafe fn l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId(
    mut v_m_419_: *mut leanh::LeanObject,
    mut v_00_u03b1_420_: *mut leanh::LeanObject,
    mut v_00_u03b3_421_: *mut leanh::LeanObject,
    mut v_00_u03b2_422_: *mut leanh::LeanObject,
    mut v_inst_423_: *mut leanh::LeanObject,
    mut v_inst_424_: *mut leanh::LeanObject,
    mut v_inst_425_: *mut leanh::LeanObject,
    mut v_inst_426_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_427_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_427_ = l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___redArg(
        v_inst_423_,
        v_inst_424_,
        v_inst_426_,
    );
    return v___x_427_;
}
pub unsafe fn l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___boxed(
    mut v_m_428_: *mut leanh::LeanObject,
    mut v_00_u03b1_429_: *mut leanh::LeanObject,
    mut v_00_u03b3_430_: *mut leanh::LeanObject,
    mut v_00_u03b2_431_: *mut leanh::LeanObject,
    mut v_inst_432_: *mut leanh::LeanObject,
    mut v_inst_433_: *mut leanh::LeanObject,
    mut v_inst_434_: *mut leanh::LeanObject,
    mut v_inst_435_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_436_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_436_ = l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId(
        v_m_428_,
        v_00_u03b1_429_,
        v_00_u03b3_430_,
        v_00_u03b2_431_,
        v_inst_432_,
        v_inst_433_,
        v_inst_434_,
        v_inst_435_,
    );
    leanh::lean_dec(v_inst_434_);
    return v_res_436_;
}
pub unsafe fn l_Std_Slice_foldlM___redArg___lam__1(
    mut v_a_437_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_438_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_438_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_438_, 0, v_a_437_);
    return v___x_438_;
}
pub unsafe fn l_Std_Slice_foldlM___redArg___lam__2(
    mut v_toFunctor_439_: *mut leanh::LeanObject,
    mut v_f_440_: *mut leanh::LeanObject,
    mut v___f_441_: *mut leanh::LeanObject,
    mut v_toBind_442_: *mut leanh::LeanObject,
    mut v___f_443_: *mut leanh::LeanObject,
    mut v_x1_444_: *mut leanh::LeanObject,
    mut v_x2_445_: *mut leanh::LeanObject,
    mut v_x3_446_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_map_447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_450_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_map_447_ = leanh::lean_ctor_get(v_toFunctor_439_, 0);
    leanh::lean_inc(v_map_447_);
    leanh::lean_dec_ref(v_toFunctor_439_);
    v___x_448_ = leanh::lean_apply_2(v_f_440_, v_x3_446_, v_x1_444_);
    v___x_449_ = leanh::lean_apply_4(
        v_map_447_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_441_,
        v___x_448_,
    );
    v___x_450_ = leanh::lean_apply_4(
        v_toBind_442_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_449_,
        v___f_443_,
    );
    return v___x_450_;
}
pub unsafe fn l_Std_Slice_foldlM___redArg(
    mut v_inst_452_: *mut leanh::LeanObject,
    mut v_f_453_: *mut leanh::LeanObject,
    mut v_init_454_: *mut leanh::LeanObject,
    mut v_inst_455_: *mut leanh::LeanObject,
    mut v_inst_456_: *mut leanh::LeanObject,
    mut v_s_457_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_467_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_458_ = leanh::lean_ctor_get(v_inst_452_, 0);
    leanh::lean_inc_ref(v_toApplicative_458_);
    v_toBind_459_ = leanh::lean_ctor_get(v_inst_452_, 1);
    leanh::lean_inc(v_toBind_459_);
    leanh::lean_dec_ref(v_inst_452_);
    v_toFunctor_460_ = leanh::lean_ctor_get(v_toApplicative_458_, 0);
    leanh::lean_inc_ref(v_toFunctor_460_);
    v_toPure_461_ = leanh::lean_ctor_get(v_toApplicative_458_, 1);
    leanh::lean_inc(v_toPure_461_);
    leanh::lean_dec_ref(v_toApplicative_458_);
    v___f_462_ = l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___redArg___closed__0;
    v___f_463_ = l_Std_Slice_foldlM___redArg___closed__0;
    v___x_464_ = leanh::lean_apply_1(v_inst_455_, v_s_457_);
    v___f_465_ = leanh::lean_alloc_closure(
        l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___redArg___lam__1
            as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_465_, 0, v_toPure_461_);
    v___f_466_ = leanh::lean_alloc_closure(
        l_Std_Slice_foldlM___redArg___lam__2 as *mut core::ffi::c_void,
        8,
        5,
    );
    leanh::lean_closure_set(v___f_466_, 0, v_toFunctor_460_);
    leanh::lean_closure_set(v___f_466_, 1, v_f_453_);
    leanh::lean_closure_set(v___f_466_, 2, v___f_463_);
    leanh::lean_closure_set(v___f_466_, 3, v_toBind_459_);
    leanh::lean_closure_set(v___f_466_, 4, v___f_465_);
    v___x_467_ = leanh::lean_apply_6(
        v_inst_456_,
        v___f_462_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_464_,
        v_init_454_,
        v___f_466_,
    );
    return v___x_467_;
}
pub unsafe fn l_Std_Slice_foldlM(
    mut v_00_u03b1_468_: *mut leanh::LeanObject,
    mut v_00_u03b3_469_: *mut leanh::LeanObject,
    mut v_00_u03b2_470_: *mut leanh::LeanObject,
    mut v_00_u03b4_471_: *mut leanh::LeanObject,
    mut v_m_472_: *mut leanh::LeanObject,
    mut v_inst_473_: *mut leanh::LeanObject,
    mut v_f_474_: *mut leanh::LeanObject,
    mut v_init_475_: *mut leanh::LeanObject,
    mut v_inst_476_: *mut leanh::LeanObject,
    mut v_inst_477_: *mut leanh::LeanObject,
    mut v_inst_478_: *mut leanh::LeanObject,
    mut v_s_479_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_489_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_480_ = leanh::lean_ctor_get(v_inst_473_, 0);
    leanh::lean_inc_ref(v_toApplicative_480_);
    v_toBind_481_ = leanh::lean_ctor_get(v_inst_473_, 1);
    leanh::lean_inc(v_toBind_481_);
    leanh::lean_dec_ref(v_inst_473_);
    v_toFunctor_482_ = leanh::lean_ctor_get(v_toApplicative_480_, 0);
    leanh::lean_inc_ref(v_toFunctor_482_);
    v_toPure_483_ = leanh::lean_ctor_get(v_toApplicative_480_, 1);
    leanh::lean_inc(v_toPure_483_);
    leanh::lean_dec_ref(v_toApplicative_480_);
    v___f_484_ = l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___redArg___closed__0;
    v___f_485_ = l_Std_Slice_foldlM___redArg___closed__0;
    v___x_486_ = leanh::lean_apply_1(v_inst_476_, v_s_479_);
    v___f_487_ = leanh::lean_alloc_closure(
        l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___redArg___lam__1
            as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_487_, 0, v_toPure_483_);
    v___f_488_ = leanh::lean_alloc_closure(
        l_Std_Slice_foldlM___redArg___lam__2 as *mut core::ffi::c_void,
        8,
        5,
    );
    leanh::lean_closure_set(v___f_488_, 0, v_toFunctor_482_);
    leanh::lean_closure_set(v___f_488_, 1, v_f_474_);
    leanh::lean_closure_set(v___f_488_, 2, v___f_485_);
    leanh::lean_closure_set(v___f_488_, 3, v_toBind_481_);
    leanh::lean_closure_set(v___f_488_, 4, v___f_487_);
    v___x_489_ = leanh::lean_apply_6(
        v_inst_478_,
        v___f_484_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_486_,
        v_init_475_,
        v___f_488_,
    );
    return v___x_489_;
}
pub unsafe fn l_Std_Slice_foldlM___boxed(
    mut v_00_u03b1_490_: *mut leanh::LeanObject,
    mut v_00_u03b3_491_: *mut leanh::LeanObject,
    mut v_00_u03b2_492_: *mut leanh::LeanObject,
    mut v_00_u03b4_493_: *mut leanh::LeanObject,
    mut v_m_494_: *mut leanh::LeanObject,
    mut v_inst_495_: *mut leanh::LeanObject,
    mut v_f_496_: *mut leanh::LeanObject,
    mut v_init_497_: *mut leanh::LeanObject,
    mut v_inst_498_: *mut leanh::LeanObject,
    mut v_inst_499_: *mut leanh::LeanObject,
    mut v_inst_500_: *mut leanh::LeanObject,
    mut v_s_501_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_502_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_502_ = l_Std_Slice_foldlM(
        v_00_u03b1_490_,
        v_00_u03b3_491_,
        v_00_u03b2_492_,
        v_00_u03b4_493_,
        v_m_494_,
        v_inst_495_,
        v_f_496_,
        v_init_497_,
        v_inst_498_,
        v_inst_499_,
        v_inst_500_,
        v_s_501_,
    );
    leanh::lean_dec(v_inst_499_);
    return v_res_502_;
}
pub unsafe fn l_Std_Slice_foldl___redArg___lam__1(
    mut v_f_503_: *mut leanh::LeanObject,
    mut v_x1_504_: *mut leanh::LeanObject,
    mut v_x2_505_: *mut leanh::LeanObject,
    mut v_x3_506_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_508_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_507_ = leanh::lean_apply_2(v_f_503_, v_x3_506_, v_x1_504_);
    v___x_508_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_508_, 0, v___x_507_);
    return v___x_508_;
}
pub unsafe fn l_Std_Slice_foldl___redArg(
    mut v_f_509_: *mut leanh::LeanObject,
    mut v_init_510_: *mut leanh::LeanObject,
    mut v_inst_511_: *mut leanh::LeanObject,
    mut v_inst_512_: *mut leanh::LeanObject,
    mut v_s_513_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_517_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_514_ = l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___redArg___closed__0;
    v___f_515_ = leanh::lean_alloc_closure(
        l_Std_Slice_foldl___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_515_, 0, v_f_509_);
    v___x_516_ = leanh::lean_apply_1(v_inst_511_, v_s_513_);
    v___x_517_ = leanh::lean_apply_6(
        v_inst_512_,
        v___f_514_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_516_,
        v_init_510_,
        v___f_515_,
    );
    return v___x_517_;
}
pub unsafe fn l_Std_Slice_foldl(
    mut v_00_u03b1_518_: *mut leanh::LeanObject,
    mut v_00_u03b3_519_: *mut leanh::LeanObject,
    mut v_00_u03b2_520_: *mut leanh::LeanObject,
    mut v_00_u03b4_521_: *mut leanh::LeanObject,
    mut v_f_522_: *mut leanh::LeanObject,
    mut v_init_523_: *mut leanh::LeanObject,
    mut v_inst_524_: *mut leanh::LeanObject,
    mut v_inst_525_: *mut leanh::LeanObject,
    mut v_inst_526_: *mut leanh::LeanObject,
    mut v_s_527_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_531_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_528_ = l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___redArg___closed__0;
    v___f_529_ = leanh::lean_alloc_closure(
        l_Std_Slice_foldl___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_529_, 0, v_f_522_);
    v___x_530_ = leanh::lean_apply_1(v_inst_524_, v_s_527_);
    v___x_531_ = leanh::lean_apply_6(
        v_inst_526_,
        v___f_528_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_530_,
        v_init_523_,
        v___f_529_,
    );
    return v___x_531_;
}
pub unsafe fn l_Std_Slice_foldl___boxed(
    mut v_00_u03b1_532_: *mut leanh::LeanObject,
    mut v_00_u03b3_533_: *mut leanh::LeanObject,
    mut v_00_u03b2_534_: *mut leanh::LeanObject,
    mut v_00_u03b4_535_: *mut leanh::LeanObject,
    mut v_f_536_: *mut leanh::LeanObject,
    mut v_init_537_: *mut leanh::LeanObject,
    mut v_inst_538_: *mut leanh::LeanObject,
    mut v_inst_539_: *mut leanh::LeanObject,
    mut v_inst_540_: *mut leanh::LeanObject,
    mut v_s_541_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_542_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_542_ = l_Std_Slice_foldl(
        v_00_u03b1_532_,
        v_00_u03b3_533_,
        v_00_u03b2_534_,
        v_00_u03b4_535_,
        v_f_536_,
        v_init_537_,
        v_inst_538_,
        v_inst_539_,
        v_inst_540_,
        v_s_541_,
    );
    leanh::lean_dec(v_inst_539_);
    return v_res_542_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Slice_Operations(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Slice_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_ToIterator(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Loop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Slice_Operations(
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
pub unsafe fn initialize_Init_Data_Slice_Operations(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Slice_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_ToIterator(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Loop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Slice_Operations(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Slice_Operations(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Slice_Operations(builtin);
}