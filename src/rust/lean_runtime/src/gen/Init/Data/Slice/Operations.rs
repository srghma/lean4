// Lean compiler output
// Module: Init.Data.Slice.Operations
// Imports: Init.Data.Slice.Basic Init.Data.Iterators.ToIterator Init.Data.Iterators.Consumers.Loop Init.Data.Iterators.Consumers.Collect
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
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_4, lean_apply_6, lean_box, lean_closure_set,
    lean_ctor_get, lean_ctor_set, lean_ctor_set_tag, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_inc, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_tag,
};
pub static l_Std_Slice_toArray___redArg___closed__0_value: LeanArrayObject<0> = LeanArrayObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Std_Slice_toArray___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Slice_toArray___redArg___closed__0_value) as *mut LeanObject;
pub static l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___redArg___closed__0_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___redArg___closed__0_value
) as *mut LeanObject;
pub static l_Std_Slice_foldlM___redArg___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Slice_foldlM___redArg___lam__1 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Slice_foldlM___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Slice_foldlM___redArg___closed__0_value) as *mut LeanObject;
pub unsafe fn l_Std_Slice_instToIterator___redArg___lam__0(
    mut v_inst_272_: *mut LeanObject,
    mut v_x_273_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_274_: *mut LeanObject = core::ptr::null_mut();
    v___x_274_ = lean_apply_1(v_inst_272_, v_x_273_);
    return v___x_274_;
}
pub unsafe fn l_Std_Slice_instToIterator___redArg(
    mut v_inst_275_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_276_: *mut LeanObject = core::ptr::null_mut();
    v___f_276_ = lean_alloc_closure(
        l_Std_Slice_instToIterator___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_276_, 0, v_inst_275_);
    return v___f_276_;
}
pub unsafe fn l_Std_Slice_instToIterator(
    mut v_00_u03b3_277_: *mut LeanObject,
    mut v_m_278_: *mut LeanObject,
    mut v_00_u03b1_279_: *mut LeanObject,
    mut v_00_u03b2_280_: *mut LeanObject,
    mut v_inst_281_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_282_: *mut LeanObject = core::ptr::null_mut();
    v___f_282_ = lean_alloc_closure(
        l_Std_Slice_instToIterator___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_282_, 0, v_inst_281_);
    return v___f_282_;
}
pub unsafe fn l_Std_Slice_Internal_iter___redArg(
    mut v_inst_283_: *mut LeanObject,
    mut v_s_284_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_285_: *mut LeanObject = core::ptr::null_mut();
    v___x_285_ = lean_apply_1(v_inst_283_, v_s_284_);
    return v___x_285_;
}
pub unsafe fn l_Std_Slice_Internal_iter(
    mut v_00_u03b3_286_: *mut LeanObject,
    mut v_00_u03b1_287_: *mut LeanObject,
    mut v_00_u03b2_288_: *mut LeanObject,
    mut v_inst_289_: *mut LeanObject,
    mut v_s_290_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_291_: *mut LeanObject = core::ptr::null_mut();
    v___x_291_ = lean_apply_1(v_inst_289_, v_s_290_);
    return v___x_291_;
}
pub unsafe fn l_Std_Slice_size___redArg(
    mut v_s_292_: *mut LeanObject,
    mut v_inst_293_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_294_: *mut LeanObject = core::ptr::null_mut();
    v___x_294_ = lean_apply_1(v_inst_293_, v_s_292_);
    return v___x_294_;
}
pub unsafe fn l_Std_Slice_size(
    mut v_00_u03b3_295_: *mut LeanObject,
    mut v_s_296_: *mut LeanObject,
    mut v_inst_297_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_298_: *mut LeanObject = core::ptr::null_mut();
    v___x_298_ = lean_apply_1(v_inst_297_, v_s_296_);
    return v___x_298_;
}
pub unsafe fn l_Std_Slice_toArray___redArg___lam__0(
    mut v_inst_299_: *mut LeanObject,
    mut v_it_300_: *mut LeanObject,
    mut v_acc_301_: *mut LeanObject,
    mut v_recur_302_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_val_303_: *mut LeanObject = core::ptr::null_mut();
    v_val_303_ = lean_apply_1(v_inst_299_, v_it_300_);
    match lean_obj_tag(v_val_303_) {
        0 => {
            let mut v_it_304_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_305_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_306_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_307_: *mut LeanObject = core::ptr::null_mut();
            v_it_304_ = lean_ctor_get(v_val_303_, 0);
            lean_inc(v_it_304_);
            v_out_305_ = lean_ctor_get(v_val_303_, 1);
            lean_inc(v_out_305_);
            lean_dec_ref_known(v_val_303_, 2);
            v___x_306_ = lean_array_push(v_acc_301_, v_out_305_);
            v___x_307_ = lean_apply_3(v_recur_302_, v_it_304_, v___x_306_, lean_box(0));
            return v___x_307_;
        }
        1 => {
            let mut v_it_308_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_309_: *mut LeanObject = core::ptr::null_mut();
            v_it_308_ = lean_ctor_get(v_val_303_, 0);
            lean_inc(v_it_308_);
            lean_dec_ref_known(v_val_303_, 1);
            v___x_309_ = lean_apply_3(v_recur_302_, v_it_308_, v_acc_301_, lean_box(0));
            return v___x_309_;
        }
        _ => {
            lean_dec_ref(v_recur_302_);
            return v_acc_301_;
        }
    }
}
pub unsafe fn l_Std_Slice_toArray___redArg(
    mut v_inst_312_: *mut LeanObject,
    mut v_inst_313_: *mut LeanObject,
    mut v_s_314_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_318_: *mut LeanObject = core::ptr::null_mut();
    v___f_315_ = lean_alloc_closure(
        l_Std_Slice_toArray___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_315_, 0, v_inst_313_);
    v___x_316_ = lean_apply_1(v_inst_312_, v_s_314_);
    v___x_317_ = l_Std_Slice_toArray___redArg___closed__0;
    v___x_318_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_315_, v___x_316_, v___x_317_,
    );
    return v___x_318_;
}
pub unsafe fn l_Std_Slice_toArray(
    mut v_00_u03b3_319_: *mut LeanObject,
    mut v_00_u03b1_320_: *mut LeanObject,
    mut v_00_u03b2_321_: *mut LeanObject,
    mut v_inst_322_: *mut LeanObject,
    mut v_inst_323_: *mut LeanObject,
    mut v_s_324_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_328_: *mut LeanObject = core::ptr::null_mut();
    v___f_325_ = lean_alloc_closure(
        l_Std_Slice_toArray___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_325_, 0, v_inst_323_);
    v___x_326_ = lean_apply_1(v_inst_322_, v_s_324_);
    v___x_327_ = l_Std_Slice_toArray___redArg___closed__0;
    v___x_328_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_325_, v___x_326_, v___x_327_,
    );
    return v___x_328_;
}
pub unsafe fn l_Std_Slice_toList___redArg(
    mut v_inst_329_: *mut LeanObject,
    mut v_inst_330_: *mut LeanObject,
    mut v_s_331_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_336_: *mut LeanObject = core::ptr::null_mut();
    v___f_332_ = lean_alloc_closure(
        l_Std_Slice_toArray___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_332_, 0, v_inst_330_);
    v___x_333_ = lean_apply_1(v_inst_329_, v_s_331_);
    v___x_334_ = l_Std_Slice_toArray___redArg___closed__0;
    v___x_335_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_332_, v___x_333_, v___x_334_,
    );
    v___x_336_ = lean_array_to_list(v___x_335_);
    return v___x_336_;
}
pub unsafe fn l_Std_Slice_toList(
    mut v_00_u03b3_337_: *mut LeanObject,
    mut v_00_u03b1_338_: *mut LeanObject,
    mut v_00_u03b2_339_: *mut LeanObject,
    mut v_inst_340_: *mut LeanObject,
    mut v_inst_341_: *mut LeanObject,
    mut v_s_342_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_347_: *mut LeanObject = core::ptr::null_mut();
    v___f_343_ = lean_alloc_closure(
        l_Std_Slice_toArray___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_343_, 0, v_inst_341_);
    v___x_344_ = lean_apply_1(v_inst_340_, v_s_342_);
    v___x_345_ = l_Std_Slice_toArray___redArg___closed__0;
    v___x_346_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_343_, v___x_344_, v___x_345_,
    );
    v___x_347_ = lean_array_to_list(v___x_346_);
    return v___x_347_;
}
pub unsafe fn l_Std_Slice_toListRev___redArg___lam__0(
    mut v_inst_348_: *mut LeanObject,
    mut v_it_349_: *mut LeanObject,
    mut v_acc_350_: *mut LeanObject,
    mut v_recur_351_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_val_352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_it_353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_out_354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_357_: u8 = 0;
    let mut v___x_359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_362_: u8 = 0;
    let mut v_it_363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_364_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_val_352_ = lean_apply_1(v_inst_348_, v_it_349_);
                match lean_obj_tag(v_val_352_) {
                    0 => {
                        v_it_353_ = lean_ctor_get(v_val_352_, 0);
                        v_out_354_ = lean_ctor_get(v_val_352_, 1);
                        v_isSharedCheck_362_ = (!lean_is_exclusive(v_val_352_)) as u8;
                        if v_isSharedCheck_362_ == 0 {
                            v___x_356_ = v_val_352_;
                            v_isShared_357_ = v_isSharedCheck_362_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_out_354_);
                            lean_inc(v_it_353_);
                            lean_dec(v_val_352_);
                            v___x_356_ = lean_box(0);
                            v_isShared_357_ = v_isSharedCheck_362_;
                            state = 1;
                            continue;
                        }
                    }
                    1 => {
                        v_it_363_ = lean_ctor_get(v_val_352_, 0);
                        lean_inc(v_it_363_);
                        lean_dec_ref_known(v_val_352_, 1);
                        v___x_364_ = lean_apply_3(v_recur_351_, v_it_363_, v_acc_350_, lean_box(0));
                        return v___x_364_;
                    }
                    _ => {
                        lean_dec_ref(v_recur_351_);
                        return v_acc_350_;
                    }
                }
            }
            1 => {
                if v_isShared_357_ == 0 {
                    lean_ctor_set_tag(v___x_356_, 1);
                    lean_ctor_set(v___x_356_, 1, v_acc_350_);
                    lean_ctor_set(v___x_356_, 0, v_out_354_);
                    v___x_359_ = v___x_356_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_361_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_361_, 0, v_out_354_);
                    lean_ctor_set(v_reuseFailAlloc_361_, 1, v_acc_350_);
                    v___x_359_ = v_reuseFailAlloc_361_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_360_ = lean_apply_3(v_recur_351_, v_it_353_, v___x_359_, lean_box(0));
                return v___x_360_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Slice_toListRev___redArg(
    mut v_inst_365_: *mut LeanObject,
    mut v_inst_366_: *mut LeanObject,
    mut v_s_367_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_371_: *mut LeanObject = core::ptr::null_mut();
    v___f_368_ = lean_alloc_closure(
        l_Std_Slice_toListRev___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_368_, 0, v_inst_366_);
    v___x_369_ = lean_apply_1(v_inst_365_, v_s_367_);
    v___x_370_ = lean_box(0);
    v___x_371_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_368_, v___x_369_, v___x_370_,
    );
    return v___x_371_;
}
pub unsafe fn l_Std_Slice_toListRev(
    mut v_00_u03b3_372_: *mut LeanObject,
    mut v_00_u03b1_373_: *mut LeanObject,
    mut v_00_u03b2_374_: *mut LeanObject,
    mut v_inst_375_: *mut LeanObject,
    mut v_inst_376_: *mut LeanObject,
    mut v_s_377_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_381_: *mut LeanObject = core::ptr::null_mut();
    v___f_378_ = lean_alloc_closure(
        l_Std_Slice_toListRev___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_378_, 0, v_inst_376_);
    v___x_379_ = lean_apply_1(v_inst_375_, v_s_377_);
    v___x_380_ = lean_box(0);
    v___x_381_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_378_, v___x_379_, v___x_380_,
    );
    return v___x_381_;
}
pub unsafe fn l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___redArg___lam__0(
    mut v_x_382_: *mut LeanObject,
    mut v_x_383_: *mut LeanObject,
    mut v_f_384_: *mut LeanObject,
    mut v_c_385_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_386_: *mut LeanObject = core::ptr::null_mut();
    v___x_386_ = lean_apply_1(v_f_384_, v_c_385_);
    return v___x_386_;
}
pub unsafe fn l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___redArg___lam__1(
    mut v_toPure_387_: *mut LeanObject,
    mut v_____do__lift_388_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_389_: *mut LeanObject = core::ptr::null_mut();
    v___x_389_ = lean_apply_2(v_toPure_387_, lean_box(0), v_____do__lift_388_);
    return v___x_389_;
}
pub unsafe fn l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___redArg___lam__2(
    mut v_f_390_: *mut LeanObject,
    mut v_toBind_391_: *mut LeanObject,
    mut v___f_392_: *mut LeanObject,
    mut v_x1_393_: *mut LeanObject,
    mut v_x2_394_: *mut LeanObject,
    mut v_x3_395_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_397_: *mut LeanObject = core::ptr::null_mut();
    v___x_396_ = lean_apply_2(v_f_390_, v_x1_393_, v_x3_395_);
    v___x_397_ = lean_apply_4(
        v_toBind_391_,
        lean_box(0),
        lean_box(0),
        v___x_396_,
        v___f_392_,
    );
    return v___x_397_;
}
pub unsafe fn l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___redArg___lam__3(
    mut v_inst_398_: *mut LeanObject,
    mut v_inst_399_: *mut LeanObject,
    mut v_inst_400_: *mut LeanObject,
    mut v___f_401_: *mut LeanObject,
    mut v_00_u03b2_402_: *mut LeanObject,
    mut v_s_403_: *mut LeanObject,
    mut v_init_404_: *mut LeanObject,
    mut v_f_405_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_412_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_406_ = lean_ctor_get(v_inst_398_, 0);
    lean_inc_ref(v_toApplicative_406_);
    v_toBind_407_ = lean_ctor_get(v_inst_398_, 1);
    lean_inc(v_toBind_407_);
    lean_dec_ref(v_inst_398_);
    v_toPure_408_ = lean_ctor_get(v_toApplicative_406_, 1);
    lean_inc(v_toPure_408_);
    lean_dec_ref(v_toApplicative_406_);
    v___x_409_ = lean_apply_1(v_inst_399_, v_s_403_);
    v___f_410_ = lean_alloc_closure(
        l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___redArg___lam__1
            as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_410_, 0, v_toPure_408_);
    v___f_411_ = lean_alloc_closure(
        l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___redArg___lam__2
            as *mut core::ffi::c_void,
        6,
        3,
    );
    lean_closure_set(v___f_411_, 0, v_f_405_);
    lean_closure_set(v___f_411_, 1, v_toBind_407_);
    lean_closure_set(v___f_411_, 2, v___f_410_);
    v___x_412_ = lean_apply_6(
        v_inst_400_,
        v___f_401_,
        lean_box(0),
        lean_box(0),
        v___x_409_,
        v_init_404_,
        v___f_411_,
    );
    return v___x_412_;
}
pub unsafe fn l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___redArg(
    mut v_inst_414_: *mut LeanObject,
    mut v_inst_415_: *mut LeanObject,
    mut v_inst_416_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_418_: *mut LeanObject = core::ptr::null_mut();
    v___f_417_ = l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___redArg___closed__0;
    v___f_418_ = lean_alloc_closure(
        l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___redArg___lam__3
            as *mut core::ffi::c_void,
        8,
        4,
    );
    lean_closure_set(v___f_418_, 0, v_inst_414_);
    lean_closure_set(v___f_418_, 1, v_inst_415_);
    lean_closure_set(v___f_418_, 2, v_inst_416_);
    lean_closure_set(v___f_418_, 3, v___f_417_);
    return v___f_418_;
}
pub unsafe fn l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId(
    mut v_m_419_: *mut LeanObject,
    mut v_00_u03b1_420_: *mut LeanObject,
    mut v_00_u03b3_421_: *mut LeanObject,
    mut v_00_u03b2_422_: *mut LeanObject,
    mut v_inst_423_: *mut LeanObject,
    mut v_inst_424_: *mut LeanObject,
    mut v_inst_425_: *mut LeanObject,
    mut v_inst_426_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_427_: *mut LeanObject = core::ptr::null_mut();
    v___x_427_ = l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___redArg(
        v_inst_423_,
        v_inst_424_,
        v_inst_426_,
    );
    return v___x_427_;
}
pub unsafe fn l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___boxed(
    mut v_m_428_: *mut LeanObject,
    mut v_00_u03b1_429_: *mut LeanObject,
    mut v_00_u03b3_430_: *mut LeanObject,
    mut v_00_u03b2_431_: *mut LeanObject,
    mut v_inst_432_: *mut LeanObject,
    mut v_inst_433_: *mut LeanObject,
    mut v_inst_434_: *mut LeanObject,
    mut v_inst_435_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_436_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_inst_434_);
    return v_res_436_;
}
pub unsafe fn l_Std_Slice_foldlM___redArg___lam__1(
    mut v_a_437_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_438_: *mut LeanObject = core::ptr::null_mut();
    v___x_438_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_438_, 0, v_a_437_);
    return v___x_438_;
}
pub unsafe fn l_Std_Slice_foldlM___redArg___lam__2(
    mut v_toFunctor_439_: *mut LeanObject,
    mut v_f_440_: *mut LeanObject,
    mut v___f_441_: *mut LeanObject,
    mut v_toBind_442_: *mut LeanObject,
    mut v___f_443_: *mut LeanObject,
    mut v_x1_444_: *mut LeanObject,
    mut v_x2_445_: *mut LeanObject,
    mut v_x3_446_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_450_: *mut LeanObject = core::ptr::null_mut();
    v_map_447_ = lean_ctor_get(v_toFunctor_439_, 0);
    lean_inc(v_map_447_);
    lean_dec_ref(v_toFunctor_439_);
    v___x_448_ = lean_apply_2(v_f_440_, v_x3_446_, v_x1_444_);
    v___x_449_ = lean_apply_4(v_map_447_, lean_box(0), lean_box(0), v___f_441_, v___x_448_);
    v___x_450_ = lean_apply_4(
        v_toBind_442_,
        lean_box(0),
        lean_box(0),
        v___x_449_,
        v___f_443_,
    );
    return v___x_450_;
}
pub unsafe fn l_Std_Slice_foldlM___redArg(
    mut v_inst_452_: *mut LeanObject,
    mut v_f_453_: *mut LeanObject,
    mut v_init_454_: *mut LeanObject,
    mut v_inst_455_: *mut LeanObject,
    mut v_inst_456_: *mut LeanObject,
    mut v_s_457_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_467_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_458_ = lean_ctor_get(v_inst_452_, 0);
    lean_inc_ref(v_toApplicative_458_);
    v_toBind_459_ = lean_ctor_get(v_inst_452_, 1);
    lean_inc(v_toBind_459_);
    lean_dec_ref(v_inst_452_);
    v_toFunctor_460_ = lean_ctor_get(v_toApplicative_458_, 0);
    lean_inc_ref(v_toFunctor_460_);
    v_toPure_461_ = lean_ctor_get(v_toApplicative_458_, 1);
    lean_inc(v_toPure_461_);
    lean_dec_ref(v_toApplicative_458_);
    v___f_462_ = l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___redArg___closed__0;
    v___f_463_ = l_Std_Slice_foldlM___redArg___closed__0;
    v___x_464_ = lean_apply_1(v_inst_455_, v_s_457_);
    v___f_465_ = lean_alloc_closure(
        l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___redArg___lam__1
            as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_465_, 0, v_toPure_461_);
    v___f_466_ = lean_alloc_closure(
        l_Std_Slice_foldlM___redArg___lam__2 as *mut core::ffi::c_void,
        8,
        5,
    );
    lean_closure_set(v___f_466_, 0, v_toFunctor_460_);
    lean_closure_set(v___f_466_, 1, v_f_453_);
    lean_closure_set(v___f_466_, 2, v___f_463_);
    lean_closure_set(v___f_466_, 3, v_toBind_459_);
    lean_closure_set(v___f_466_, 4, v___f_465_);
    v___x_467_ = lean_apply_6(
        v_inst_456_,
        v___f_462_,
        lean_box(0),
        lean_box(0),
        v___x_464_,
        v_init_454_,
        v___f_466_,
    );
    return v___x_467_;
}
pub unsafe fn l_Std_Slice_foldlM(
    mut v_00_u03b1_468_: *mut LeanObject,
    mut v_00_u03b3_469_: *mut LeanObject,
    mut v_00_u03b2_470_: *mut LeanObject,
    mut v_00_u03b4_471_: *mut LeanObject,
    mut v_m_472_: *mut LeanObject,
    mut v_inst_473_: *mut LeanObject,
    mut v_f_474_: *mut LeanObject,
    mut v_init_475_: *mut LeanObject,
    mut v_inst_476_: *mut LeanObject,
    mut v_inst_477_: *mut LeanObject,
    mut v_inst_478_: *mut LeanObject,
    mut v_s_479_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_489_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_480_ = lean_ctor_get(v_inst_473_, 0);
    lean_inc_ref(v_toApplicative_480_);
    v_toBind_481_ = lean_ctor_get(v_inst_473_, 1);
    lean_inc(v_toBind_481_);
    lean_dec_ref(v_inst_473_);
    v_toFunctor_482_ = lean_ctor_get(v_toApplicative_480_, 0);
    lean_inc_ref(v_toFunctor_482_);
    v_toPure_483_ = lean_ctor_get(v_toApplicative_480_, 1);
    lean_inc(v_toPure_483_);
    lean_dec_ref(v_toApplicative_480_);
    v___f_484_ = l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___redArg___closed__0;
    v___f_485_ = l_Std_Slice_foldlM___redArg___closed__0;
    v___x_486_ = lean_apply_1(v_inst_476_, v_s_479_);
    v___f_487_ = lean_alloc_closure(
        l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___redArg___lam__1
            as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_487_, 0, v_toPure_483_);
    v___f_488_ = lean_alloc_closure(
        l_Std_Slice_foldlM___redArg___lam__2 as *mut core::ffi::c_void,
        8,
        5,
    );
    lean_closure_set(v___f_488_, 0, v_toFunctor_482_);
    lean_closure_set(v___f_488_, 1, v_f_474_);
    lean_closure_set(v___f_488_, 2, v___f_485_);
    lean_closure_set(v___f_488_, 3, v_toBind_481_);
    lean_closure_set(v___f_488_, 4, v___f_487_);
    v___x_489_ = lean_apply_6(
        v_inst_478_,
        v___f_484_,
        lean_box(0),
        lean_box(0),
        v___x_486_,
        v_init_475_,
        v___f_488_,
    );
    return v___x_489_;
}
pub unsafe fn l_Std_Slice_foldlM___boxed(
    mut v_00_u03b1_490_: *mut LeanObject,
    mut v_00_u03b3_491_: *mut LeanObject,
    mut v_00_u03b2_492_: *mut LeanObject,
    mut v_00_u03b4_493_: *mut LeanObject,
    mut v_m_494_: *mut LeanObject,
    mut v_inst_495_: *mut LeanObject,
    mut v_f_496_: *mut LeanObject,
    mut v_init_497_: *mut LeanObject,
    mut v_inst_498_: *mut LeanObject,
    mut v_inst_499_: *mut LeanObject,
    mut v_inst_500_: *mut LeanObject,
    mut v_s_501_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_502_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_inst_499_);
    return v_res_502_;
}
pub unsafe fn l_Std_Slice_foldl___redArg___lam__1(
    mut v_f_503_: *mut LeanObject,
    mut v_x1_504_: *mut LeanObject,
    mut v_x2_505_: *mut LeanObject,
    mut v_x3_506_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_508_: *mut LeanObject = core::ptr::null_mut();
    v___x_507_ = lean_apply_2(v_f_503_, v_x3_506_, v_x1_504_);
    v___x_508_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_508_, 0, v___x_507_);
    return v___x_508_;
}
pub unsafe fn l_Std_Slice_foldl___redArg(
    mut v_f_509_: *mut LeanObject,
    mut v_init_510_: *mut LeanObject,
    mut v_inst_511_: *mut LeanObject,
    mut v_inst_512_: *mut LeanObject,
    mut v_s_513_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_517_: *mut LeanObject = core::ptr::null_mut();
    v___f_514_ = l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___redArg___closed__0;
    v___f_515_ = lean_alloc_closure(
        l_Std_Slice_foldl___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_515_, 0, v_f_509_);
    v___x_516_ = lean_apply_1(v_inst_511_, v_s_513_);
    v___x_517_ = lean_apply_6(
        v_inst_512_,
        v___f_514_,
        lean_box(0),
        lean_box(0),
        v___x_516_,
        v_init_510_,
        v___f_515_,
    );
    return v___x_517_;
}
pub unsafe fn l_Std_Slice_foldl(
    mut v_00_u03b1_518_: *mut LeanObject,
    mut v_00_u03b3_519_: *mut LeanObject,
    mut v_00_u03b2_520_: *mut LeanObject,
    mut v_00_u03b4_521_: *mut LeanObject,
    mut v_f_522_: *mut LeanObject,
    mut v_init_523_: *mut LeanObject,
    mut v_inst_524_: *mut LeanObject,
    mut v_inst_525_: *mut LeanObject,
    mut v_inst_526_: *mut LeanObject,
    mut v_s_527_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_531_: *mut LeanObject = core::ptr::null_mut();
    v___f_528_ = l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___redArg___closed__0;
    v___f_529_ = lean_alloc_closure(
        l_Std_Slice_foldl___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_529_, 0, v_f_522_);
    v___x_530_ = lean_apply_1(v_inst_524_, v_s_527_);
    v___x_531_ = lean_apply_6(
        v_inst_526_,
        v___f_528_,
        lean_box(0),
        lean_box(0),
        v___x_530_,
        v_init_523_,
        v___f_529_,
    );
    return v___x_531_;
}
pub unsafe fn l_Std_Slice_foldl___boxed(
    mut v_00_u03b1_532_: *mut LeanObject,
    mut v_00_u03b3_533_: *mut LeanObject,
    mut v_00_u03b2_534_: *mut LeanObject,
    mut v_00_u03b4_535_: *mut LeanObject,
    mut v_f_536_: *mut LeanObject,
    mut v_init_537_: *mut LeanObject,
    mut v_inst_538_: *mut LeanObject,
    mut v_inst_539_: *mut LeanObject,
    mut v_inst_540_: *mut LeanObject,
    mut v_s_541_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_542_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_inst_539_);
    return v_res_542_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Slice_Operations(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Slice_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_ToIterator(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Loop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Slice_Operations(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Slice_Operations(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Slice_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_ToIterator(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Loop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Slice_Operations(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Slice_Operations(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Slice_Operations(builtin);
}
