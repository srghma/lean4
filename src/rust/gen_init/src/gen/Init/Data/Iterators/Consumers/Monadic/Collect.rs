// Lean compiler output
// Module: Init.Data.Iterators.Consumers.Monadic.Collect
// Imports: Init.Data.Iterators.Consumers.Monadic.Partial Init.Data.Iterators.Consumers.Monadic.Total Init.WFExtrinsicFix Init.Ext
use crate::ffi::{lean_array_push, lean_array_to_list};
use crate::r#gen::Init::Data::Iterators::Consumers::Monadic::Partial::{
    initialize_Init_Data_Iterators_Consumers_Monadic_Partial,
    runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Partial,
};
use crate::r#gen::Init::Data::Iterators::Consumers::Monadic::Total::{
    initialize_Init_Data_Iterators_Consumers_Monadic_Total,
    runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Total,
};
use crate::r#gen::Init::Ext::{initialize_Init_Ext, runtime_initialize_Init_Ext};
use crate::r#gen::Init::WFExtrinsicFix::{
    initialize_Init_WFExtrinsicFix,
    l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg,
    runtime_initialize_Init_WFExtrinsicFix,
};
pub static l_Std_IterM_toArray___redArg___closed__0_value: leanh::LeanArrayObject<0> =
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
static mut l_Std_IterM_toArray___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_IterM_toArray___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_IterM_toList___redArg___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_IterM_toList___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_IterM_toList___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_IterM_toList___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Std_IterM_toArray_go___redArg___lam__0(
    mut v_acc_310_: *mut leanh::LeanObject,
    mut v_recur_311_: *mut leanh::LeanObject,
    mut v_toPure_312_: *mut leanh::LeanObject,
    mut v_____do__lift_313_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_____do__lift_313_) {
        0 => {
            let mut v_it_314_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_315_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_316_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_317_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_toPure_312_);
            v_it_314_ = leanh::lean_ctor_get(v_____do__lift_313_, 0);
            leanh::lean_inc(v_it_314_);
            v_out_315_ = leanh::lean_ctor_get(v_____do__lift_313_, 1);
            leanh::lean_inc(v_out_315_);
            leanh::lean_dec_ref_known(v_____do__lift_313_, 2);
            v___x_316_ = lean_array_push(v_acc_310_, v_out_315_);
            v___x_317_ = leanh::lean_apply_3(
                v_recur_311_,
                v_it_314_,
                v___x_316_,
                leanh::lean_box(0),
            );
            return v___x_317_;
        }
        1 => {
            let mut v_it_318_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_319_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_toPure_312_);
            v_it_318_ = leanh::lean_ctor_get(v_____do__lift_313_, 0);
            leanh::lean_inc(v_it_318_);
            leanh::lean_dec_ref_known(v_____do__lift_313_, 1);
            v___x_319_ = leanh::lean_apply_3(
                v_recur_311_,
                v_it_318_,
                v_acc_310_,
                leanh::lean_box(0),
            );
            return v___x_319_;
        }
        _ => {
            let mut v___x_320_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_recur_311_);
            v___x_320_ =
                leanh::lean_apply_2(v_toPure_312_, leanh::lean_box(0), v_acc_310_);
            return v___x_320_;
        }
    }
}
pub unsafe fn l_Std_IterM_toArray_go___redArg___lam__1(
    mut v_toPure_321_: *mut leanh::LeanObject,
    mut v_inst_322_: *mut leanh::LeanObject,
    mut v_toBind_323_: *mut leanh::LeanObject,
    mut v_it_324_: *mut leanh::LeanObject,
    mut v_acc_325_: *mut leanh::LeanObject,
    mut v_recur_326_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_329_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_327_ = leanh::lean_alloc_closure(
        l_Std_IterM_toArray_go___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_327_, 0, v_acc_325_);
    leanh::lean_closure_set(v___f_327_, 1, v_recur_326_);
    leanh::lean_closure_set(v___f_327_, 2, v_toPure_321_);
    v___x_328_ = leanh::lean_apply_1(v_inst_322_, v_it_324_);
    v___x_329_ = leanh::lean_apply_4(
        v_toBind_323_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_328_,
        v___f_327_,
    );
    return v___x_329_;
}
pub unsafe fn l_Std_IterM_toArray_go___redArg(
    mut v_inst_330_: *mut leanh::LeanObject,
    mut v_inst_331_: *mut leanh::LeanObject,
    mut v_it_332_: *mut leanh::LeanObject,
    mut v_acc_333_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_338_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_334_ = leanh::lean_ctor_get(v_inst_330_, 0);
    leanh::lean_inc_ref(v_toApplicative_334_);
    v_toBind_335_ = leanh::lean_ctor_get(v_inst_330_, 1);
    leanh::lean_inc(v_toBind_335_);
    leanh::lean_dec_ref(v_inst_330_);
    v_toPure_336_ = leanh::lean_ctor_get(v_toApplicative_334_, 1);
    leanh::lean_inc(v_toPure_336_);
    leanh::lean_dec_ref(v_toApplicative_334_);
    v___f_337_ = leanh::lean_alloc_closure(
        l_Std_IterM_toArray_go___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    leanh::lean_closure_set(v___f_337_, 0, v_toPure_336_);
    leanh::lean_closure_set(v___f_337_, 1, v_inst_331_);
    leanh::lean_closure_set(v___f_337_, 2, v_toBind_335_);
    v___x_338_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_337_, v_it_332_, v_acc_333_,
    );
    return v___x_338_;
}
pub unsafe fn l_Std_IterM_toArray_go(
    mut v_00_u03b1_339_: *mut leanh::LeanObject,
    mut v_00_u03b2_340_: *mut leanh::LeanObject,
    mut v_m_341_: *mut leanh::LeanObject,
    mut v_inst_342_: *mut leanh::LeanObject,
    mut v_inst_343_: *mut leanh::LeanObject,
    mut v_it_344_: *mut leanh::LeanObject,
    mut v_acc_345_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_350_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_346_ = leanh::lean_ctor_get(v_inst_342_, 0);
    leanh::lean_inc_ref(v_toApplicative_346_);
    v_toBind_347_ = leanh::lean_ctor_get(v_inst_342_, 1);
    leanh::lean_inc(v_toBind_347_);
    leanh::lean_dec_ref(v_inst_342_);
    v_toPure_348_ = leanh::lean_ctor_get(v_toApplicative_346_, 1);
    leanh::lean_inc(v_toPure_348_);
    leanh::lean_dec_ref(v_toApplicative_346_);
    v___f_349_ = leanh::lean_alloc_closure(
        l_Std_IterM_toArray_go___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    leanh::lean_closure_set(v___f_349_, 0, v_toPure_348_);
    leanh::lean_closure_set(v___f_349_, 1, v_inst_343_);
    leanh::lean_closure_set(v___f_349_, 2, v_toBind_347_);
    v___x_350_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_349_, v_it_344_, v_acc_345_,
    );
    return v___x_350_;
}
pub unsafe fn l_Std_IterM_toArray___redArg(
    mut v_inst_353_: *mut leanh::LeanObject,
    mut v_inst_354_: *mut leanh::LeanObject,
    mut v_it_355_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_361_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_356_ = leanh::lean_ctor_get(v_inst_353_, 0);
    leanh::lean_inc_ref(v_toApplicative_356_);
    v_toBind_357_ = leanh::lean_ctor_get(v_inst_353_, 1);
    leanh::lean_inc(v_toBind_357_);
    leanh::lean_dec_ref(v_inst_353_);
    v_toPure_358_ = leanh::lean_ctor_get(v_toApplicative_356_, 1);
    leanh::lean_inc(v_toPure_358_);
    leanh::lean_dec_ref(v_toApplicative_356_);
    v___x_359_ = l_Std_IterM_toArray___redArg___closed__0;
    v___f_360_ = leanh::lean_alloc_closure(
        l_Std_IterM_toArray_go___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    leanh::lean_closure_set(v___f_360_, 0, v_toPure_358_);
    leanh::lean_closure_set(v___f_360_, 1, v_inst_354_);
    leanh::lean_closure_set(v___f_360_, 2, v_toBind_357_);
    v___x_361_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_360_, v_it_355_, v___x_359_,
    );
    return v___x_361_;
}
pub unsafe fn l_Std_IterM_toArray(
    mut v_00_u03b1_362_: *mut leanh::LeanObject,
    mut v_00_u03b2_363_: *mut leanh::LeanObject,
    mut v_m_364_: *mut leanh::LeanObject,
    mut v_inst_365_: *mut leanh::LeanObject,
    mut v_inst_366_: *mut leanh::LeanObject,
    mut v_it_367_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_373_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_368_ = leanh::lean_ctor_get(v_inst_365_, 0);
    leanh::lean_inc_ref(v_toApplicative_368_);
    v_toBind_369_ = leanh::lean_ctor_get(v_inst_365_, 1);
    leanh::lean_inc(v_toBind_369_);
    leanh::lean_dec_ref(v_inst_365_);
    v_toPure_370_ = leanh::lean_ctor_get(v_toApplicative_368_, 1);
    leanh::lean_inc(v_toPure_370_);
    leanh::lean_dec_ref(v_toApplicative_368_);
    v___x_371_ = l_Std_IterM_toArray___redArg___closed__0;
    v___f_372_ = leanh::lean_alloc_closure(
        l_Std_IterM_toArray_go___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    leanh::lean_closure_set(v___f_372_, 0, v_toPure_370_);
    leanh::lean_closure_set(v___f_372_, 1, v_inst_366_);
    leanh::lean_closure_set(v___f_372_, 2, v_toBind_369_);
    v___x_373_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_372_, v_it_367_, v___x_371_,
    );
    return v___x_373_;
}
pub unsafe fn l_Std_IterM_Partial_toArray___redArg(
    mut v_inst_374_: *mut leanh::LeanObject,
    mut v_inst_375_: *mut leanh::LeanObject,
    mut v_it_376_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_382_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_377_ = leanh::lean_ctor_get(v_inst_374_, 0);
    leanh::lean_inc_ref(v_toApplicative_377_);
    v_toBind_378_ = leanh::lean_ctor_get(v_inst_374_, 1);
    leanh::lean_inc(v_toBind_378_);
    leanh::lean_dec_ref(v_inst_374_);
    v_toPure_379_ = leanh::lean_ctor_get(v_toApplicative_377_, 1);
    leanh::lean_inc(v_toPure_379_);
    leanh::lean_dec_ref(v_toApplicative_377_);
    v___x_380_ = l_Std_IterM_toArray___redArg___closed__0;
    v___f_381_ = leanh::lean_alloc_closure(
        l_Std_IterM_toArray_go___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    leanh::lean_closure_set(v___f_381_, 0, v_toPure_379_);
    leanh::lean_closure_set(v___f_381_, 1, v_inst_375_);
    leanh::lean_closure_set(v___f_381_, 2, v_toBind_378_);
    v___x_382_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_381_, v_it_376_, v___x_380_,
    );
    return v___x_382_;
}
pub unsafe fn l_Std_IterM_Partial_toArray(
    mut v_00_u03b1_383_: *mut leanh::LeanObject,
    mut v_m_384_: *mut leanh::LeanObject,
    mut v_00_u03b2_385_: *mut leanh::LeanObject,
    mut v_inst_386_: *mut leanh::LeanObject,
    mut v_inst_387_: *mut leanh::LeanObject,
    mut v_it_388_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_394_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_389_ = leanh::lean_ctor_get(v_inst_386_, 0);
    leanh::lean_inc_ref(v_toApplicative_389_);
    v_toBind_390_ = leanh::lean_ctor_get(v_inst_386_, 1);
    leanh::lean_inc(v_toBind_390_);
    leanh::lean_dec_ref(v_inst_386_);
    v_toPure_391_ = leanh::lean_ctor_get(v_toApplicative_389_, 1);
    leanh::lean_inc(v_toPure_391_);
    leanh::lean_dec_ref(v_toApplicative_389_);
    v___x_392_ = l_Std_IterM_toArray___redArg___closed__0;
    v___f_393_ = leanh::lean_alloc_closure(
        l_Std_IterM_toArray_go___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    leanh::lean_closure_set(v___f_393_, 0, v_toPure_391_);
    leanh::lean_closure_set(v___f_393_, 1, v_inst_387_);
    leanh::lean_closure_set(v___f_393_, 2, v_toBind_390_);
    v___x_394_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_393_, v_it_388_, v___x_392_,
    );
    return v___x_394_;
}
pub unsafe fn l_Std_IterM_Total_toArray___redArg(
    mut v_inst_395_: *mut leanh::LeanObject,
    mut v_inst_396_: *mut leanh::LeanObject,
    mut v_it_397_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_403_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_398_ = leanh::lean_ctor_get(v_inst_395_, 0);
    leanh::lean_inc_ref(v_toApplicative_398_);
    v_toBind_399_ = leanh::lean_ctor_get(v_inst_395_, 1);
    leanh::lean_inc(v_toBind_399_);
    leanh::lean_dec_ref(v_inst_395_);
    v_toPure_400_ = leanh::lean_ctor_get(v_toApplicative_398_, 1);
    leanh::lean_inc(v_toPure_400_);
    leanh::lean_dec_ref(v_toApplicative_398_);
    v___x_401_ = l_Std_IterM_toArray___redArg___closed__0;
    v___f_402_ = leanh::lean_alloc_closure(
        l_Std_IterM_toArray_go___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    leanh::lean_closure_set(v___f_402_, 0, v_toPure_400_);
    leanh::lean_closure_set(v___f_402_, 1, v_inst_396_);
    leanh::lean_closure_set(v___f_402_, 2, v_toBind_399_);
    v___x_403_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_402_, v_it_397_, v___x_401_,
    );
    return v___x_403_;
}
pub unsafe fn l_Std_IterM_Total_toArray(
    mut v_00_u03b1_404_: *mut leanh::LeanObject,
    mut v_m_405_: *mut leanh::LeanObject,
    mut v_00_u03b2_406_: *mut leanh::LeanObject,
    mut v_inst_407_: *mut leanh::LeanObject,
    mut v_inst_408_: *mut leanh::LeanObject,
    mut v_inst_409_: *mut leanh::LeanObject,
    mut v_it_410_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_416_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_411_ = leanh::lean_ctor_get(v_inst_407_, 0);
    leanh::lean_inc_ref(v_toApplicative_411_);
    v_toBind_412_ = leanh::lean_ctor_get(v_inst_407_, 1);
    leanh::lean_inc(v_toBind_412_);
    leanh::lean_dec_ref(v_inst_407_);
    v_toPure_413_ = leanh::lean_ctor_get(v_toApplicative_411_, 1);
    leanh::lean_inc(v_toPure_413_);
    leanh::lean_dec_ref(v_toApplicative_411_);
    v___x_414_ = l_Std_IterM_toArray___redArg___closed__0;
    v___f_415_ = leanh::lean_alloc_closure(
        l_Std_IterM_toArray_go___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    leanh::lean_closure_set(v___f_415_, 0, v_toPure_413_);
    leanh::lean_closure_set(v___f_415_, 1, v_inst_408_);
    leanh::lean_closure_set(v___f_415_, 2, v_toBind_412_);
    v___x_416_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_415_, v_it_410_, v___x_414_,
    );
    return v___x_416_;
}
pub unsafe fn l_Std_IterM_toListRev_go___redArg___lam__0(
    mut v_acc_417_: *mut leanh::LeanObject,
    mut v_recur_418_: *mut leanh::LeanObject,
    mut v_toPure_419_: *mut leanh::LeanObject,
    mut v_____do__lift_420_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_it_421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_425_: u8 = 0;
    let mut v___x_427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_430_: u8 = 0;
    let mut v_it_431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_____do__lift_420_) {
                0 => {
                    leanh::lean_dec(v_toPure_419_);
                    v_it_421_ = leanh::lean_ctor_get(v_____do__lift_420_, 0);
                    v_out_422_ = leanh::lean_ctor_get(v_____do__lift_420_, 1);
                    v_isSharedCheck_430_ =
                        (!leanh::lean_is_exclusive(v_____do__lift_420_)) as u8;
                    if v_isSharedCheck_430_ == 0 {
                        v___x_424_ = v_____do__lift_420_;
                        v_isShared_425_ = v_isSharedCheck_430_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_out_422_);
                        leanh::lean_inc(v_it_421_);
                        leanh::lean_dec(v_____do__lift_420_);
                        v___x_424_ = leanh::lean_box(0);
                        v_isShared_425_ = v_isSharedCheck_430_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    leanh::lean_dec(v_toPure_419_);
                    v_it_431_ = leanh::lean_ctor_get(v_____do__lift_420_, 0);
                    leanh::lean_inc(v_it_431_);
                    leanh::lean_dec_ref_known(v_____do__lift_420_, 1);
                    v___x_432_ = leanh::lean_apply_3(
                        v_recur_418_,
                        v_it_431_,
                        v_acc_417_,
                        leanh::lean_box(0),
                    );
                    return v___x_432_;
                }
                _ => {
                    leanh::lean_dec(v_recur_418_);
                    v___x_433_ = leanh::lean_apply_2(
                        v_toPure_419_,
                        leanh::lean_box(0),
                        v_acc_417_,
                    );
                    return v___x_433_;
                }
            },
            1 => {
                if v_isShared_425_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_424_, 1);
                    leanh::lean_ctor_set(v___x_424_, 1, v_acc_417_);
                    leanh::lean_ctor_set(v___x_424_, 0, v_out_422_);
                    v___x_427_ = v___x_424_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_429_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_429_, 0, v_out_422_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_429_, 1, v_acc_417_);
                    v___x_427_ = v_reuseFailAlloc_429_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_428_ = leanh::lean_apply_3(
                    v_recur_418_,
                    v_it_421_,
                    v___x_427_,
                    leanh::lean_box(0),
                );
                return v___x_428_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_IterM_toListRev_go___redArg___lam__1(
    mut v_toPure_434_: *mut leanh::LeanObject,
    mut v_inst_435_: *mut leanh::LeanObject,
    mut v_toBind_436_: *mut leanh::LeanObject,
    mut v_it_437_: *mut leanh::LeanObject,
    mut v_acc_438_: *mut leanh::LeanObject,
    mut v_recur_439_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_442_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_440_ = leanh::lean_alloc_closure(
        l_Std_IterM_toListRev_go___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_440_, 0, v_acc_438_);
    leanh::lean_closure_set(v___f_440_, 1, v_recur_439_);
    leanh::lean_closure_set(v___f_440_, 2, v_toPure_434_);
    v___x_441_ = leanh::lean_apply_1(v_inst_435_, v_it_437_);
    v___x_442_ = leanh::lean_apply_4(
        v_toBind_436_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_441_,
        v___f_440_,
    );
    return v___x_442_;
}
pub unsafe fn l_Std_IterM_toListRev_go___redArg(
    mut v_inst_443_: *mut leanh::LeanObject,
    mut v_inst_444_: *mut leanh::LeanObject,
    mut v_it_445_: *mut leanh::LeanObject,
    mut v_acc_446_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_451_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_447_ = leanh::lean_ctor_get(v_inst_443_, 0);
    leanh::lean_inc_ref(v_toApplicative_447_);
    v_toBind_448_ = leanh::lean_ctor_get(v_inst_443_, 1);
    leanh::lean_inc(v_toBind_448_);
    leanh::lean_dec_ref(v_inst_443_);
    v_toPure_449_ = leanh::lean_ctor_get(v_toApplicative_447_, 1);
    leanh::lean_inc(v_toPure_449_);
    leanh::lean_dec_ref(v_toApplicative_447_);
    v___f_450_ = leanh::lean_alloc_closure(
        l_Std_IterM_toListRev_go___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    leanh::lean_closure_set(v___f_450_, 0, v_toPure_449_);
    leanh::lean_closure_set(v___f_450_, 1, v_inst_444_);
    leanh::lean_closure_set(v___f_450_, 2, v_toBind_448_);
    v___x_451_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_450_, v_it_445_, v_acc_446_,
    );
    return v___x_451_;
}
pub unsafe fn l_Std_IterM_toListRev_go(
    mut v_00_u03b1_452_: *mut leanh::LeanObject,
    mut v_m_453_: *mut leanh::LeanObject,
    mut v_inst_454_: *mut leanh::LeanObject,
    mut v_00_u03b2_455_: *mut leanh::LeanObject,
    mut v_inst_456_: *mut leanh::LeanObject,
    mut v_it_457_: *mut leanh::LeanObject,
    mut v_acc_458_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_463_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_459_ = leanh::lean_ctor_get(v_inst_454_, 0);
    leanh::lean_inc_ref(v_toApplicative_459_);
    v_toBind_460_ = leanh::lean_ctor_get(v_inst_454_, 1);
    leanh::lean_inc(v_toBind_460_);
    leanh::lean_dec_ref(v_inst_454_);
    v_toPure_461_ = leanh::lean_ctor_get(v_toApplicative_459_, 1);
    leanh::lean_inc(v_toPure_461_);
    leanh::lean_dec_ref(v_toApplicative_459_);
    v___f_462_ = leanh::lean_alloc_closure(
        l_Std_IterM_toListRev_go___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    leanh::lean_closure_set(v___f_462_, 0, v_toPure_461_);
    leanh::lean_closure_set(v___f_462_, 1, v_inst_456_);
    leanh::lean_closure_set(v___f_462_, 2, v_toBind_460_);
    v___x_463_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_462_, v_it_457_, v_acc_458_,
    );
    return v___x_463_;
}
pub unsafe fn l_Std_IterM_toListRev___redArg(
    mut v_inst_464_: *mut leanh::LeanObject,
    mut v_inst_465_: *mut leanh::LeanObject,
    mut v_it_466_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_472_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_467_ = leanh::lean_ctor_get(v_inst_464_, 0);
    leanh::lean_inc_ref(v_toApplicative_467_);
    v_toBind_468_ = leanh::lean_ctor_get(v_inst_464_, 1);
    leanh::lean_inc(v_toBind_468_);
    leanh::lean_dec_ref(v_inst_464_);
    v_toPure_469_ = leanh::lean_ctor_get(v_toApplicative_467_, 1);
    leanh::lean_inc(v_toPure_469_);
    leanh::lean_dec_ref(v_toApplicative_467_);
    v___x_470_ = leanh::lean_box(0);
    v___f_471_ = leanh::lean_alloc_closure(
        l_Std_IterM_toListRev_go___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    leanh::lean_closure_set(v___f_471_, 0, v_toPure_469_);
    leanh::lean_closure_set(v___f_471_, 1, v_inst_465_);
    leanh::lean_closure_set(v___f_471_, 2, v_toBind_468_);
    v___x_472_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_471_, v_it_466_, v___x_470_,
    );
    return v___x_472_;
}
pub unsafe fn l_Std_IterM_toListRev(
    mut v_00_u03b1_473_: *mut leanh::LeanObject,
    mut v_m_474_: *mut leanh::LeanObject,
    mut v_inst_475_: *mut leanh::LeanObject,
    mut v_00_u03b2_476_: *mut leanh::LeanObject,
    mut v_inst_477_: *mut leanh::LeanObject,
    mut v_it_478_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_484_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_479_ = leanh::lean_ctor_get(v_inst_475_, 0);
    leanh::lean_inc_ref(v_toApplicative_479_);
    v_toBind_480_ = leanh::lean_ctor_get(v_inst_475_, 1);
    leanh::lean_inc(v_toBind_480_);
    leanh::lean_dec_ref(v_inst_475_);
    v_toPure_481_ = leanh::lean_ctor_get(v_toApplicative_479_, 1);
    leanh::lean_inc(v_toPure_481_);
    leanh::lean_dec_ref(v_toApplicative_479_);
    v___x_482_ = leanh::lean_box(0);
    v___f_483_ = leanh::lean_alloc_closure(
        l_Std_IterM_toListRev_go___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    leanh::lean_closure_set(v___f_483_, 0, v_toPure_481_);
    leanh::lean_closure_set(v___f_483_, 1, v_inst_477_);
    leanh::lean_closure_set(v___f_483_, 2, v_toBind_480_);
    v___x_484_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_483_, v_it_478_, v___x_482_,
    );
    return v___x_484_;
}
pub unsafe fn l_Std_IterM_Partial_toListRev___redArg(
    mut v_inst_485_: *mut leanh::LeanObject,
    mut v_inst_486_: *mut leanh::LeanObject,
    mut v_it_487_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_493_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_488_ = leanh::lean_ctor_get(v_inst_485_, 0);
    leanh::lean_inc_ref(v_toApplicative_488_);
    v_toBind_489_ = leanh::lean_ctor_get(v_inst_485_, 1);
    leanh::lean_inc(v_toBind_489_);
    leanh::lean_dec_ref(v_inst_485_);
    v_toPure_490_ = leanh::lean_ctor_get(v_toApplicative_488_, 1);
    leanh::lean_inc(v_toPure_490_);
    leanh::lean_dec_ref(v_toApplicative_488_);
    v___x_491_ = leanh::lean_box(0);
    v___f_492_ = leanh::lean_alloc_closure(
        l_Std_IterM_toListRev_go___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    leanh::lean_closure_set(v___f_492_, 0, v_toPure_490_);
    leanh::lean_closure_set(v___f_492_, 1, v_inst_486_);
    leanh::lean_closure_set(v___f_492_, 2, v_toBind_489_);
    v___x_493_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_492_, v_it_487_, v___x_491_,
    );
    return v___x_493_;
}
pub unsafe fn l_Std_IterM_Partial_toListRev(
    mut v_00_u03b1_494_: *mut leanh::LeanObject,
    mut v_m_495_: *mut leanh::LeanObject,
    mut v_inst_496_: *mut leanh::LeanObject,
    mut v_00_u03b2_497_: *mut leanh::LeanObject,
    mut v_inst_498_: *mut leanh::LeanObject,
    mut v_it_499_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_505_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_500_ = leanh::lean_ctor_get(v_inst_496_, 0);
    leanh::lean_inc_ref(v_toApplicative_500_);
    v_toBind_501_ = leanh::lean_ctor_get(v_inst_496_, 1);
    leanh::lean_inc(v_toBind_501_);
    leanh::lean_dec_ref(v_inst_496_);
    v_toPure_502_ = leanh::lean_ctor_get(v_toApplicative_500_, 1);
    leanh::lean_inc(v_toPure_502_);
    leanh::lean_dec_ref(v_toApplicative_500_);
    v___x_503_ = leanh::lean_box(0);
    v___f_504_ = leanh::lean_alloc_closure(
        l_Std_IterM_toListRev_go___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    leanh::lean_closure_set(v___f_504_, 0, v_toPure_502_);
    leanh::lean_closure_set(v___f_504_, 1, v_inst_498_);
    leanh::lean_closure_set(v___f_504_, 2, v_toBind_501_);
    v___x_505_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_504_, v_it_499_, v___x_503_,
    );
    return v___x_505_;
}
pub unsafe fn l_Std_IterM_Total_toListRev___redArg(
    mut v_inst_506_: *mut leanh::LeanObject,
    mut v_inst_507_: *mut leanh::LeanObject,
    mut v_it_508_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_514_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_509_ = leanh::lean_ctor_get(v_inst_506_, 0);
    leanh::lean_inc_ref(v_toApplicative_509_);
    v_toBind_510_ = leanh::lean_ctor_get(v_inst_506_, 1);
    leanh::lean_inc(v_toBind_510_);
    leanh::lean_dec_ref(v_inst_506_);
    v_toPure_511_ = leanh::lean_ctor_get(v_toApplicative_509_, 1);
    leanh::lean_inc(v_toPure_511_);
    leanh::lean_dec_ref(v_toApplicative_509_);
    v___x_512_ = leanh::lean_box(0);
    v___f_513_ = leanh::lean_alloc_closure(
        l_Std_IterM_toListRev_go___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    leanh::lean_closure_set(v___f_513_, 0, v_toPure_511_);
    leanh::lean_closure_set(v___f_513_, 1, v_inst_507_);
    leanh::lean_closure_set(v___f_513_, 2, v_toBind_510_);
    v___x_514_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_513_, v_it_508_, v___x_512_,
    );
    return v___x_514_;
}
pub unsafe fn l_Std_IterM_Total_toListRev(
    mut v_00_u03b1_515_: *mut leanh::LeanObject,
    mut v_m_516_: *mut leanh::LeanObject,
    mut v_00_u03b2_517_: *mut leanh::LeanObject,
    mut v_inst_518_: *mut leanh::LeanObject,
    mut v_inst_519_: *mut leanh::LeanObject,
    mut v_inst_520_: *mut leanh::LeanObject,
    mut v_it_521_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_527_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_522_ = leanh::lean_ctor_get(v_inst_518_, 0);
    leanh::lean_inc_ref(v_toApplicative_522_);
    v_toBind_523_ = leanh::lean_ctor_get(v_inst_518_, 1);
    leanh::lean_inc(v_toBind_523_);
    leanh::lean_dec_ref(v_inst_518_);
    v_toPure_524_ = leanh::lean_ctor_get(v_toApplicative_522_, 1);
    leanh::lean_inc(v_toPure_524_);
    leanh::lean_dec_ref(v_toApplicative_522_);
    v___x_525_ = leanh::lean_box(0);
    v___f_526_ = leanh::lean_alloc_closure(
        l_Std_IterM_toListRev_go___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    leanh::lean_closure_set(v___f_526_, 0, v_toPure_524_);
    leanh::lean_closure_set(v___f_526_, 1, v_inst_519_);
    leanh::lean_closure_set(v___f_526_, 2, v_toBind_523_);
    v___x_527_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_526_, v_it_521_, v___x_525_,
    );
    return v___x_527_;
}
pub unsafe fn l_Std_IterM_toList___redArg___lam__0(
    mut v_self_528_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_529_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_529_ = lean_array_to_list(v_self_528_);
    return v___x_529_;
}
pub unsafe fn l_Std_IterM_toList___redArg(
    mut v_inst_531_: *mut leanh::LeanObject,
    mut v_inst_532_: *mut leanh::LeanObject,
    mut v_it_533_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_543_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_534_ = leanh::lean_ctor_get(v_inst_531_, 0);
    leanh::lean_inc_ref(v_toApplicative_534_);
    v_toFunctor_535_ = leanh::lean_ctor_get(v_toApplicative_534_, 0);
    leanh::lean_inc_ref(v_toFunctor_535_);
    v_toBind_536_ = leanh::lean_ctor_get(v_inst_531_, 1);
    leanh::lean_inc(v_toBind_536_);
    leanh::lean_dec_ref(v_inst_531_);
    v_toPure_537_ = leanh::lean_ctor_get(v_toApplicative_534_, 1);
    leanh::lean_inc(v_toPure_537_);
    leanh::lean_dec_ref(v_toApplicative_534_);
    v_map_538_ = leanh::lean_ctor_get(v_toFunctor_535_, 0);
    leanh::lean_inc(v_map_538_);
    leanh::lean_dec_ref(v_toFunctor_535_);
    v___f_539_ = l_Std_IterM_toList___redArg___closed__0;
    v___f_540_ = leanh::lean_alloc_closure(
        l_Std_IterM_toArray_go___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    leanh::lean_closure_set(v___f_540_, 0, v_toPure_537_);
    leanh::lean_closure_set(v___f_540_, 1, v_inst_532_);
    leanh::lean_closure_set(v___f_540_, 2, v_toBind_536_);
    v___x_541_ = l_Std_IterM_toArray___redArg___closed__0;
    v___x_542_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_540_, v_it_533_, v___x_541_,
    );
    v___x_543_ = leanh::lean_apply_4(
        v_map_538_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_539_,
        v___x_542_,
    );
    return v___x_543_;
}
pub unsafe fn l_Std_IterM_toList(
    mut v_00_u03b1_544_: *mut leanh::LeanObject,
    mut v_m_545_: *mut leanh::LeanObject,
    mut v_inst_546_: *mut leanh::LeanObject,
    mut v_00_u03b2_547_: *mut leanh::LeanObject,
    mut v_inst_548_: *mut leanh::LeanObject,
    mut v_it_549_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_559_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_550_ = leanh::lean_ctor_get(v_inst_546_, 0);
    leanh::lean_inc_ref(v_toApplicative_550_);
    v_toFunctor_551_ = leanh::lean_ctor_get(v_toApplicative_550_, 0);
    leanh::lean_inc_ref(v_toFunctor_551_);
    v_toBind_552_ = leanh::lean_ctor_get(v_inst_546_, 1);
    leanh::lean_inc(v_toBind_552_);
    leanh::lean_dec_ref(v_inst_546_);
    v_toPure_553_ = leanh::lean_ctor_get(v_toApplicative_550_, 1);
    leanh::lean_inc(v_toPure_553_);
    leanh::lean_dec_ref(v_toApplicative_550_);
    v_map_554_ = leanh::lean_ctor_get(v_toFunctor_551_, 0);
    leanh::lean_inc(v_map_554_);
    leanh::lean_dec_ref(v_toFunctor_551_);
    v___f_555_ = l_Std_IterM_toList___redArg___closed__0;
    v___f_556_ = leanh::lean_alloc_closure(
        l_Std_IterM_toArray_go___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    leanh::lean_closure_set(v___f_556_, 0, v_toPure_553_);
    leanh::lean_closure_set(v___f_556_, 1, v_inst_548_);
    leanh::lean_closure_set(v___f_556_, 2, v_toBind_552_);
    v___x_557_ = l_Std_IterM_toArray___redArg___closed__0;
    v___x_558_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_556_, v_it_549_, v___x_557_,
    );
    v___x_559_ = leanh::lean_apply_4(
        v_map_554_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_555_,
        v___x_558_,
    );
    return v___x_559_;
}
pub unsafe fn l_Std_IterM_Partial_toList___redArg(
    mut v_inst_560_: *mut leanh::LeanObject,
    mut v_inst_561_: *mut leanh::LeanObject,
    mut v_it_562_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_572_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_563_ = leanh::lean_ctor_get(v_inst_560_, 0);
    leanh::lean_inc_ref(v_toApplicative_563_);
    v_toFunctor_564_ = leanh::lean_ctor_get(v_toApplicative_563_, 0);
    leanh::lean_inc_ref(v_toFunctor_564_);
    v_toBind_565_ = leanh::lean_ctor_get(v_inst_560_, 1);
    leanh::lean_inc(v_toBind_565_);
    leanh::lean_dec_ref(v_inst_560_);
    v_toPure_566_ = leanh::lean_ctor_get(v_toApplicative_563_, 1);
    leanh::lean_inc(v_toPure_566_);
    leanh::lean_dec_ref(v_toApplicative_563_);
    v_map_567_ = leanh::lean_ctor_get(v_toFunctor_564_, 0);
    leanh::lean_inc(v_map_567_);
    leanh::lean_dec_ref(v_toFunctor_564_);
    v___f_568_ = l_Std_IterM_toList___redArg___closed__0;
    v___f_569_ = leanh::lean_alloc_closure(
        l_Std_IterM_toArray_go___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    leanh::lean_closure_set(v___f_569_, 0, v_toPure_566_);
    leanh::lean_closure_set(v___f_569_, 1, v_inst_561_);
    leanh::lean_closure_set(v___f_569_, 2, v_toBind_565_);
    v___x_570_ = l_Std_IterM_toArray___redArg___closed__0;
    v___x_571_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_569_, v_it_562_, v___x_570_,
    );
    v___x_572_ = leanh::lean_apply_4(
        v_map_567_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_568_,
        v___x_571_,
    );
    return v___x_572_;
}
pub unsafe fn l_Std_IterM_Partial_toList(
    mut v_00_u03b1_573_: *mut leanh::LeanObject,
    mut v_m_574_: *mut leanh::LeanObject,
    mut v_inst_575_: *mut leanh::LeanObject,
    mut v_00_u03b2_576_: *mut leanh::LeanObject,
    mut v_inst_577_: *mut leanh::LeanObject,
    mut v_it_578_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_588_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_579_ = leanh::lean_ctor_get(v_inst_575_, 0);
    leanh::lean_inc_ref(v_toApplicative_579_);
    v_toFunctor_580_ = leanh::lean_ctor_get(v_toApplicative_579_, 0);
    leanh::lean_inc_ref(v_toFunctor_580_);
    v_toBind_581_ = leanh::lean_ctor_get(v_inst_575_, 1);
    leanh::lean_inc(v_toBind_581_);
    leanh::lean_dec_ref(v_inst_575_);
    v_toPure_582_ = leanh::lean_ctor_get(v_toApplicative_579_, 1);
    leanh::lean_inc(v_toPure_582_);
    leanh::lean_dec_ref(v_toApplicative_579_);
    v_map_583_ = leanh::lean_ctor_get(v_toFunctor_580_, 0);
    leanh::lean_inc(v_map_583_);
    leanh::lean_dec_ref(v_toFunctor_580_);
    v___f_584_ = l_Std_IterM_toList___redArg___closed__0;
    v___f_585_ = leanh::lean_alloc_closure(
        l_Std_IterM_toArray_go___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    leanh::lean_closure_set(v___f_585_, 0, v_toPure_582_);
    leanh::lean_closure_set(v___f_585_, 1, v_inst_577_);
    leanh::lean_closure_set(v___f_585_, 2, v_toBind_581_);
    v___x_586_ = l_Std_IterM_toArray___redArg___closed__0;
    v___x_587_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_585_, v_it_578_, v___x_586_,
    );
    v___x_588_ = leanh::lean_apply_4(
        v_map_583_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_584_,
        v___x_587_,
    );
    return v___x_588_;
}
pub unsafe fn l_Std_IterM_Total_toList___redArg(
    mut v_inst_589_: *mut leanh::LeanObject,
    mut v_inst_590_: *mut leanh::LeanObject,
    mut v_it_591_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_601_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_592_ = leanh::lean_ctor_get(v_inst_589_, 0);
    leanh::lean_inc_ref(v_toApplicative_592_);
    v_toFunctor_593_ = leanh::lean_ctor_get(v_toApplicative_592_, 0);
    leanh::lean_inc_ref(v_toFunctor_593_);
    v_toBind_594_ = leanh::lean_ctor_get(v_inst_589_, 1);
    leanh::lean_inc(v_toBind_594_);
    leanh::lean_dec_ref(v_inst_589_);
    v_toPure_595_ = leanh::lean_ctor_get(v_toApplicative_592_, 1);
    leanh::lean_inc(v_toPure_595_);
    leanh::lean_dec_ref(v_toApplicative_592_);
    v_map_596_ = leanh::lean_ctor_get(v_toFunctor_593_, 0);
    leanh::lean_inc(v_map_596_);
    leanh::lean_dec_ref(v_toFunctor_593_);
    v___f_597_ = l_Std_IterM_toList___redArg___closed__0;
    v___f_598_ = leanh::lean_alloc_closure(
        l_Std_IterM_toArray_go___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    leanh::lean_closure_set(v___f_598_, 0, v_toPure_595_);
    leanh::lean_closure_set(v___f_598_, 1, v_inst_590_);
    leanh::lean_closure_set(v___f_598_, 2, v_toBind_594_);
    v___x_599_ = l_Std_IterM_toArray___redArg___closed__0;
    v___x_600_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_598_, v_it_591_, v___x_599_,
    );
    v___x_601_ = leanh::lean_apply_4(
        v_map_596_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_597_,
        v___x_600_,
    );
    return v___x_601_;
}
pub unsafe fn l_Std_IterM_Total_toList(
    mut v_00_u03b1_602_: *mut leanh::LeanObject,
    mut v_m_603_: *mut leanh::LeanObject,
    mut v_00_u03b2_604_: *mut leanh::LeanObject,
    mut v_inst_605_: *mut leanh::LeanObject,
    mut v_inst_606_: *mut leanh::LeanObject,
    mut v_inst_607_: *mut leanh::LeanObject,
    mut v_it_608_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_618_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_609_ = leanh::lean_ctor_get(v_inst_605_, 0);
    leanh::lean_inc_ref(v_toApplicative_609_);
    v_toFunctor_610_ = leanh::lean_ctor_get(v_toApplicative_609_, 0);
    leanh::lean_inc_ref(v_toFunctor_610_);
    v_toBind_611_ = leanh::lean_ctor_get(v_inst_605_, 1);
    leanh::lean_inc(v_toBind_611_);
    leanh::lean_dec_ref(v_inst_605_);
    v_toPure_612_ = leanh::lean_ctor_get(v_toApplicative_609_, 1);
    leanh::lean_inc(v_toPure_612_);
    leanh::lean_dec_ref(v_toApplicative_609_);
    v_map_613_ = leanh::lean_ctor_get(v_toFunctor_610_, 0);
    leanh::lean_inc(v_map_613_);
    leanh::lean_dec_ref(v_toFunctor_610_);
    v___f_614_ = l_Std_IterM_toList___redArg___closed__0;
    v___f_615_ = leanh::lean_alloc_closure(
        l_Std_IterM_toArray_go___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    leanh::lean_closure_set(v___f_615_, 0, v_toPure_612_);
    leanh::lean_closure_set(v___f_615_, 1, v_inst_606_);
    leanh::lean_closure_set(v___f_615_, 2, v_toBind_611_);
    v___x_616_ = l_Std_IterM_toArray___redArg___closed__0;
    v___x_617_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_615_, v_it_608_, v___x_616_,
    );
    v___x_618_ = leanh::lean_apply_4(
        v_map_613_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_614_,
        v___x_617_,
    );
    return v___x_618_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Partial(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Total(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_WFExtrinsicFix(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Ext(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(
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
pub unsafe fn initialize_Init_Data_Iterators_Consumers_Monadic_Collect(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Consumers_Monadic_Partial(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Monadic_Total(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_WFExtrinsicFix(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Ext(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
}