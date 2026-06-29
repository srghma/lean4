// Lean compiler output
// Module: Init.Data.Iterators.Consumers.Monadic.Collect
// Imports: Init.Data.Iterators.Consumers.Monadic.Partial Init.Data.Iterators.Consumers.Monadic.Total Init.WFExtrinsicFix Init.Ext
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
use crate::ffi::{lean_array_push, lean_array_to_list};
pub static l_Std_IterM_toArray___redArg___closed__0_value: crate::leanh::LeanArrayObject<0> =
    crate::leanh::LeanArrayObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Std_IterM_toArray___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_IterM_toArray___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_IterM_toList___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_IterM_toList___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_IterM_toList___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_IterM_toList___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Std_IterM_toArray_go___redArg___lam__0(
    mut v_acc_310_: *mut crate::leanh::LeanObject,
    mut v_recur_311_: *mut crate::leanh::LeanObject,
    mut v_toPure_312_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_____do__lift_313_) {
        0 => {
            let mut v_it_314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_toPure_312_);
            v_it_314_ = crate::leanh::lean_ctor_get(v_____do__lift_313_, 0);
            crate::leanh::lean_inc(v_it_314_);
            v_out_315_ = crate::leanh::lean_ctor_get(v_____do__lift_313_, 1);
            crate::leanh::lean_inc(v_out_315_);
            crate::leanh::lean_dec_ref_known(v_____do__lift_313_, 2);
            v___x_316_ = lean_array_push(v_acc_310_, v_out_315_);
            v___x_317_ = crate::leanh::lean_apply_3(
                v_recur_311_,
                v_it_314_,
                v___x_316_,
                crate::leanh::lean_box(0),
            );
            return v___x_317_;
        }
        1 => {
            let mut v_it_318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_toPure_312_);
            v_it_318_ = crate::leanh::lean_ctor_get(v_____do__lift_313_, 0);
            crate::leanh::lean_inc(v_it_318_);
            crate::leanh::lean_dec_ref_known(v_____do__lift_313_, 1);
            v___x_319_ = crate::leanh::lean_apply_3(
                v_recur_311_,
                v_it_318_,
                v_acc_310_,
                crate::leanh::lean_box(0),
            );
            return v___x_319_;
        }
        _ => {
            let mut v___x_320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_recur_311_);
            v___x_320_ =
                crate::leanh::lean_apply_2(v_toPure_312_, crate::leanh::lean_box(0), v_acc_310_);
            return v___x_320_;
        }
    }
}
pub unsafe fn l_Std_IterM_toArray_go___redArg___lam__1(
    mut v_toPure_321_: *mut crate::leanh::LeanObject,
    mut v_inst_322_: *mut crate::leanh::LeanObject,
    mut v_toBind_323_: *mut crate::leanh::LeanObject,
    mut v_it_324_: *mut crate::leanh::LeanObject,
    mut v_acc_325_: *mut crate::leanh::LeanObject,
    mut v_recur_326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_327_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_toArray_go___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_327_, 0, v_acc_325_);
    crate::leanh::lean_closure_set(v___f_327_, 1, v_recur_326_);
    crate::leanh::lean_closure_set(v___f_327_, 2, v_toPure_321_);
    v___x_328_ = crate::leanh::lean_apply_1(v_inst_322_, v_it_324_);
    v___x_329_ = crate::leanh::lean_apply_4(
        v_toBind_323_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_328_,
        v___f_327_,
    );
    return v___x_329_;
}
pub unsafe fn l_Std_IterM_toArray_go___redArg(
    mut v_inst_330_: *mut crate::leanh::LeanObject,
    mut v_inst_331_: *mut crate::leanh::LeanObject,
    mut v_it_332_: *mut crate::leanh::LeanObject,
    mut v_acc_333_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_334_ = crate::leanh::lean_ctor_get(v_inst_330_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_334_);
    v_toBind_335_ = crate::leanh::lean_ctor_get(v_inst_330_, 1);
    crate::leanh::lean_inc(v_toBind_335_);
    crate::leanh::lean_dec_ref(v_inst_330_);
    v_toPure_336_ = crate::leanh::lean_ctor_get(v_toApplicative_334_, 1);
    crate::leanh::lean_inc(v_toPure_336_);
    crate::leanh::lean_dec_ref(v_toApplicative_334_);
    v___f_337_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_toArray_go___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    crate::leanh::lean_closure_set(v___f_337_, 0, v_toPure_336_);
    crate::leanh::lean_closure_set(v___f_337_, 1, v_inst_331_);
    crate::leanh::lean_closure_set(v___f_337_, 2, v_toBind_335_);
    v___x_338_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_337_, v_it_332_, v_acc_333_,
    );
    return v___x_338_;
}
pub unsafe fn l_Std_IterM_toArray_go(
    mut v_00_u03b1_339_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_340_: *mut crate::leanh::LeanObject,
    mut v_m_341_: *mut crate::leanh::LeanObject,
    mut v_inst_342_: *mut crate::leanh::LeanObject,
    mut v_inst_343_: *mut crate::leanh::LeanObject,
    mut v_it_344_: *mut crate::leanh::LeanObject,
    mut v_acc_345_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_346_ = crate::leanh::lean_ctor_get(v_inst_342_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_346_);
    v_toBind_347_ = crate::leanh::lean_ctor_get(v_inst_342_, 1);
    crate::leanh::lean_inc(v_toBind_347_);
    crate::leanh::lean_dec_ref(v_inst_342_);
    v_toPure_348_ = crate::leanh::lean_ctor_get(v_toApplicative_346_, 1);
    crate::leanh::lean_inc(v_toPure_348_);
    crate::leanh::lean_dec_ref(v_toApplicative_346_);
    v___f_349_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_toArray_go___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    crate::leanh::lean_closure_set(v___f_349_, 0, v_toPure_348_);
    crate::leanh::lean_closure_set(v___f_349_, 1, v_inst_343_);
    crate::leanh::lean_closure_set(v___f_349_, 2, v_toBind_347_);
    v___x_350_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_349_, v_it_344_, v_acc_345_,
    );
    return v___x_350_;
}
pub unsafe fn l_Std_IterM_toArray___redArg(
    mut v_inst_353_: *mut crate::leanh::LeanObject,
    mut v_inst_354_: *mut crate::leanh::LeanObject,
    mut v_it_355_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_356_ = crate::leanh::lean_ctor_get(v_inst_353_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_356_);
    v_toBind_357_ = crate::leanh::lean_ctor_get(v_inst_353_, 1);
    crate::leanh::lean_inc(v_toBind_357_);
    crate::leanh::lean_dec_ref(v_inst_353_);
    v_toPure_358_ = crate::leanh::lean_ctor_get(v_toApplicative_356_, 1);
    crate::leanh::lean_inc(v_toPure_358_);
    crate::leanh::lean_dec_ref(v_toApplicative_356_);
    v___x_359_ = l_Std_IterM_toArray___redArg___closed__0;
    v___f_360_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_toArray_go___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    crate::leanh::lean_closure_set(v___f_360_, 0, v_toPure_358_);
    crate::leanh::lean_closure_set(v___f_360_, 1, v_inst_354_);
    crate::leanh::lean_closure_set(v___f_360_, 2, v_toBind_357_);
    v___x_361_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_360_, v_it_355_, v___x_359_,
    );
    return v___x_361_;
}
pub unsafe fn l_Std_IterM_toArray(
    mut v_00_u03b1_362_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_363_: *mut crate::leanh::LeanObject,
    mut v_m_364_: *mut crate::leanh::LeanObject,
    mut v_inst_365_: *mut crate::leanh::LeanObject,
    mut v_inst_366_: *mut crate::leanh::LeanObject,
    mut v_it_367_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_368_ = crate::leanh::lean_ctor_get(v_inst_365_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_368_);
    v_toBind_369_ = crate::leanh::lean_ctor_get(v_inst_365_, 1);
    crate::leanh::lean_inc(v_toBind_369_);
    crate::leanh::lean_dec_ref(v_inst_365_);
    v_toPure_370_ = crate::leanh::lean_ctor_get(v_toApplicative_368_, 1);
    crate::leanh::lean_inc(v_toPure_370_);
    crate::leanh::lean_dec_ref(v_toApplicative_368_);
    v___x_371_ = l_Std_IterM_toArray___redArg___closed__0;
    v___f_372_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_toArray_go___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    crate::leanh::lean_closure_set(v___f_372_, 0, v_toPure_370_);
    crate::leanh::lean_closure_set(v___f_372_, 1, v_inst_366_);
    crate::leanh::lean_closure_set(v___f_372_, 2, v_toBind_369_);
    v___x_373_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_372_, v_it_367_, v___x_371_,
    );
    return v___x_373_;
}
pub unsafe fn l_Std_IterM_Partial_toArray___redArg(
    mut v_inst_374_: *mut crate::leanh::LeanObject,
    mut v_inst_375_: *mut crate::leanh::LeanObject,
    mut v_it_376_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_377_ = crate::leanh::lean_ctor_get(v_inst_374_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_377_);
    v_toBind_378_ = crate::leanh::lean_ctor_get(v_inst_374_, 1);
    crate::leanh::lean_inc(v_toBind_378_);
    crate::leanh::lean_dec_ref(v_inst_374_);
    v_toPure_379_ = crate::leanh::lean_ctor_get(v_toApplicative_377_, 1);
    crate::leanh::lean_inc(v_toPure_379_);
    crate::leanh::lean_dec_ref(v_toApplicative_377_);
    v___x_380_ = l_Std_IterM_toArray___redArg___closed__0;
    v___f_381_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_toArray_go___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    crate::leanh::lean_closure_set(v___f_381_, 0, v_toPure_379_);
    crate::leanh::lean_closure_set(v___f_381_, 1, v_inst_375_);
    crate::leanh::lean_closure_set(v___f_381_, 2, v_toBind_378_);
    v___x_382_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_381_, v_it_376_, v___x_380_,
    );
    return v___x_382_;
}
pub unsafe fn l_Std_IterM_Partial_toArray(
    mut v_00_u03b1_383_: *mut crate::leanh::LeanObject,
    mut v_m_384_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_385_: *mut crate::leanh::LeanObject,
    mut v_inst_386_: *mut crate::leanh::LeanObject,
    mut v_inst_387_: *mut crate::leanh::LeanObject,
    mut v_it_388_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_389_ = crate::leanh::lean_ctor_get(v_inst_386_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_389_);
    v_toBind_390_ = crate::leanh::lean_ctor_get(v_inst_386_, 1);
    crate::leanh::lean_inc(v_toBind_390_);
    crate::leanh::lean_dec_ref(v_inst_386_);
    v_toPure_391_ = crate::leanh::lean_ctor_get(v_toApplicative_389_, 1);
    crate::leanh::lean_inc(v_toPure_391_);
    crate::leanh::lean_dec_ref(v_toApplicative_389_);
    v___x_392_ = l_Std_IterM_toArray___redArg___closed__0;
    v___f_393_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_toArray_go___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    crate::leanh::lean_closure_set(v___f_393_, 0, v_toPure_391_);
    crate::leanh::lean_closure_set(v___f_393_, 1, v_inst_387_);
    crate::leanh::lean_closure_set(v___f_393_, 2, v_toBind_390_);
    v___x_394_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_393_, v_it_388_, v___x_392_,
    );
    return v___x_394_;
}
pub unsafe fn l_Std_IterM_Total_toArray___redArg(
    mut v_inst_395_: *mut crate::leanh::LeanObject,
    mut v_inst_396_: *mut crate::leanh::LeanObject,
    mut v_it_397_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_398_ = crate::leanh::lean_ctor_get(v_inst_395_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_398_);
    v_toBind_399_ = crate::leanh::lean_ctor_get(v_inst_395_, 1);
    crate::leanh::lean_inc(v_toBind_399_);
    crate::leanh::lean_dec_ref(v_inst_395_);
    v_toPure_400_ = crate::leanh::lean_ctor_get(v_toApplicative_398_, 1);
    crate::leanh::lean_inc(v_toPure_400_);
    crate::leanh::lean_dec_ref(v_toApplicative_398_);
    v___x_401_ = l_Std_IterM_toArray___redArg___closed__0;
    v___f_402_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_toArray_go___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    crate::leanh::lean_closure_set(v___f_402_, 0, v_toPure_400_);
    crate::leanh::lean_closure_set(v___f_402_, 1, v_inst_396_);
    crate::leanh::lean_closure_set(v___f_402_, 2, v_toBind_399_);
    v___x_403_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_402_, v_it_397_, v___x_401_,
    );
    return v___x_403_;
}
pub unsafe fn l_Std_IterM_Total_toArray(
    mut v_00_u03b1_404_: *mut crate::leanh::LeanObject,
    mut v_m_405_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_406_: *mut crate::leanh::LeanObject,
    mut v_inst_407_: *mut crate::leanh::LeanObject,
    mut v_inst_408_: *mut crate::leanh::LeanObject,
    mut v_inst_409_: *mut crate::leanh::LeanObject,
    mut v_it_410_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_411_ = crate::leanh::lean_ctor_get(v_inst_407_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_411_);
    v_toBind_412_ = crate::leanh::lean_ctor_get(v_inst_407_, 1);
    crate::leanh::lean_inc(v_toBind_412_);
    crate::leanh::lean_dec_ref(v_inst_407_);
    v_toPure_413_ = crate::leanh::lean_ctor_get(v_toApplicative_411_, 1);
    crate::leanh::lean_inc(v_toPure_413_);
    crate::leanh::lean_dec_ref(v_toApplicative_411_);
    v___x_414_ = l_Std_IterM_toArray___redArg___closed__0;
    v___f_415_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_toArray_go___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    crate::leanh::lean_closure_set(v___f_415_, 0, v_toPure_413_);
    crate::leanh::lean_closure_set(v___f_415_, 1, v_inst_408_);
    crate::leanh::lean_closure_set(v___f_415_, 2, v_toBind_412_);
    v___x_416_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_415_, v_it_410_, v___x_414_,
    );
    return v___x_416_;
}
pub unsafe fn l_Std_IterM_toListRev_go___redArg___lam__0(
    mut v_acc_417_: *mut crate::leanh::LeanObject,
    mut v_recur_418_: *mut crate::leanh::LeanObject,
    mut v_toPure_419_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_420_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_it_421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_425_: u8 = 0;
    let mut v___x_427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_430_: u8 = 0;
    let mut v_it_431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_____do__lift_420_) {
                0 => {
                    crate::leanh::lean_dec(v_toPure_419_);
                    v_it_421_ = crate::leanh::lean_ctor_get(v_____do__lift_420_, 0);
                    v_out_422_ = crate::leanh::lean_ctor_get(v_____do__lift_420_, 1);
                    v_isSharedCheck_430_ =
                        (!crate::leanh::lean_is_exclusive(v_____do__lift_420_)) as u8;
                    if v_isSharedCheck_430_ == 0 {
                        v___x_424_ = v_____do__lift_420_;
                        v_isShared_425_ = v_isSharedCheck_430_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_out_422_);
                        crate::leanh::lean_inc(v_it_421_);
                        crate::leanh::lean_dec(v_____do__lift_420_);
                        v___x_424_ = crate::leanh::lean_box(0);
                        v_isShared_425_ = v_isSharedCheck_430_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    crate::leanh::lean_dec(v_toPure_419_);
                    v_it_431_ = crate::leanh::lean_ctor_get(v_____do__lift_420_, 0);
                    crate::leanh::lean_inc(v_it_431_);
                    crate::leanh::lean_dec_ref_known(v_____do__lift_420_, 1);
                    v___x_432_ = crate::leanh::lean_apply_3(
                        v_recur_418_,
                        v_it_431_,
                        v_acc_417_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_432_;
                }
                _ => {
                    crate::leanh::lean_dec(v_recur_418_);
                    v___x_433_ = crate::leanh::lean_apply_2(
                        v_toPure_419_,
                        crate::leanh::lean_box(0),
                        v_acc_417_,
                    );
                    return v___x_433_;
                }
            },
            1 => {
                if v_isShared_425_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_424_, 1);
                    crate::leanh::lean_ctor_set(v___x_424_, 1, v_acc_417_);
                    crate::leanh::lean_ctor_set(v___x_424_, 0, v_out_422_);
                    v___x_427_ = v___x_424_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_429_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_429_, 0, v_out_422_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_429_, 1, v_acc_417_);
                    v___x_427_ = v_reuseFailAlloc_429_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_428_ = crate::leanh::lean_apply_3(
                    v_recur_418_,
                    v_it_421_,
                    v___x_427_,
                    crate::leanh::lean_box(0),
                );
                return v___x_428_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_IterM_toListRev_go___redArg___lam__1(
    mut v_toPure_434_: *mut crate::leanh::LeanObject,
    mut v_inst_435_: *mut crate::leanh::LeanObject,
    mut v_toBind_436_: *mut crate::leanh::LeanObject,
    mut v_it_437_: *mut crate::leanh::LeanObject,
    mut v_acc_438_: *mut crate::leanh::LeanObject,
    mut v_recur_439_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_440_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_toListRev_go___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_440_, 0, v_acc_438_);
    crate::leanh::lean_closure_set(v___f_440_, 1, v_recur_439_);
    crate::leanh::lean_closure_set(v___f_440_, 2, v_toPure_434_);
    v___x_441_ = crate::leanh::lean_apply_1(v_inst_435_, v_it_437_);
    v___x_442_ = crate::leanh::lean_apply_4(
        v_toBind_436_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_441_,
        v___f_440_,
    );
    return v___x_442_;
}
pub unsafe fn l_Std_IterM_toListRev_go___redArg(
    mut v_inst_443_: *mut crate::leanh::LeanObject,
    mut v_inst_444_: *mut crate::leanh::LeanObject,
    mut v_it_445_: *mut crate::leanh::LeanObject,
    mut v_acc_446_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_447_ = crate::leanh::lean_ctor_get(v_inst_443_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_447_);
    v_toBind_448_ = crate::leanh::lean_ctor_get(v_inst_443_, 1);
    crate::leanh::lean_inc(v_toBind_448_);
    crate::leanh::lean_dec_ref(v_inst_443_);
    v_toPure_449_ = crate::leanh::lean_ctor_get(v_toApplicative_447_, 1);
    crate::leanh::lean_inc(v_toPure_449_);
    crate::leanh::lean_dec_ref(v_toApplicative_447_);
    v___f_450_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_toListRev_go___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    crate::leanh::lean_closure_set(v___f_450_, 0, v_toPure_449_);
    crate::leanh::lean_closure_set(v___f_450_, 1, v_inst_444_);
    crate::leanh::lean_closure_set(v___f_450_, 2, v_toBind_448_);
    v___x_451_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_450_, v_it_445_, v_acc_446_,
    );
    return v___x_451_;
}
pub unsafe fn l_Std_IterM_toListRev_go(
    mut v_00_u03b1_452_: *mut crate::leanh::LeanObject,
    mut v_m_453_: *mut crate::leanh::LeanObject,
    mut v_inst_454_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_455_: *mut crate::leanh::LeanObject,
    mut v_inst_456_: *mut crate::leanh::LeanObject,
    mut v_it_457_: *mut crate::leanh::LeanObject,
    mut v_acc_458_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_459_ = crate::leanh::lean_ctor_get(v_inst_454_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_459_);
    v_toBind_460_ = crate::leanh::lean_ctor_get(v_inst_454_, 1);
    crate::leanh::lean_inc(v_toBind_460_);
    crate::leanh::lean_dec_ref(v_inst_454_);
    v_toPure_461_ = crate::leanh::lean_ctor_get(v_toApplicative_459_, 1);
    crate::leanh::lean_inc(v_toPure_461_);
    crate::leanh::lean_dec_ref(v_toApplicative_459_);
    v___f_462_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_toListRev_go___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    crate::leanh::lean_closure_set(v___f_462_, 0, v_toPure_461_);
    crate::leanh::lean_closure_set(v___f_462_, 1, v_inst_456_);
    crate::leanh::lean_closure_set(v___f_462_, 2, v_toBind_460_);
    v___x_463_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_462_, v_it_457_, v_acc_458_,
    );
    return v___x_463_;
}
pub unsafe fn l_Std_IterM_toListRev___redArg(
    mut v_inst_464_: *mut crate::leanh::LeanObject,
    mut v_inst_465_: *mut crate::leanh::LeanObject,
    mut v_it_466_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_467_ = crate::leanh::lean_ctor_get(v_inst_464_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_467_);
    v_toBind_468_ = crate::leanh::lean_ctor_get(v_inst_464_, 1);
    crate::leanh::lean_inc(v_toBind_468_);
    crate::leanh::lean_dec_ref(v_inst_464_);
    v_toPure_469_ = crate::leanh::lean_ctor_get(v_toApplicative_467_, 1);
    crate::leanh::lean_inc(v_toPure_469_);
    crate::leanh::lean_dec_ref(v_toApplicative_467_);
    v___x_470_ = crate::leanh::lean_box(0);
    v___f_471_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_toListRev_go___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    crate::leanh::lean_closure_set(v___f_471_, 0, v_toPure_469_);
    crate::leanh::lean_closure_set(v___f_471_, 1, v_inst_465_);
    crate::leanh::lean_closure_set(v___f_471_, 2, v_toBind_468_);
    v___x_472_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_471_, v_it_466_, v___x_470_,
    );
    return v___x_472_;
}
pub unsafe fn l_Std_IterM_toListRev(
    mut v_00_u03b1_473_: *mut crate::leanh::LeanObject,
    mut v_m_474_: *mut crate::leanh::LeanObject,
    mut v_inst_475_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_476_: *mut crate::leanh::LeanObject,
    mut v_inst_477_: *mut crate::leanh::LeanObject,
    mut v_it_478_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_479_ = crate::leanh::lean_ctor_get(v_inst_475_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_479_);
    v_toBind_480_ = crate::leanh::lean_ctor_get(v_inst_475_, 1);
    crate::leanh::lean_inc(v_toBind_480_);
    crate::leanh::lean_dec_ref(v_inst_475_);
    v_toPure_481_ = crate::leanh::lean_ctor_get(v_toApplicative_479_, 1);
    crate::leanh::lean_inc(v_toPure_481_);
    crate::leanh::lean_dec_ref(v_toApplicative_479_);
    v___x_482_ = crate::leanh::lean_box(0);
    v___f_483_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_toListRev_go___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    crate::leanh::lean_closure_set(v___f_483_, 0, v_toPure_481_);
    crate::leanh::lean_closure_set(v___f_483_, 1, v_inst_477_);
    crate::leanh::lean_closure_set(v___f_483_, 2, v_toBind_480_);
    v___x_484_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_483_, v_it_478_, v___x_482_,
    );
    return v___x_484_;
}
pub unsafe fn l_Std_IterM_Partial_toListRev___redArg(
    mut v_inst_485_: *mut crate::leanh::LeanObject,
    mut v_inst_486_: *mut crate::leanh::LeanObject,
    mut v_it_487_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_488_ = crate::leanh::lean_ctor_get(v_inst_485_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_488_);
    v_toBind_489_ = crate::leanh::lean_ctor_get(v_inst_485_, 1);
    crate::leanh::lean_inc(v_toBind_489_);
    crate::leanh::lean_dec_ref(v_inst_485_);
    v_toPure_490_ = crate::leanh::lean_ctor_get(v_toApplicative_488_, 1);
    crate::leanh::lean_inc(v_toPure_490_);
    crate::leanh::lean_dec_ref(v_toApplicative_488_);
    v___x_491_ = crate::leanh::lean_box(0);
    v___f_492_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_toListRev_go___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    crate::leanh::lean_closure_set(v___f_492_, 0, v_toPure_490_);
    crate::leanh::lean_closure_set(v___f_492_, 1, v_inst_486_);
    crate::leanh::lean_closure_set(v___f_492_, 2, v_toBind_489_);
    v___x_493_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_492_, v_it_487_, v___x_491_,
    );
    return v___x_493_;
}
pub unsafe fn l_Std_IterM_Partial_toListRev(
    mut v_00_u03b1_494_: *mut crate::leanh::LeanObject,
    mut v_m_495_: *mut crate::leanh::LeanObject,
    mut v_inst_496_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_497_: *mut crate::leanh::LeanObject,
    mut v_inst_498_: *mut crate::leanh::LeanObject,
    mut v_it_499_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_500_ = crate::leanh::lean_ctor_get(v_inst_496_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_500_);
    v_toBind_501_ = crate::leanh::lean_ctor_get(v_inst_496_, 1);
    crate::leanh::lean_inc(v_toBind_501_);
    crate::leanh::lean_dec_ref(v_inst_496_);
    v_toPure_502_ = crate::leanh::lean_ctor_get(v_toApplicative_500_, 1);
    crate::leanh::lean_inc(v_toPure_502_);
    crate::leanh::lean_dec_ref(v_toApplicative_500_);
    v___x_503_ = crate::leanh::lean_box(0);
    v___f_504_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_toListRev_go___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    crate::leanh::lean_closure_set(v___f_504_, 0, v_toPure_502_);
    crate::leanh::lean_closure_set(v___f_504_, 1, v_inst_498_);
    crate::leanh::lean_closure_set(v___f_504_, 2, v_toBind_501_);
    v___x_505_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_504_, v_it_499_, v___x_503_,
    );
    return v___x_505_;
}
pub unsafe fn l_Std_IterM_Total_toListRev___redArg(
    mut v_inst_506_: *mut crate::leanh::LeanObject,
    mut v_inst_507_: *mut crate::leanh::LeanObject,
    mut v_it_508_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_509_ = crate::leanh::lean_ctor_get(v_inst_506_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_509_);
    v_toBind_510_ = crate::leanh::lean_ctor_get(v_inst_506_, 1);
    crate::leanh::lean_inc(v_toBind_510_);
    crate::leanh::lean_dec_ref(v_inst_506_);
    v_toPure_511_ = crate::leanh::lean_ctor_get(v_toApplicative_509_, 1);
    crate::leanh::lean_inc(v_toPure_511_);
    crate::leanh::lean_dec_ref(v_toApplicative_509_);
    v___x_512_ = crate::leanh::lean_box(0);
    v___f_513_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_toListRev_go___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    crate::leanh::lean_closure_set(v___f_513_, 0, v_toPure_511_);
    crate::leanh::lean_closure_set(v___f_513_, 1, v_inst_507_);
    crate::leanh::lean_closure_set(v___f_513_, 2, v_toBind_510_);
    v___x_514_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_513_, v_it_508_, v___x_512_,
    );
    return v___x_514_;
}
pub unsafe fn l_Std_IterM_Total_toListRev(
    mut v_00_u03b1_515_: *mut crate::leanh::LeanObject,
    mut v_m_516_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_517_: *mut crate::leanh::LeanObject,
    mut v_inst_518_: *mut crate::leanh::LeanObject,
    mut v_inst_519_: *mut crate::leanh::LeanObject,
    mut v_inst_520_: *mut crate::leanh::LeanObject,
    mut v_it_521_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_522_ = crate::leanh::lean_ctor_get(v_inst_518_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_522_);
    v_toBind_523_ = crate::leanh::lean_ctor_get(v_inst_518_, 1);
    crate::leanh::lean_inc(v_toBind_523_);
    crate::leanh::lean_dec_ref(v_inst_518_);
    v_toPure_524_ = crate::leanh::lean_ctor_get(v_toApplicative_522_, 1);
    crate::leanh::lean_inc(v_toPure_524_);
    crate::leanh::lean_dec_ref(v_toApplicative_522_);
    v___x_525_ = crate::leanh::lean_box(0);
    v___f_526_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_toListRev_go___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    crate::leanh::lean_closure_set(v___f_526_, 0, v_toPure_524_);
    crate::leanh::lean_closure_set(v___f_526_, 1, v_inst_519_);
    crate::leanh::lean_closure_set(v___f_526_, 2, v_toBind_523_);
    v___x_527_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_526_, v_it_521_, v___x_525_,
    );
    return v___x_527_;
}
pub unsafe fn l_Std_IterM_toList___redArg___lam__0(
    mut v_self_528_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_529_ = lean_array_to_list(v_self_528_);
    return v___x_529_;
}
pub unsafe fn l_Std_IterM_toList___redArg(
    mut v_inst_531_: *mut crate::leanh::LeanObject,
    mut v_inst_532_: *mut crate::leanh::LeanObject,
    mut v_it_533_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_534_ = crate::leanh::lean_ctor_get(v_inst_531_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_534_);
    v_toFunctor_535_ = crate::leanh::lean_ctor_get(v_toApplicative_534_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_535_);
    v_toBind_536_ = crate::leanh::lean_ctor_get(v_inst_531_, 1);
    crate::leanh::lean_inc(v_toBind_536_);
    crate::leanh::lean_dec_ref(v_inst_531_);
    v_toPure_537_ = crate::leanh::lean_ctor_get(v_toApplicative_534_, 1);
    crate::leanh::lean_inc(v_toPure_537_);
    crate::leanh::lean_dec_ref(v_toApplicative_534_);
    v_map_538_ = crate::leanh::lean_ctor_get(v_toFunctor_535_, 0);
    crate::leanh::lean_inc(v_map_538_);
    crate::leanh::lean_dec_ref(v_toFunctor_535_);
    v___f_539_ = l_Std_IterM_toList___redArg___closed__0;
    v___f_540_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_toArray_go___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    crate::leanh::lean_closure_set(v___f_540_, 0, v_toPure_537_);
    crate::leanh::lean_closure_set(v___f_540_, 1, v_inst_532_);
    crate::leanh::lean_closure_set(v___f_540_, 2, v_toBind_536_);
    v___x_541_ = l_Std_IterM_toArray___redArg___closed__0;
    v___x_542_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_540_, v_it_533_, v___x_541_,
    );
    v___x_543_ = crate::leanh::lean_apply_4(
        v_map_538_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_539_,
        v___x_542_,
    );
    return v___x_543_;
}
pub unsafe fn l_Std_IterM_toList(
    mut v_00_u03b1_544_: *mut crate::leanh::LeanObject,
    mut v_m_545_: *mut crate::leanh::LeanObject,
    mut v_inst_546_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_547_: *mut crate::leanh::LeanObject,
    mut v_inst_548_: *mut crate::leanh::LeanObject,
    mut v_it_549_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_550_ = crate::leanh::lean_ctor_get(v_inst_546_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_550_);
    v_toFunctor_551_ = crate::leanh::lean_ctor_get(v_toApplicative_550_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_551_);
    v_toBind_552_ = crate::leanh::lean_ctor_get(v_inst_546_, 1);
    crate::leanh::lean_inc(v_toBind_552_);
    crate::leanh::lean_dec_ref(v_inst_546_);
    v_toPure_553_ = crate::leanh::lean_ctor_get(v_toApplicative_550_, 1);
    crate::leanh::lean_inc(v_toPure_553_);
    crate::leanh::lean_dec_ref(v_toApplicative_550_);
    v_map_554_ = crate::leanh::lean_ctor_get(v_toFunctor_551_, 0);
    crate::leanh::lean_inc(v_map_554_);
    crate::leanh::lean_dec_ref(v_toFunctor_551_);
    v___f_555_ = l_Std_IterM_toList___redArg___closed__0;
    v___f_556_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_toArray_go___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    crate::leanh::lean_closure_set(v___f_556_, 0, v_toPure_553_);
    crate::leanh::lean_closure_set(v___f_556_, 1, v_inst_548_);
    crate::leanh::lean_closure_set(v___f_556_, 2, v_toBind_552_);
    v___x_557_ = l_Std_IterM_toArray___redArg___closed__0;
    v___x_558_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_556_, v_it_549_, v___x_557_,
    );
    v___x_559_ = crate::leanh::lean_apply_4(
        v_map_554_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_555_,
        v___x_558_,
    );
    return v___x_559_;
}
pub unsafe fn l_Std_IterM_Partial_toList___redArg(
    mut v_inst_560_: *mut crate::leanh::LeanObject,
    mut v_inst_561_: *mut crate::leanh::LeanObject,
    mut v_it_562_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_563_ = crate::leanh::lean_ctor_get(v_inst_560_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_563_);
    v_toFunctor_564_ = crate::leanh::lean_ctor_get(v_toApplicative_563_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_564_);
    v_toBind_565_ = crate::leanh::lean_ctor_get(v_inst_560_, 1);
    crate::leanh::lean_inc(v_toBind_565_);
    crate::leanh::lean_dec_ref(v_inst_560_);
    v_toPure_566_ = crate::leanh::lean_ctor_get(v_toApplicative_563_, 1);
    crate::leanh::lean_inc(v_toPure_566_);
    crate::leanh::lean_dec_ref(v_toApplicative_563_);
    v_map_567_ = crate::leanh::lean_ctor_get(v_toFunctor_564_, 0);
    crate::leanh::lean_inc(v_map_567_);
    crate::leanh::lean_dec_ref(v_toFunctor_564_);
    v___f_568_ = l_Std_IterM_toList___redArg___closed__0;
    v___f_569_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_toArray_go___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    crate::leanh::lean_closure_set(v___f_569_, 0, v_toPure_566_);
    crate::leanh::lean_closure_set(v___f_569_, 1, v_inst_561_);
    crate::leanh::lean_closure_set(v___f_569_, 2, v_toBind_565_);
    v___x_570_ = l_Std_IterM_toArray___redArg___closed__0;
    v___x_571_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_569_, v_it_562_, v___x_570_,
    );
    v___x_572_ = crate::leanh::lean_apply_4(
        v_map_567_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_568_,
        v___x_571_,
    );
    return v___x_572_;
}
pub unsafe fn l_Std_IterM_Partial_toList(
    mut v_00_u03b1_573_: *mut crate::leanh::LeanObject,
    mut v_m_574_: *mut crate::leanh::LeanObject,
    mut v_inst_575_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_576_: *mut crate::leanh::LeanObject,
    mut v_inst_577_: *mut crate::leanh::LeanObject,
    mut v_it_578_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_579_ = crate::leanh::lean_ctor_get(v_inst_575_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_579_);
    v_toFunctor_580_ = crate::leanh::lean_ctor_get(v_toApplicative_579_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_580_);
    v_toBind_581_ = crate::leanh::lean_ctor_get(v_inst_575_, 1);
    crate::leanh::lean_inc(v_toBind_581_);
    crate::leanh::lean_dec_ref(v_inst_575_);
    v_toPure_582_ = crate::leanh::lean_ctor_get(v_toApplicative_579_, 1);
    crate::leanh::lean_inc(v_toPure_582_);
    crate::leanh::lean_dec_ref(v_toApplicative_579_);
    v_map_583_ = crate::leanh::lean_ctor_get(v_toFunctor_580_, 0);
    crate::leanh::lean_inc(v_map_583_);
    crate::leanh::lean_dec_ref(v_toFunctor_580_);
    v___f_584_ = l_Std_IterM_toList___redArg___closed__0;
    v___f_585_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_toArray_go___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    crate::leanh::lean_closure_set(v___f_585_, 0, v_toPure_582_);
    crate::leanh::lean_closure_set(v___f_585_, 1, v_inst_577_);
    crate::leanh::lean_closure_set(v___f_585_, 2, v_toBind_581_);
    v___x_586_ = l_Std_IterM_toArray___redArg___closed__0;
    v___x_587_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_585_, v_it_578_, v___x_586_,
    );
    v___x_588_ = crate::leanh::lean_apply_4(
        v_map_583_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_584_,
        v___x_587_,
    );
    return v___x_588_;
}
pub unsafe fn l_Std_IterM_Total_toList___redArg(
    mut v_inst_589_: *mut crate::leanh::LeanObject,
    mut v_inst_590_: *mut crate::leanh::LeanObject,
    mut v_it_591_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_592_ = crate::leanh::lean_ctor_get(v_inst_589_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_592_);
    v_toFunctor_593_ = crate::leanh::lean_ctor_get(v_toApplicative_592_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_593_);
    v_toBind_594_ = crate::leanh::lean_ctor_get(v_inst_589_, 1);
    crate::leanh::lean_inc(v_toBind_594_);
    crate::leanh::lean_dec_ref(v_inst_589_);
    v_toPure_595_ = crate::leanh::lean_ctor_get(v_toApplicative_592_, 1);
    crate::leanh::lean_inc(v_toPure_595_);
    crate::leanh::lean_dec_ref(v_toApplicative_592_);
    v_map_596_ = crate::leanh::lean_ctor_get(v_toFunctor_593_, 0);
    crate::leanh::lean_inc(v_map_596_);
    crate::leanh::lean_dec_ref(v_toFunctor_593_);
    v___f_597_ = l_Std_IterM_toList___redArg___closed__0;
    v___f_598_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_toArray_go___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    crate::leanh::lean_closure_set(v___f_598_, 0, v_toPure_595_);
    crate::leanh::lean_closure_set(v___f_598_, 1, v_inst_590_);
    crate::leanh::lean_closure_set(v___f_598_, 2, v_toBind_594_);
    v___x_599_ = l_Std_IterM_toArray___redArg___closed__0;
    v___x_600_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_598_, v_it_591_, v___x_599_,
    );
    v___x_601_ = crate::leanh::lean_apply_4(
        v_map_596_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_597_,
        v___x_600_,
    );
    return v___x_601_;
}
pub unsafe fn l_Std_IterM_Total_toList(
    mut v_00_u03b1_602_: *mut crate::leanh::LeanObject,
    mut v_m_603_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_604_: *mut crate::leanh::LeanObject,
    mut v_inst_605_: *mut crate::leanh::LeanObject,
    mut v_inst_606_: *mut crate::leanh::LeanObject,
    mut v_inst_607_: *mut crate::leanh::LeanObject,
    mut v_it_608_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_609_ = crate::leanh::lean_ctor_get(v_inst_605_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_609_);
    v_toFunctor_610_ = crate::leanh::lean_ctor_get(v_toApplicative_609_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_610_);
    v_toBind_611_ = crate::leanh::lean_ctor_get(v_inst_605_, 1);
    crate::leanh::lean_inc(v_toBind_611_);
    crate::leanh::lean_dec_ref(v_inst_605_);
    v_toPure_612_ = crate::leanh::lean_ctor_get(v_toApplicative_609_, 1);
    crate::leanh::lean_inc(v_toPure_612_);
    crate::leanh::lean_dec_ref(v_toApplicative_609_);
    v_map_613_ = crate::leanh::lean_ctor_get(v_toFunctor_610_, 0);
    crate::leanh::lean_inc(v_map_613_);
    crate::leanh::lean_dec_ref(v_toFunctor_610_);
    v___f_614_ = l_Std_IterM_toList___redArg___closed__0;
    v___f_615_ = crate::leanh::lean_alloc_closure(
        l_Std_IterM_toArray_go___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    crate::leanh::lean_closure_set(v___f_615_, 0, v_toPure_612_);
    crate::leanh::lean_closure_set(v___f_615_, 1, v_inst_606_);
    crate::leanh::lean_closure_set(v___f_615_, 2, v_toBind_611_);
    v___x_616_ = l_Std_IterM_toArray___redArg___closed__0;
    v___x_617_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_615_, v_it_608_, v___x_616_,
    );
    v___x_618_ = crate::leanh::lean_apply_4(
        v_map_613_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_614_,
        v___x_617_,
    );
    return v___x_618_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Partial(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Total(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_WFExtrinsicFix(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Ext(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(
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
pub unsafe fn initialize_Init_Data_Iterators_Consumers_Monadic_Collect(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Consumers_Monadic_Partial(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Monadic_Total(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_WFExtrinsicFix(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Ext(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
}
