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
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get,
    lean_ctor_set, lean_ctor_set_tag, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc,
    lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_tag,
};
pub static l_Std_IterM_toArray___redArg___closed__0_value: LeanArrayObject<0> = LeanArrayObject {
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
static mut l_Std_IterM_toArray___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_IterM_toArray___redArg___closed__0_value) as *mut LeanObject;
pub static l_Std_IterM_toList___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_IterM_toList___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_IterM_toList___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_IterM_toList___redArg___closed__0_value) as *mut LeanObject;
pub unsafe fn l_Std_IterM_toArray_go___redArg___lam__0(
    mut v_acc_310_: *mut LeanObject,
    mut v_recur_311_: *mut LeanObject,
    mut v_toPure_312_: *mut LeanObject,
    mut v_____do__lift_313_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_____do__lift_313_) {
        0 => {
            let mut v_it_314_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_315_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_316_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_317_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_toPure_312_);
            v_it_314_ = lean_ctor_get(v_____do__lift_313_, 0);
            lean_inc(v_it_314_);
            v_out_315_ = lean_ctor_get(v_____do__lift_313_, 1);
            lean_inc(v_out_315_);
            lean_dec_ref_known(v_____do__lift_313_, 2);
            v___x_316_ = lean_array_push(v_acc_310_, v_out_315_);
            v___x_317_ = lean_apply_3(v_recur_311_, v_it_314_, v___x_316_, lean_box(0));
            return v___x_317_;
        }
        1 => {
            let mut v_it_318_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_319_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_toPure_312_);
            v_it_318_ = lean_ctor_get(v_____do__lift_313_, 0);
            lean_inc(v_it_318_);
            lean_dec_ref_known(v_____do__lift_313_, 1);
            v___x_319_ = lean_apply_3(v_recur_311_, v_it_318_, v_acc_310_, lean_box(0));
            return v___x_319_;
        }
        _ => {
            let mut v___x_320_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_recur_311_);
            v___x_320_ = lean_apply_2(v_toPure_312_, lean_box(0), v_acc_310_);
            return v___x_320_;
        }
    }
}
pub unsafe fn l_Std_IterM_toArray_go___redArg___lam__1(
    mut v_toPure_321_: *mut LeanObject,
    mut v_inst_322_: *mut LeanObject,
    mut v_toBind_323_: *mut LeanObject,
    mut v_it_324_: *mut LeanObject,
    mut v_acc_325_: *mut LeanObject,
    mut v_recur_326_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_329_: *mut LeanObject = core::ptr::null_mut();
    v___f_327_ = lean_alloc_closure(
        l_Std_IterM_toArray_go___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_327_, 0, v_acc_325_);
    lean_closure_set(v___f_327_, 1, v_recur_326_);
    lean_closure_set(v___f_327_, 2, v_toPure_321_);
    v___x_328_ = lean_apply_1(v_inst_322_, v_it_324_);
    v___x_329_ = lean_apply_4(
        v_toBind_323_,
        lean_box(0),
        lean_box(0),
        v___x_328_,
        v___f_327_,
    );
    return v___x_329_;
}
pub unsafe fn l_Std_IterM_toArray_go___redArg(
    mut v_inst_330_: *mut LeanObject,
    mut v_inst_331_: *mut LeanObject,
    mut v_it_332_: *mut LeanObject,
    mut v_acc_333_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_338_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_334_ = lean_ctor_get(v_inst_330_, 0);
    lean_inc_ref(v_toApplicative_334_);
    v_toBind_335_ = lean_ctor_get(v_inst_330_, 1);
    lean_inc(v_toBind_335_);
    lean_dec_ref(v_inst_330_);
    v_toPure_336_ = lean_ctor_get(v_toApplicative_334_, 1);
    lean_inc(v_toPure_336_);
    lean_dec_ref(v_toApplicative_334_);
    v___f_337_ = lean_alloc_closure(
        l_Std_IterM_toArray_go___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    lean_closure_set(v___f_337_, 0, v_toPure_336_);
    lean_closure_set(v___f_337_, 1, v_inst_331_);
    lean_closure_set(v___f_337_, 2, v_toBind_335_);
    v___x_338_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_337_, v_it_332_, v_acc_333_,
    );
    return v___x_338_;
}
pub unsafe fn l_Std_IterM_toArray_go(
    mut v_00_u03b1_339_: *mut LeanObject,
    mut v_00_u03b2_340_: *mut LeanObject,
    mut v_m_341_: *mut LeanObject,
    mut v_inst_342_: *mut LeanObject,
    mut v_inst_343_: *mut LeanObject,
    mut v_it_344_: *mut LeanObject,
    mut v_acc_345_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_350_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_346_ = lean_ctor_get(v_inst_342_, 0);
    lean_inc_ref(v_toApplicative_346_);
    v_toBind_347_ = lean_ctor_get(v_inst_342_, 1);
    lean_inc(v_toBind_347_);
    lean_dec_ref(v_inst_342_);
    v_toPure_348_ = lean_ctor_get(v_toApplicative_346_, 1);
    lean_inc(v_toPure_348_);
    lean_dec_ref(v_toApplicative_346_);
    v___f_349_ = lean_alloc_closure(
        l_Std_IterM_toArray_go___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    lean_closure_set(v___f_349_, 0, v_toPure_348_);
    lean_closure_set(v___f_349_, 1, v_inst_343_);
    lean_closure_set(v___f_349_, 2, v_toBind_347_);
    v___x_350_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_349_, v_it_344_, v_acc_345_,
    );
    return v___x_350_;
}
pub unsafe fn l_Std_IterM_toArray___redArg(
    mut v_inst_353_: *mut LeanObject,
    mut v_inst_354_: *mut LeanObject,
    mut v_it_355_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_361_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_356_ = lean_ctor_get(v_inst_353_, 0);
    lean_inc_ref(v_toApplicative_356_);
    v_toBind_357_ = lean_ctor_get(v_inst_353_, 1);
    lean_inc(v_toBind_357_);
    lean_dec_ref(v_inst_353_);
    v_toPure_358_ = lean_ctor_get(v_toApplicative_356_, 1);
    lean_inc(v_toPure_358_);
    lean_dec_ref(v_toApplicative_356_);
    v___x_359_ = l_Std_IterM_toArray___redArg___closed__0;
    v___f_360_ = lean_alloc_closure(
        l_Std_IterM_toArray_go___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    lean_closure_set(v___f_360_, 0, v_toPure_358_);
    lean_closure_set(v___f_360_, 1, v_inst_354_);
    lean_closure_set(v___f_360_, 2, v_toBind_357_);
    v___x_361_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_360_, v_it_355_, v___x_359_,
    );
    return v___x_361_;
}
pub unsafe fn l_Std_IterM_toArray(
    mut v_00_u03b1_362_: *mut LeanObject,
    mut v_00_u03b2_363_: *mut LeanObject,
    mut v_m_364_: *mut LeanObject,
    mut v_inst_365_: *mut LeanObject,
    mut v_inst_366_: *mut LeanObject,
    mut v_it_367_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_373_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_368_ = lean_ctor_get(v_inst_365_, 0);
    lean_inc_ref(v_toApplicative_368_);
    v_toBind_369_ = lean_ctor_get(v_inst_365_, 1);
    lean_inc(v_toBind_369_);
    lean_dec_ref(v_inst_365_);
    v_toPure_370_ = lean_ctor_get(v_toApplicative_368_, 1);
    lean_inc(v_toPure_370_);
    lean_dec_ref(v_toApplicative_368_);
    v___x_371_ = l_Std_IterM_toArray___redArg___closed__0;
    v___f_372_ = lean_alloc_closure(
        l_Std_IterM_toArray_go___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    lean_closure_set(v___f_372_, 0, v_toPure_370_);
    lean_closure_set(v___f_372_, 1, v_inst_366_);
    lean_closure_set(v___f_372_, 2, v_toBind_369_);
    v___x_373_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_372_, v_it_367_, v___x_371_,
    );
    return v___x_373_;
}
pub unsafe fn l_Std_IterM_Partial_toArray___redArg(
    mut v_inst_374_: *mut LeanObject,
    mut v_inst_375_: *mut LeanObject,
    mut v_it_376_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_382_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_377_ = lean_ctor_get(v_inst_374_, 0);
    lean_inc_ref(v_toApplicative_377_);
    v_toBind_378_ = lean_ctor_get(v_inst_374_, 1);
    lean_inc(v_toBind_378_);
    lean_dec_ref(v_inst_374_);
    v_toPure_379_ = lean_ctor_get(v_toApplicative_377_, 1);
    lean_inc(v_toPure_379_);
    lean_dec_ref(v_toApplicative_377_);
    v___x_380_ = l_Std_IterM_toArray___redArg___closed__0;
    v___f_381_ = lean_alloc_closure(
        l_Std_IterM_toArray_go___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    lean_closure_set(v___f_381_, 0, v_toPure_379_);
    lean_closure_set(v___f_381_, 1, v_inst_375_);
    lean_closure_set(v___f_381_, 2, v_toBind_378_);
    v___x_382_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_381_, v_it_376_, v___x_380_,
    );
    return v___x_382_;
}
pub unsafe fn l_Std_IterM_Partial_toArray(
    mut v_00_u03b1_383_: *mut LeanObject,
    mut v_m_384_: *mut LeanObject,
    mut v_00_u03b2_385_: *mut LeanObject,
    mut v_inst_386_: *mut LeanObject,
    mut v_inst_387_: *mut LeanObject,
    mut v_it_388_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_394_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_389_ = lean_ctor_get(v_inst_386_, 0);
    lean_inc_ref(v_toApplicative_389_);
    v_toBind_390_ = lean_ctor_get(v_inst_386_, 1);
    lean_inc(v_toBind_390_);
    lean_dec_ref(v_inst_386_);
    v_toPure_391_ = lean_ctor_get(v_toApplicative_389_, 1);
    lean_inc(v_toPure_391_);
    lean_dec_ref(v_toApplicative_389_);
    v___x_392_ = l_Std_IterM_toArray___redArg___closed__0;
    v___f_393_ = lean_alloc_closure(
        l_Std_IterM_toArray_go___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    lean_closure_set(v___f_393_, 0, v_toPure_391_);
    lean_closure_set(v___f_393_, 1, v_inst_387_);
    lean_closure_set(v___f_393_, 2, v_toBind_390_);
    v___x_394_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_393_, v_it_388_, v___x_392_,
    );
    return v___x_394_;
}
pub unsafe fn l_Std_IterM_Total_toArray___redArg(
    mut v_inst_395_: *mut LeanObject,
    mut v_inst_396_: *mut LeanObject,
    mut v_it_397_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_403_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_398_ = lean_ctor_get(v_inst_395_, 0);
    lean_inc_ref(v_toApplicative_398_);
    v_toBind_399_ = lean_ctor_get(v_inst_395_, 1);
    lean_inc(v_toBind_399_);
    lean_dec_ref(v_inst_395_);
    v_toPure_400_ = lean_ctor_get(v_toApplicative_398_, 1);
    lean_inc(v_toPure_400_);
    lean_dec_ref(v_toApplicative_398_);
    v___x_401_ = l_Std_IterM_toArray___redArg___closed__0;
    v___f_402_ = lean_alloc_closure(
        l_Std_IterM_toArray_go___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    lean_closure_set(v___f_402_, 0, v_toPure_400_);
    lean_closure_set(v___f_402_, 1, v_inst_396_);
    lean_closure_set(v___f_402_, 2, v_toBind_399_);
    v___x_403_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_402_, v_it_397_, v___x_401_,
    );
    return v___x_403_;
}
pub unsafe fn l_Std_IterM_Total_toArray(
    mut v_00_u03b1_404_: *mut LeanObject,
    mut v_m_405_: *mut LeanObject,
    mut v_00_u03b2_406_: *mut LeanObject,
    mut v_inst_407_: *mut LeanObject,
    mut v_inst_408_: *mut LeanObject,
    mut v_inst_409_: *mut LeanObject,
    mut v_it_410_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_416_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_411_ = lean_ctor_get(v_inst_407_, 0);
    lean_inc_ref(v_toApplicative_411_);
    v_toBind_412_ = lean_ctor_get(v_inst_407_, 1);
    lean_inc(v_toBind_412_);
    lean_dec_ref(v_inst_407_);
    v_toPure_413_ = lean_ctor_get(v_toApplicative_411_, 1);
    lean_inc(v_toPure_413_);
    lean_dec_ref(v_toApplicative_411_);
    v___x_414_ = l_Std_IterM_toArray___redArg___closed__0;
    v___f_415_ = lean_alloc_closure(
        l_Std_IterM_toArray_go___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    lean_closure_set(v___f_415_, 0, v_toPure_413_);
    lean_closure_set(v___f_415_, 1, v_inst_408_);
    lean_closure_set(v___f_415_, 2, v_toBind_412_);
    v___x_416_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_415_, v_it_410_, v___x_414_,
    );
    return v___x_416_;
}
pub unsafe fn l_Std_IterM_toListRev_go___redArg___lam__0(
    mut v_acc_417_: *mut LeanObject,
    mut v_recur_418_: *mut LeanObject,
    mut v_toPure_419_: *mut LeanObject,
    mut v_____do__lift_420_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_it_421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_out_422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_425_: u8 = 0;
    let mut v___x_427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_430_: u8 = 0;
    let mut v_it_431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_433_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_____do__lift_420_) {
                0 => {
                    lean_dec(v_toPure_419_);
                    v_it_421_ = lean_ctor_get(v_____do__lift_420_, 0);
                    v_out_422_ = lean_ctor_get(v_____do__lift_420_, 1);
                    v_isSharedCheck_430_ = (!lean_is_exclusive(v_____do__lift_420_)) as u8;
                    if v_isSharedCheck_430_ == 0 {
                        v___x_424_ = v_____do__lift_420_;
                        v_isShared_425_ = v_isSharedCheck_430_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_out_422_);
                        lean_inc(v_it_421_);
                        lean_dec(v_____do__lift_420_);
                        v___x_424_ = lean_box(0);
                        v_isShared_425_ = v_isSharedCheck_430_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    lean_dec(v_toPure_419_);
                    v_it_431_ = lean_ctor_get(v_____do__lift_420_, 0);
                    lean_inc(v_it_431_);
                    lean_dec_ref_known(v_____do__lift_420_, 1);
                    v___x_432_ = lean_apply_3(v_recur_418_, v_it_431_, v_acc_417_, lean_box(0));
                    return v___x_432_;
                }
                _ => {
                    lean_dec(v_recur_418_);
                    v___x_433_ = lean_apply_2(v_toPure_419_, lean_box(0), v_acc_417_);
                    return v___x_433_;
                }
            },
            1 => {
                if v_isShared_425_ == 0 {
                    lean_ctor_set_tag(v___x_424_, 1);
                    lean_ctor_set(v___x_424_, 1, v_acc_417_);
                    lean_ctor_set(v___x_424_, 0, v_out_422_);
                    v___x_427_ = v___x_424_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_429_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_429_, 0, v_out_422_);
                    lean_ctor_set(v_reuseFailAlloc_429_, 1, v_acc_417_);
                    v___x_427_ = v_reuseFailAlloc_429_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_428_ = lean_apply_3(v_recur_418_, v_it_421_, v___x_427_, lean_box(0));
                return v___x_428_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_IterM_toListRev_go___redArg___lam__1(
    mut v_toPure_434_: *mut LeanObject,
    mut v_inst_435_: *mut LeanObject,
    mut v_toBind_436_: *mut LeanObject,
    mut v_it_437_: *mut LeanObject,
    mut v_acc_438_: *mut LeanObject,
    mut v_recur_439_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_442_: *mut LeanObject = core::ptr::null_mut();
    v___f_440_ = lean_alloc_closure(
        l_Std_IterM_toListRev_go___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_440_, 0, v_acc_438_);
    lean_closure_set(v___f_440_, 1, v_recur_439_);
    lean_closure_set(v___f_440_, 2, v_toPure_434_);
    v___x_441_ = lean_apply_1(v_inst_435_, v_it_437_);
    v___x_442_ = lean_apply_4(
        v_toBind_436_,
        lean_box(0),
        lean_box(0),
        v___x_441_,
        v___f_440_,
    );
    return v___x_442_;
}
pub unsafe fn l_Std_IterM_toListRev_go___redArg(
    mut v_inst_443_: *mut LeanObject,
    mut v_inst_444_: *mut LeanObject,
    mut v_it_445_: *mut LeanObject,
    mut v_acc_446_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_451_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_447_ = lean_ctor_get(v_inst_443_, 0);
    lean_inc_ref(v_toApplicative_447_);
    v_toBind_448_ = lean_ctor_get(v_inst_443_, 1);
    lean_inc(v_toBind_448_);
    lean_dec_ref(v_inst_443_);
    v_toPure_449_ = lean_ctor_get(v_toApplicative_447_, 1);
    lean_inc(v_toPure_449_);
    lean_dec_ref(v_toApplicative_447_);
    v___f_450_ = lean_alloc_closure(
        l_Std_IterM_toListRev_go___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    lean_closure_set(v___f_450_, 0, v_toPure_449_);
    lean_closure_set(v___f_450_, 1, v_inst_444_);
    lean_closure_set(v___f_450_, 2, v_toBind_448_);
    v___x_451_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_450_, v_it_445_, v_acc_446_,
    );
    return v___x_451_;
}
pub unsafe fn l_Std_IterM_toListRev_go(
    mut v_00_u03b1_452_: *mut LeanObject,
    mut v_m_453_: *mut LeanObject,
    mut v_inst_454_: *mut LeanObject,
    mut v_00_u03b2_455_: *mut LeanObject,
    mut v_inst_456_: *mut LeanObject,
    mut v_it_457_: *mut LeanObject,
    mut v_acc_458_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_463_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_459_ = lean_ctor_get(v_inst_454_, 0);
    lean_inc_ref(v_toApplicative_459_);
    v_toBind_460_ = lean_ctor_get(v_inst_454_, 1);
    lean_inc(v_toBind_460_);
    lean_dec_ref(v_inst_454_);
    v_toPure_461_ = lean_ctor_get(v_toApplicative_459_, 1);
    lean_inc(v_toPure_461_);
    lean_dec_ref(v_toApplicative_459_);
    v___f_462_ = lean_alloc_closure(
        l_Std_IterM_toListRev_go___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    lean_closure_set(v___f_462_, 0, v_toPure_461_);
    lean_closure_set(v___f_462_, 1, v_inst_456_);
    lean_closure_set(v___f_462_, 2, v_toBind_460_);
    v___x_463_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_462_, v_it_457_, v_acc_458_,
    );
    return v___x_463_;
}
pub unsafe fn l_Std_IterM_toListRev___redArg(
    mut v_inst_464_: *mut LeanObject,
    mut v_inst_465_: *mut LeanObject,
    mut v_it_466_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_472_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_467_ = lean_ctor_get(v_inst_464_, 0);
    lean_inc_ref(v_toApplicative_467_);
    v_toBind_468_ = lean_ctor_get(v_inst_464_, 1);
    lean_inc(v_toBind_468_);
    lean_dec_ref(v_inst_464_);
    v_toPure_469_ = lean_ctor_get(v_toApplicative_467_, 1);
    lean_inc(v_toPure_469_);
    lean_dec_ref(v_toApplicative_467_);
    v___x_470_ = lean_box(0);
    v___f_471_ = lean_alloc_closure(
        l_Std_IterM_toListRev_go___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    lean_closure_set(v___f_471_, 0, v_toPure_469_);
    lean_closure_set(v___f_471_, 1, v_inst_465_);
    lean_closure_set(v___f_471_, 2, v_toBind_468_);
    v___x_472_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_471_, v_it_466_, v___x_470_,
    );
    return v___x_472_;
}
pub unsafe fn l_Std_IterM_toListRev(
    mut v_00_u03b1_473_: *mut LeanObject,
    mut v_m_474_: *mut LeanObject,
    mut v_inst_475_: *mut LeanObject,
    mut v_00_u03b2_476_: *mut LeanObject,
    mut v_inst_477_: *mut LeanObject,
    mut v_it_478_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_484_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_479_ = lean_ctor_get(v_inst_475_, 0);
    lean_inc_ref(v_toApplicative_479_);
    v_toBind_480_ = lean_ctor_get(v_inst_475_, 1);
    lean_inc(v_toBind_480_);
    lean_dec_ref(v_inst_475_);
    v_toPure_481_ = lean_ctor_get(v_toApplicative_479_, 1);
    lean_inc(v_toPure_481_);
    lean_dec_ref(v_toApplicative_479_);
    v___x_482_ = lean_box(0);
    v___f_483_ = lean_alloc_closure(
        l_Std_IterM_toListRev_go___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    lean_closure_set(v___f_483_, 0, v_toPure_481_);
    lean_closure_set(v___f_483_, 1, v_inst_477_);
    lean_closure_set(v___f_483_, 2, v_toBind_480_);
    v___x_484_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_483_, v_it_478_, v___x_482_,
    );
    return v___x_484_;
}
pub unsafe fn l_Std_IterM_Partial_toListRev___redArg(
    mut v_inst_485_: *mut LeanObject,
    mut v_inst_486_: *mut LeanObject,
    mut v_it_487_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_493_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_488_ = lean_ctor_get(v_inst_485_, 0);
    lean_inc_ref(v_toApplicative_488_);
    v_toBind_489_ = lean_ctor_get(v_inst_485_, 1);
    lean_inc(v_toBind_489_);
    lean_dec_ref(v_inst_485_);
    v_toPure_490_ = lean_ctor_get(v_toApplicative_488_, 1);
    lean_inc(v_toPure_490_);
    lean_dec_ref(v_toApplicative_488_);
    v___x_491_ = lean_box(0);
    v___f_492_ = lean_alloc_closure(
        l_Std_IterM_toListRev_go___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    lean_closure_set(v___f_492_, 0, v_toPure_490_);
    lean_closure_set(v___f_492_, 1, v_inst_486_);
    lean_closure_set(v___f_492_, 2, v_toBind_489_);
    v___x_493_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_492_, v_it_487_, v___x_491_,
    );
    return v___x_493_;
}
pub unsafe fn l_Std_IterM_Partial_toListRev(
    mut v_00_u03b1_494_: *mut LeanObject,
    mut v_m_495_: *mut LeanObject,
    mut v_inst_496_: *mut LeanObject,
    mut v_00_u03b2_497_: *mut LeanObject,
    mut v_inst_498_: *mut LeanObject,
    mut v_it_499_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_505_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_500_ = lean_ctor_get(v_inst_496_, 0);
    lean_inc_ref(v_toApplicative_500_);
    v_toBind_501_ = lean_ctor_get(v_inst_496_, 1);
    lean_inc(v_toBind_501_);
    lean_dec_ref(v_inst_496_);
    v_toPure_502_ = lean_ctor_get(v_toApplicative_500_, 1);
    lean_inc(v_toPure_502_);
    lean_dec_ref(v_toApplicative_500_);
    v___x_503_ = lean_box(0);
    v___f_504_ = lean_alloc_closure(
        l_Std_IterM_toListRev_go___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    lean_closure_set(v___f_504_, 0, v_toPure_502_);
    lean_closure_set(v___f_504_, 1, v_inst_498_);
    lean_closure_set(v___f_504_, 2, v_toBind_501_);
    v___x_505_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_504_, v_it_499_, v___x_503_,
    );
    return v___x_505_;
}
pub unsafe fn l_Std_IterM_Total_toListRev___redArg(
    mut v_inst_506_: *mut LeanObject,
    mut v_inst_507_: *mut LeanObject,
    mut v_it_508_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_514_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_509_ = lean_ctor_get(v_inst_506_, 0);
    lean_inc_ref(v_toApplicative_509_);
    v_toBind_510_ = lean_ctor_get(v_inst_506_, 1);
    lean_inc(v_toBind_510_);
    lean_dec_ref(v_inst_506_);
    v_toPure_511_ = lean_ctor_get(v_toApplicative_509_, 1);
    lean_inc(v_toPure_511_);
    lean_dec_ref(v_toApplicative_509_);
    v___x_512_ = lean_box(0);
    v___f_513_ = lean_alloc_closure(
        l_Std_IterM_toListRev_go___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    lean_closure_set(v___f_513_, 0, v_toPure_511_);
    lean_closure_set(v___f_513_, 1, v_inst_507_);
    lean_closure_set(v___f_513_, 2, v_toBind_510_);
    v___x_514_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_513_, v_it_508_, v___x_512_,
    );
    return v___x_514_;
}
pub unsafe fn l_Std_IterM_Total_toListRev(
    mut v_00_u03b1_515_: *mut LeanObject,
    mut v_m_516_: *mut LeanObject,
    mut v_00_u03b2_517_: *mut LeanObject,
    mut v_inst_518_: *mut LeanObject,
    mut v_inst_519_: *mut LeanObject,
    mut v_inst_520_: *mut LeanObject,
    mut v_it_521_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_527_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_522_ = lean_ctor_get(v_inst_518_, 0);
    lean_inc_ref(v_toApplicative_522_);
    v_toBind_523_ = lean_ctor_get(v_inst_518_, 1);
    lean_inc(v_toBind_523_);
    lean_dec_ref(v_inst_518_);
    v_toPure_524_ = lean_ctor_get(v_toApplicative_522_, 1);
    lean_inc(v_toPure_524_);
    lean_dec_ref(v_toApplicative_522_);
    v___x_525_ = lean_box(0);
    v___f_526_ = lean_alloc_closure(
        l_Std_IterM_toListRev_go___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    lean_closure_set(v___f_526_, 0, v_toPure_524_);
    lean_closure_set(v___f_526_, 1, v_inst_519_);
    lean_closure_set(v___f_526_, 2, v_toBind_523_);
    v___x_527_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_526_, v_it_521_, v___x_525_,
    );
    return v___x_527_;
}
pub unsafe fn l_Std_IterM_toList___redArg___lam__0(
    mut v_self_528_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_529_: *mut LeanObject = core::ptr::null_mut();
    v___x_529_ = lean_array_to_list(v_self_528_);
    return v___x_529_;
}
pub unsafe fn l_Std_IterM_toList___redArg(
    mut v_inst_531_: *mut LeanObject,
    mut v_inst_532_: *mut LeanObject,
    mut v_it_533_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_543_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_534_ = lean_ctor_get(v_inst_531_, 0);
    lean_inc_ref(v_toApplicative_534_);
    v_toFunctor_535_ = lean_ctor_get(v_toApplicative_534_, 0);
    lean_inc_ref(v_toFunctor_535_);
    v_toBind_536_ = lean_ctor_get(v_inst_531_, 1);
    lean_inc(v_toBind_536_);
    lean_dec_ref(v_inst_531_);
    v_toPure_537_ = lean_ctor_get(v_toApplicative_534_, 1);
    lean_inc(v_toPure_537_);
    lean_dec_ref(v_toApplicative_534_);
    v_map_538_ = lean_ctor_get(v_toFunctor_535_, 0);
    lean_inc(v_map_538_);
    lean_dec_ref(v_toFunctor_535_);
    v___f_539_ = l_Std_IterM_toList___redArg___closed__0;
    v___f_540_ = lean_alloc_closure(
        l_Std_IterM_toArray_go___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    lean_closure_set(v___f_540_, 0, v_toPure_537_);
    lean_closure_set(v___f_540_, 1, v_inst_532_);
    lean_closure_set(v___f_540_, 2, v_toBind_536_);
    v___x_541_ = l_Std_IterM_toArray___redArg___closed__0;
    v___x_542_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_540_, v_it_533_, v___x_541_,
    );
    v___x_543_ = lean_apply_4(v_map_538_, lean_box(0), lean_box(0), v___f_539_, v___x_542_);
    return v___x_543_;
}
pub unsafe fn l_Std_IterM_toList(
    mut v_00_u03b1_544_: *mut LeanObject,
    mut v_m_545_: *mut LeanObject,
    mut v_inst_546_: *mut LeanObject,
    mut v_00_u03b2_547_: *mut LeanObject,
    mut v_inst_548_: *mut LeanObject,
    mut v_it_549_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_559_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_550_ = lean_ctor_get(v_inst_546_, 0);
    lean_inc_ref(v_toApplicative_550_);
    v_toFunctor_551_ = lean_ctor_get(v_toApplicative_550_, 0);
    lean_inc_ref(v_toFunctor_551_);
    v_toBind_552_ = lean_ctor_get(v_inst_546_, 1);
    lean_inc(v_toBind_552_);
    lean_dec_ref(v_inst_546_);
    v_toPure_553_ = lean_ctor_get(v_toApplicative_550_, 1);
    lean_inc(v_toPure_553_);
    lean_dec_ref(v_toApplicative_550_);
    v_map_554_ = lean_ctor_get(v_toFunctor_551_, 0);
    lean_inc(v_map_554_);
    lean_dec_ref(v_toFunctor_551_);
    v___f_555_ = l_Std_IterM_toList___redArg___closed__0;
    v___f_556_ = lean_alloc_closure(
        l_Std_IterM_toArray_go___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    lean_closure_set(v___f_556_, 0, v_toPure_553_);
    lean_closure_set(v___f_556_, 1, v_inst_548_);
    lean_closure_set(v___f_556_, 2, v_toBind_552_);
    v___x_557_ = l_Std_IterM_toArray___redArg___closed__0;
    v___x_558_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_556_, v_it_549_, v___x_557_,
    );
    v___x_559_ = lean_apply_4(v_map_554_, lean_box(0), lean_box(0), v___f_555_, v___x_558_);
    return v___x_559_;
}
pub unsafe fn l_Std_IterM_Partial_toList___redArg(
    mut v_inst_560_: *mut LeanObject,
    mut v_inst_561_: *mut LeanObject,
    mut v_it_562_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_572_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_563_ = lean_ctor_get(v_inst_560_, 0);
    lean_inc_ref(v_toApplicative_563_);
    v_toFunctor_564_ = lean_ctor_get(v_toApplicative_563_, 0);
    lean_inc_ref(v_toFunctor_564_);
    v_toBind_565_ = lean_ctor_get(v_inst_560_, 1);
    lean_inc(v_toBind_565_);
    lean_dec_ref(v_inst_560_);
    v_toPure_566_ = lean_ctor_get(v_toApplicative_563_, 1);
    lean_inc(v_toPure_566_);
    lean_dec_ref(v_toApplicative_563_);
    v_map_567_ = lean_ctor_get(v_toFunctor_564_, 0);
    lean_inc(v_map_567_);
    lean_dec_ref(v_toFunctor_564_);
    v___f_568_ = l_Std_IterM_toList___redArg___closed__0;
    v___f_569_ = lean_alloc_closure(
        l_Std_IterM_toArray_go___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    lean_closure_set(v___f_569_, 0, v_toPure_566_);
    lean_closure_set(v___f_569_, 1, v_inst_561_);
    lean_closure_set(v___f_569_, 2, v_toBind_565_);
    v___x_570_ = l_Std_IterM_toArray___redArg___closed__0;
    v___x_571_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_569_, v_it_562_, v___x_570_,
    );
    v___x_572_ = lean_apply_4(v_map_567_, lean_box(0), lean_box(0), v___f_568_, v___x_571_);
    return v___x_572_;
}
pub unsafe fn l_Std_IterM_Partial_toList(
    mut v_00_u03b1_573_: *mut LeanObject,
    mut v_m_574_: *mut LeanObject,
    mut v_inst_575_: *mut LeanObject,
    mut v_00_u03b2_576_: *mut LeanObject,
    mut v_inst_577_: *mut LeanObject,
    mut v_it_578_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_588_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_579_ = lean_ctor_get(v_inst_575_, 0);
    lean_inc_ref(v_toApplicative_579_);
    v_toFunctor_580_ = lean_ctor_get(v_toApplicative_579_, 0);
    lean_inc_ref(v_toFunctor_580_);
    v_toBind_581_ = lean_ctor_get(v_inst_575_, 1);
    lean_inc(v_toBind_581_);
    lean_dec_ref(v_inst_575_);
    v_toPure_582_ = lean_ctor_get(v_toApplicative_579_, 1);
    lean_inc(v_toPure_582_);
    lean_dec_ref(v_toApplicative_579_);
    v_map_583_ = lean_ctor_get(v_toFunctor_580_, 0);
    lean_inc(v_map_583_);
    lean_dec_ref(v_toFunctor_580_);
    v___f_584_ = l_Std_IterM_toList___redArg___closed__0;
    v___f_585_ = lean_alloc_closure(
        l_Std_IterM_toArray_go___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    lean_closure_set(v___f_585_, 0, v_toPure_582_);
    lean_closure_set(v___f_585_, 1, v_inst_577_);
    lean_closure_set(v___f_585_, 2, v_toBind_581_);
    v___x_586_ = l_Std_IterM_toArray___redArg___closed__0;
    v___x_587_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_585_, v_it_578_, v___x_586_,
    );
    v___x_588_ = lean_apply_4(v_map_583_, lean_box(0), lean_box(0), v___f_584_, v___x_587_);
    return v___x_588_;
}
pub unsafe fn l_Std_IterM_Total_toList___redArg(
    mut v_inst_589_: *mut LeanObject,
    mut v_inst_590_: *mut LeanObject,
    mut v_it_591_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_601_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_592_ = lean_ctor_get(v_inst_589_, 0);
    lean_inc_ref(v_toApplicative_592_);
    v_toFunctor_593_ = lean_ctor_get(v_toApplicative_592_, 0);
    lean_inc_ref(v_toFunctor_593_);
    v_toBind_594_ = lean_ctor_get(v_inst_589_, 1);
    lean_inc(v_toBind_594_);
    lean_dec_ref(v_inst_589_);
    v_toPure_595_ = lean_ctor_get(v_toApplicative_592_, 1);
    lean_inc(v_toPure_595_);
    lean_dec_ref(v_toApplicative_592_);
    v_map_596_ = lean_ctor_get(v_toFunctor_593_, 0);
    lean_inc(v_map_596_);
    lean_dec_ref(v_toFunctor_593_);
    v___f_597_ = l_Std_IterM_toList___redArg___closed__0;
    v___f_598_ = lean_alloc_closure(
        l_Std_IterM_toArray_go___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    lean_closure_set(v___f_598_, 0, v_toPure_595_);
    lean_closure_set(v___f_598_, 1, v_inst_590_);
    lean_closure_set(v___f_598_, 2, v_toBind_594_);
    v___x_599_ = l_Std_IterM_toArray___redArg___closed__0;
    v___x_600_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_598_, v_it_591_, v___x_599_,
    );
    v___x_601_ = lean_apply_4(v_map_596_, lean_box(0), lean_box(0), v___f_597_, v___x_600_);
    return v___x_601_;
}
pub unsafe fn l_Std_IterM_Total_toList(
    mut v_00_u03b1_602_: *mut LeanObject,
    mut v_m_603_: *mut LeanObject,
    mut v_00_u03b2_604_: *mut LeanObject,
    mut v_inst_605_: *mut LeanObject,
    mut v_inst_606_: *mut LeanObject,
    mut v_inst_607_: *mut LeanObject,
    mut v_it_608_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_618_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_609_ = lean_ctor_get(v_inst_605_, 0);
    lean_inc_ref(v_toApplicative_609_);
    v_toFunctor_610_ = lean_ctor_get(v_toApplicative_609_, 0);
    lean_inc_ref(v_toFunctor_610_);
    v_toBind_611_ = lean_ctor_get(v_inst_605_, 1);
    lean_inc(v_toBind_611_);
    lean_dec_ref(v_inst_605_);
    v_toPure_612_ = lean_ctor_get(v_toApplicative_609_, 1);
    lean_inc(v_toPure_612_);
    lean_dec_ref(v_toApplicative_609_);
    v_map_613_ = lean_ctor_get(v_toFunctor_610_, 0);
    lean_inc(v_map_613_);
    lean_dec_ref(v_toFunctor_610_);
    v___f_614_ = l_Std_IterM_toList___redArg___closed__0;
    v___f_615_ = lean_alloc_closure(
        l_Std_IterM_toArray_go___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    lean_closure_set(v___f_615_, 0, v_toPure_612_);
    lean_closure_set(v___f_615_, 1, v_inst_606_);
    lean_closure_set(v___f_615_, 2, v_toBind_611_);
    v___x_616_ = l_Std_IterM_toArray___redArg___closed__0;
    v___x_617_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_615_, v_it_608_, v___x_616_,
    );
    v___x_618_ = lean_apply_4(v_map_613_, lean_box(0), lean_box(0), v___f_614_, v___x_617_);
    return v___x_618_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Partial(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Total(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_WFExtrinsicFix(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Ext(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(
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
pub unsafe fn initialize_Init_Data_Iterators_Consumers_Monadic_Collect(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Consumers_Monadic_Partial(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Monadic_Total(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_WFExtrinsicFix(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Ext(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
}
