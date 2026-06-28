// Lean compiler output
// Module: Lake.Util.StoreInsts
// Imports: Init.Data.Order Lean.Data.NameMap.Basic Lake.Util.RBArray Lake.Util.Family Lake.Util.Store
use crate::r#gen::Init::Data::Order::{
    initialize_Init_Data_Order, runtime_initialize_Init_Data_Order,
};
use crate::r#gen::Init::System::ST::l_ST_Prim_Ref_modifyGetUnsafe___boxed;
use crate::r#gen::Lake::Util::Family::{
    initialize_Lake_Util_Family, runtime_initialize_Lake_Util_Family,
};
use crate::r#gen::Lake::Util::RBArray::{
    initialize_Lake_Util_RBArray, l_Lake_RBArray_insert___redArg,
    runtime_initialize_Lake_Util_RBArray,
};
use crate::r#gen::Lake::Util::Store::{
    initialize_Lake_Util_Store, runtime_initialize_Lake_Util_Store,
};
use crate::r#gen::Lean::Data::NameMap::Basic::{
    initialize_Lean_Data_NameMap_Basic,
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg,
    runtime_initialize_Lean_Data_NameMap_Basic,
};
use crate::r#gen::Std::Data::DTreeMap::Internal::Operations::l_Std_DTreeMap_Internal_Impl_insert___redArg;
use crate::r#gen::Std::Data::DTreeMap::Internal::Queries::{
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg,
    l_Std_DTreeMap_Internal_Impl_get_x3f___redArg,
};
pub unsafe fn l_Lake_instMonadDStoreStateTDTreeMapOfMonadOfLawfulEqCmp___redArg___lam__0(
    mut v_inst_334_: *mut crate::leanh::LeanObject,
    mut v_cmp_335_: *mut crate::leanh::LeanObject,
    mut v_k_336_: *mut crate::leanh::LeanObject,
    mut v___y_337_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_341_: u8 = 0;
    let mut v_toPure_342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_348_: u8 = 0;
    let mut v_unused_349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_338_ = crate::leanh::lean_ctor_get(v_inst_334_, 0);
                v_isSharedCheck_348_ = (!crate::leanh::lean_is_exclusive(v_inst_334_)) as u8;
                if v_isSharedCheck_348_ == 0 {
                    v_unused_349_ = crate::leanh::lean_ctor_get(v_inst_334_, 1);
                    crate::leanh::lean_dec(v_unused_349_);
                    v___x_340_ = v_inst_334_;
                    v_isShared_341_ = v_isSharedCheck_348_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_338_);
                    crate::leanh::lean_dec(v_inst_334_);
                    v___x_340_ = crate::leanh::lean_box(0);
                    v_isShared_341_ = v_isSharedCheck_348_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_342_ = crate::leanh::lean_ctor_get(v_toApplicative_338_, 1);
                crate::leanh::lean_inc(v_toPure_342_);
                crate::leanh::lean_dec_ref(v_toApplicative_338_);
                crate::leanh::lean_inc(v___y_337_);
                v___x_343_ =
                    l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_cmp_335_, v___y_337_, v_k_336_);
                if v_isShared_341_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_340_, 1, v___y_337_);
                    crate::leanh::lean_ctor_set(v___x_340_, 0, v___x_343_);
                    v___x_345_ = v___x_340_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_347_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_347_, 0, v___x_343_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_347_, 1, v___y_337_);
                    v___x_345_ = v_reuseFailAlloc_347_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_346_ = crate::leanh::lean_apply_2(
                    v_toPure_342_,
                    crate::leanh::lean_box(0),
                    v___x_345_,
                );
                return v___x_346_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instMonadDStoreStateTDTreeMapOfMonadOfLawfulEqCmp___redArg___lam__1(
    mut v_inst_350_: *mut crate::leanh::LeanObject,
    mut v_cmp_351_: *mut crate::leanh::LeanObject,
    mut v_k_352_: *mut crate::leanh::LeanObject,
    mut v_a_353_: *mut crate::leanh::LeanObject,
    mut v___y_354_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_358_: u8 = 0;
    let mut v_toPure_359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_366_: u8 = 0;
    let mut v_unused_367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_355_ = crate::leanh::lean_ctor_get(v_inst_350_, 0);
                v_isSharedCheck_366_ = (!crate::leanh::lean_is_exclusive(v_inst_350_)) as u8;
                if v_isSharedCheck_366_ == 0 {
                    v_unused_367_ = crate::leanh::lean_ctor_get(v_inst_350_, 1);
                    crate::leanh::lean_dec(v_unused_367_);
                    v___x_357_ = v_inst_350_;
                    v_isShared_358_ = v_isSharedCheck_366_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_355_);
                    crate::leanh::lean_dec(v_inst_350_);
                    v___x_357_ = crate::leanh::lean_box(0);
                    v_isShared_358_ = v_isSharedCheck_366_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_359_ = crate::leanh::lean_ctor_get(v_toApplicative_355_, 1);
                crate::leanh::lean_inc(v_toPure_359_);
                crate::leanh::lean_dec_ref(v_toApplicative_355_);
                v___x_360_ = crate::leanh::lean_box(0);
                v___x_361_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
                    v_cmp_351_, v_k_352_, v_a_353_, v___y_354_,
                );
                if v_isShared_358_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_357_, 1, v___x_361_);
                    crate::leanh::lean_ctor_set(v___x_357_, 0, v___x_360_);
                    v___x_363_ = v___x_357_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_365_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_365_, 0, v___x_360_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_365_, 1, v___x_361_);
                    v___x_363_ = v_reuseFailAlloc_365_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_364_ = crate::leanh::lean_apply_2(
                    v_toPure_359_,
                    crate::leanh::lean_box(0),
                    v___x_363_,
                );
                return v___x_364_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instMonadDStoreStateTDTreeMapOfMonadOfLawfulEqCmp___redArg(
    mut v_cmp_368_: *mut crate::leanh::LeanObject,
    mut v_inst_369_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_cmp_368_);
    crate::leanh::lean_inc_ref(v_inst_369_);
    v___f_370_ = crate::leanh::lean_alloc_closure(
        l_Lake_instMonadDStoreStateTDTreeMapOfMonadOfLawfulEqCmp___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_370_, 0, v_inst_369_);
    crate::leanh::lean_closure_set(v___f_370_, 1, v_cmp_368_);
    v___f_371_ = crate::leanh::lean_alloc_closure(
        l_Lake_instMonadDStoreStateTDTreeMapOfMonadOfLawfulEqCmp___redArg___lam__1
            as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___f_371_, 0, v_inst_369_);
    crate::leanh::lean_closure_set(v___f_371_, 1, v_cmp_368_);
    v___x_372_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_372_, 0, v___f_370_);
    crate::leanh::lean_ctor_set(v___x_372_, 1, v___f_371_);
    return v___x_372_;
}
pub unsafe fn l_Lake_instMonadDStoreStateTDTreeMapOfMonadOfLawfulEqCmp(
    mut v_00_u03ba_373_: *mut crate::leanh::LeanObject,
    mut v_m_374_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_375_: *mut crate::leanh::LeanObject,
    mut v_cmp_376_: *mut crate::leanh::LeanObject,
    mut v_inst_377_: *mut crate::leanh::LeanObject,
    mut v_inst_378_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_379_ =
        l_Lake_instMonadDStoreStateTDTreeMapOfMonadOfLawfulEqCmp___redArg(v_cmp_376_, v_inst_377_);
    return v___x_379_;
}
pub unsafe fn l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp___redArg___lam__0(
    mut v_cmp_380_: *mut crate::leanh::LeanObject,
    mut v_k_381_: *mut crate::leanh::LeanObject,
    mut v_m_382_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_m_382_);
    v___x_383_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_cmp_380_, v_m_382_, v_k_381_);
    v___x_384_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_384_, 0, v___x_383_);
    crate::leanh::lean_ctor_set(v___x_384_, 1, v_m_382_);
    return v___x_384_;
}
pub unsafe fn l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp___redArg___lam__1(
    mut v_cmp_385_: *mut crate::leanh::LeanObject,
    mut v_inst_386_: *mut crate::leanh::LeanObject,
    mut v_k_387_: *mut crate::leanh::LeanObject,
    mut v___y_388_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_389_ = crate::leanh::lean_alloc_closure(l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp___redArg___lam__0 as *mut core::ffi::c_void, 3, 2);
    crate::leanh::lean_closure_set(v___f_389_, 0, v_cmp_385_);
    crate::leanh::lean_closure_set(v___f_389_, 1, v_k_387_);
    crate::leanh::lean_inc(v___y_388_);
    v___x_390_ = crate::leanh::lean_alloc_closure(
        l_ST_Prim_Ref_modifyGetUnsafe___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___x_390_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_390_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_390_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_390_, 3, v___y_388_);
    crate::leanh::lean_closure_set(v___x_390_, 4, v___f_389_);
    v___x_391_ = crate::leanh::lean_apply_2(v_inst_386_, crate::leanh::lean_box(0), v___x_390_);
    return v___x_391_;
}
pub unsafe fn l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp___redArg___lam__1___boxed(
    mut v_cmp_392_: *mut crate::leanh::LeanObject,
    mut v_inst_393_: *mut crate::leanh::LeanObject,
    mut v_k_394_: *mut crate::leanh::LeanObject,
    mut v___y_395_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_396_ = l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp___redArg___lam__1(v_cmp_392_, v_inst_393_, v_k_394_, v___y_395_);
    crate::leanh::lean_dec(v___y_395_);
    return v_res_396_;
}
pub unsafe fn l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp___redArg___lam__2(
    mut v_cmp_397_: *mut crate::leanh::LeanObject,
    mut v_k_398_: *mut crate::leanh::LeanObject,
    mut v_a_399_: *mut crate::leanh::LeanObject,
    mut v_s_400_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_401_ = crate::leanh::lean_box(0);
    v___x_402_ =
        l_Std_DTreeMap_Internal_Impl_insert___redArg(v_cmp_397_, v_k_398_, v_a_399_, v_s_400_);
    v___x_403_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_403_, 0, v___x_401_);
    crate::leanh::lean_ctor_set(v___x_403_, 1, v___x_402_);
    return v___x_403_;
}
pub unsafe fn l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp___redArg___lam__3(
    mut v_cmp_404_: *mut crate::leanh::LeanObject,
    mut v_inst_405_: *mut crate::leanh::LeanObject,
    mut v_k_406_: *mut crate::leanh::LeanObject,
    mut v_a_407_: *mut crate::leanh::LeanObject,
    mut v___y_408_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_409_ = crate::leanh::lean_alloc_closure(l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp___redArg___lam__2 as *mut core::ffi::c_void, 4, 3);
    crate::leanh::lean_closure_set(v___f_409_, 0, v_cmp_404_);
    crate::leanh::lean_closure_set(v___f_409_, 1, v_k_406_);
    crate::leanh::lean_closure_set(v___f_409_, 2, v_a_407_);
    crate::leanh::lean_inc(v___y_408_);
    v___x_410_ = crate::leanh::lean_alloc_closure(
        l_ST_Prim_Ref_modifyGetUnsafe___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___x_410_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_410_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_410_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_410_, 3, v___y_408_);
    crate::leanh::lean_closure_set(v___x_410_, 4, v___f_409_);
    v___x_411_ = crate::leanh::lean_apply_2(v_inst_405_, crate::leanh::lean_box(0), v___x_410_);
    return v___x_411_;
}
pub unsafe fn l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp___redArg___lam__3___boxed(
    mut v_cmp_412_: *mut crate::leanh::LeanObject,
    mut v_inst_413_: *mut crate::leanh::LeanObject,
    mut v_k_414_: *mut crate::leanh::LeanObject,
    mut v_a_415_: *mut crate::leanh::LeanObject,
    mut v___y_416_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_417_ = l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp___redArg___lam__3(v_cmp_412_, v_inst_413_, v_k_414_, v_a_415_, v___y_416_);
    crate::leanh::lean_dec(v___y_416_);
    return v_res_417_;
}
pub unsafe fn l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp___redArg(
    mut v_cmp_418_: *mut crate::leanh::LeanObject,
    mut v_inst_419_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_inst_419_);
    crate::leanh::lean_inc_ref(v_cmp_418_);
    v___f_420_ = crate::leanh::lean_alloc_closure(l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp___redArg___lam__1___boxed as *mut core::ffi::c_void, 4, 2);
    crate::leanh::lean_closure_set(v___f_420_, 0, v_cmp_418_);
    crate::leanh::lean_closure_set(v___f_420_, 1, v_inst_419_);
    v___f_421_ = crate::leanh::lean_alloc_closure(l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp___redArg___lam__3___boxed as *mut core::ffi::c_void, 5, 2);
    crate::leanh::lean_closure_set(v___f_421_, 0, v_cmp_418_);
    crate::leanh::lean_closure_set(v___f_421_, 1, v_inst_419_);
    v___x_422_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_422_, 0, v___f_420_);
    crate::leanh::lean_ctor_set(v___x_422_, 1, v___f_421_);
    return v___x_422_;
}
pub unsafe fn l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp(
    mut v_00_u03ba_423_: *mut crate::leanh::LeanObject,
    mut v_00_u03c9_424_: *mut crate::leanh::LeanObject,
    mut v_m_425_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_426_: *mut crate::leanh::LeanObject,
    mut v_cmp_427_: *mut crate::leanh::LeanObject,
    mut v_inst_428_: *mut crate::leanh::LeanObject,
    mut v_inst_429_: *mut crate::leanh::LeanObject,
    mut v_inst_430_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_431_ =
        l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp___redArg(
            v_cmp_427_,
            v_inst_428_,
        );
    return v___x_431_;
}
pub unsafe fn l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp___boxed(
    mut v_00_u03ba_432_: *mut crate::leanh::LeanObject,
    mut v_00_u03c9_433_: *mut crate::leanh::LeanObject,
    mut v_m_434_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_435_: *mut crate::leanh::LeanObject,
    mut v_cmp_436_: *mut crate::leanh::LeanObject,
    mut v_inst_437_: *mut crate::leanh::LeanObject,
    mut v_inst_438_: *mut crate::leanh::LeanObject,
    mut v_inst_439_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_440_ = l_Lake_instMonadDStoreStateRefT_x27DTreeMapOfMonadLiftTSTOfMonadOfLawfulEqCmp(
        v_00_u03ba_432_,
        v_00_u03c9_433_,
        v_m_434_,
        v_00_u03b2_435_,
        v_cmp_436_,
        v_inst_437_,
        v_inst_438_,
        v_inst_439_,
    );
    crate::leanh::lean_dec_ref(v_inst_438_);
    return v_res_440_;
}
pub unsafe fn l_Lake_instMonadStoreStateTRBArrayOfMonad___redArg___lam__0(
    mut v_inst_441_: *mut crate::leanh::LeanObject,
    mut v_cmp_442_: *mut crate::leanh::LeanObject,
    mut v_k_443_: *mut crate::leanh::LeanObject,
    mut v___y_444_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_448_: u8 = 0;
    let mut v_toPure_449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toTreeMap_450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_456_: u8 = 0;
    let mut v_unused_457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_445_ = crate::leanh::lean_ctor_get(v_inst_441_, 0);
                v_isSharedCheck_456_ = (!crate::leanh::lean_is_exclusive(v_inst_441_)) as u8;
                if v_isSharedCheck_456_ == 0 {
                    v_unused_457_ = crate::leanh::lean_ctor_get(v_inst_441_, 1);
                    crate::leanh::lean_dec(v_unused_457_);
                    v___x_447_ = v_inst_441_;
                    v_isShared_448_ = v_isSharedCheck_456_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_445_);
                    crate::leanh::lean_dec(v_inst_441_);
                    v___x_447_ = crate::leanh::lean_box(0);
                    v_isShared_448_ = v_isSharedCheck_456_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_449_ = crate::leanh::lean_ctor_get(v_toApplicative_445_, 1);
                crate::leanh::lean_inc(v_toPure_449_);
                crate::leanh::lean_dec_ref(v_toApplicative_445_);
                v_toTreeMap_450_ = crate::leanh::lean_ctor_get(v___y_444_, 0);
                crate::leanh::lean_inc(v_toTreeMap_450_);
                v___x_451_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(
                    v_cmp_442_,
                    v_toTreeMap_450_,
                    v_k_443_,
                );
                if v_isShared_448_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_447_, 1, v___y_444_);
                    crate::leanh::lean_ctor_set(v___x_447_, 0, v___x_451_);
                    v___x_453_ = v___x_447_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_455_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_455_, 0, v___x_451_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_455_, 1, v___y_444_);
                    v___x_453_ = v_reuseFailAlloc_455_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_454_ = crate::leanh::lean_apply_2(
                    v_toPure_449_,
                    crate::leanh::lean_box(0),
                    v___x_453_,
                );
                return v___x_454_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instMonadStoreStateTRBArrayOfMonad___redArg___lam__1(
    mut v_inst_458_: *mut crate::leanh::LeanObject,
    mut v_cmp_459_: *mut crate::leanh::LeanObject,
    mut v_k_460_: *mut crate::leanh::LeanObject,
    mut v_a_461_: *mut crate::leanh::LeanObject,
    mut v___y_462_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_466_: u8 = 0;
    let mut v_toPure_467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_474_: u8 = 0;
    let mut v_unused_475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_463_ = crate::leanh::lean_ctor_get(v_inst_458_, 0);
                v_isSharedCheck_474_ = (!crate::leanh::lean_is_exclusive(v_inst_458_)) as u8;
                if v_isSharedCheck_474_ == 0 {
                    v_unused_475_ = crate::leanh::lean_ctor_get(v_inst_458_, 1);
                    crate::leanh::lean_dec(v_unused_475_);
                    v___x_465_ = v_inst_458_;
                    v_isShared_466_ = v_isSharedCheck_474_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_463_);
                    crate::leanh::lean_dec(v_inst_458_);
                    v___x_465_ = crate::leanh::lean_box(0);
                    v_isShared_466_ = v_isSharedCheck_474_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_467_ = crate::leanh::lean_ctor_get(v_toApplicative_463_, 1);
                crate::leanh::lean_inc(v_toPure_467_);
                crate::leanh::lean_dec_ref(v_toApplicative_463_);
                v___x_468_ = crate::leanh::lean_box(0);
                v___x_469_ =
                    l_Lake_RBArray_insert___redArg(v_cmp_459_, v___y_462_, v_k_460_, v_a_461_);
                if v_isShared_466_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_465_, 1, v___x_469_);
                    crate::leanh::lean_ctor_set(v___x_465_, 0, v___x_468_);
                    v___x_471_ = v___x_465_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_473_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_473_, 0, v___x_468_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_473_, 1, v___x_469_);
                    v___x_471_ = v_reuseFailAlloc_473_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_472_ = crate::leanh::lean_apply_2(
                    v_toPure_467_,
                    crate::leanh::lean_box(0),
                    v___x_471_,
                );
                return v___x_472_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instMonadStoreStateTRBArrayOfMonad___redArg(
    mut v_cmp_476_: *mut crate::leanh::LeanObject,
    mut v_inst_477_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_cmp_476_);
    crate::leanh::lean_inc_ref(v_inst_477_);
    v___f_478_ = crate::leanh::lean_alloc_closure(
        l_Lake_instMonadStoreStateTRBArrayOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_478_, 0, v_inst_477_);
    crate::leanh::lean_closure_set(v___f_478_, 1, v_cmp_476_);
    v___f_479_ = crate::leanh::lean_alloc_closure(
        l_Lake_instMonadStoreStateTRBArrayOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___f_479_, 0, v_inst_477_);
    crate::leanh::lean_closure_set(v___f_479_, 1, v_cmp_476_);
    v___x_480_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_480_, 0, v___f_478_);
    crate::leanh::lean_ctor_set(v___x_480_, 1, v___f_479_);
    return v___x_480_;
}
pub unsafe fn l_Lake_instMonadStoreStateTRBArrayOfMonad(
    mut v_m_481_: *mut crate::leanh::LeanObject,
    mut v_00_u03ba_482_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_483_: *mut crate::leanh::LeanObject,
    mut v_cmp_484_: *mut crate::leanh::LeanObject,
    mut v_inst_485_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_486_ = l_Lake_instMonadStoreStateTRBArrayOfMonad___redArg(v_cmp_484_, v_inst_485_);
    return v___x_486_;
}
pub unsafe fn l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad___redArg___lam__0(
    mut v_cmp_487_: *mut crate::leanh::LeanObject,
    mut v_k_488_: *mut crate::leanh::LeanObject,
    mut v_m_489_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toTreeMap_490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toTreeMap_490_ = crate::leanh::lean_ctor_get(v_m_489_, 0);
    crate::leanh::lean_inc(v_toTreeMap_490_);
    v___x_491_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_cmp_487_, v_toTreeMap_490_, v_k_488_);
    v___x_492_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_492_, 0, v___x_491_);
    crate::leanh::lean_ctor_set(v___x_492_, 1, v_m_489_);
    return v___x_492_;
}
pub unsafe fn l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad___redArg___lam__1(
    mut v_cmp_493_: *mut crate::leanh::LeanObject,
    mut v_inst_494_: *mut crate::leanh::LeanObject,
    mut v_k_495_: *mut crate::leanh::LeanObject,
    mut v___y_496_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_497_ = crate::leanh::lean_alloc_closure(
        l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_497_, 0, v_cmp_493_);
    crate::leanh::lean_closure_set(v___f_497_, 1, v_k_495_);
    crate::leanh::lean_inc(v___y_496_);
    v___x_498_ = crate::leanh::lean_alloc_closure(
        l_ST_Prim_Ref_modifyGetUnsafe___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___x_498_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_498_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_498_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_498_, 3, v___y_496_);
    crate::leanh::lean_closure_set(v___x_498_, 4, v___f_497_);
    v___x_499_ = crate::leanh::lean_apply_2(v_inst_494_, crate::leanh::lean_box(0), v___x_498_);
    return v___x_499_;
}
pub unsafe fn l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad___redArg___lam__1___boxed(
    mut v_cmp_500_: *mut crate::leanh::LeanObject,
    mut v_inst_501_: *mut crate::leanh::LeanObject,
    mut v_k_502_: *mut crate::leanh::LeanObject,
    mut v___y_503_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_504_ = l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad___redArg___lam__1(
        v_cmp_500_,
        v_inst_501_,
        v_k_502_,
        v___y_503_,
    );
    crate::leanh::lean_dec(v___y_503_);
    return v_res_504_;
}
pub unsafe fn l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad___redArg___lam__2(
    mut v_cmp_505_: *mut crate::leanh::LeanObject,
    mut v_k_506_: *mut crate::leanh::LeanObject,
    mut v_a_507_: *mut crate::leanh::LeanObject,
    mut v_s_508_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_509_ = crate::leanh::lean_box(0);
    v___x_510_ = l_Lake_RBArray_insert___redArg(v_cmp_505_, v_s_508_, v_k_506_, v_a_507_);
    v___x_511_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_511_, 0, v___x_509_);
    crate::leanh::lean_ctor_set(v___x_511_, 1, v___x_510_);
    return v___x_511_;
}
pub unsafe fn l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad___redArg___lam__3(
    mut v_cmp_512_: *mut crate::leanh::LeanObject,
    mut v_inst_513_: *mut crate::leanh::LeanObject,
    mut v_k_514_: *mut crate::leanh::LeanObject,
    mut v_a_515_: *mut crate::leanh::LeanObject,
    mut v___y_516_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_517_ = crate::leanh::lean_alloc_closure(
        l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad___redArg___lam__2
            as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_517_, 0, v_cmp_512_);
    crate::leanh::lean_closure_set(v___f_517_, 1, v_k_514_);
    crate::leanh::lean_closure_set(v___f_517_, 2, v_a_515_);
    crate::leanh::lean_inc(v___y_516_);
    v___x_518_ = crate::leanh::lean_alloc_closure(
        l_ST_Prim_Ref_modifyGetUnsafe___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___x_518_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_518_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_518_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_518_, 3, v___y_516_);
    crate::leanh::lean_closure_set(v___x_518_, 4, v___f_517_);
    v___x_519_ = crate::leanh::lean_apply_2(v_inst_513_, crate::leanh::lean_box(0), v___x_518_);
    return v___x_519_;
}
pub unsafe fn l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad___redArg___lam__3___boxed(
    mut v_cmp_520_: *mut crate::leanh::LeanObject,
    mut v_inst_521_: *mut crate::leanh::LeanObject,
    mut v_k_522_: *mut crate::leanh::LeanObject,
    mut v_a_523_: *mut crate::leanh::LeanObject,
    mut v___y_524_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_525_ = l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad___redArg___lam__3(
        v_cmp_520_,
        v_inst_521_,
        v_k_522_,
        v_a_523_,
        v___y_524_,
    );
    crate::leanh::lean_dec(v___y_524_);
    return v_res_525_;
}
pub unsafe fn l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad___redArg(
    mut v_cmp_526_: *mut crate::leanh::LeanObject,
    mut v_inst_527_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_inst_527_);
    crate::leanh::lean_inc_ref(v_cmp_526_);
    v___f_528_ = crate::leanh::lean_alloc_closure(
        l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad___redArg___lam__1___boxed
            as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_528_, 0, v_cmp_526_);
    crate::leanh::lean_closure_set(v___f_528_, 1, v_inst_527_);
    v___f_529_ = crate::leanh::lean_alloc_closure(
        l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad___redArg___lam__3___boxed
            as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___f_529_, 0, v_cmp_526_);
    crate::leanh::lean_closure_set(v___f_529_, 1, v_inst_527_);
    v___x_530_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_530_, 0, v___f_528_);
    crate::leanh::lean_ctor_set(v___x_530_, 1, v___f_529_);
    return v___x_530_;
}
pub unsafe fn l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad(
    mut v_00_u03c9_531_: *mut crate::leanh::LeanObject,
    mut v_m_532_: *mut crate::leanh::LeanObject,
    mut v_00_u03ba_533_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_534_: *mut crate::leanh::LeanObject,
    mut v_cmp_535_: *mut crate::leanh::LeanObject,
    mut v_inst_536_: *mut crate::leanh::LeanObject,
    mut v_inst_537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_538_ = l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad___redArg(
        v_cmp_535_,
        v_inst_536_,
    );
    return v___x_538_;
}
pub unsafe fn l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad___boxed(
    mut v_00_u03c9_539_: *mut crate::leanh::LeanObject,
    mut v_m_540_: *mut crate::leanh::LeanObject,
    mut v_00_u03ba_541_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_542_: *mut crate::leanh::LeanObject,
    mut v_cmp_543_: *mut crate::leanh::LeanObject,
    mut v_inst_544_: *mut crate::leanh::LeanObject,
    mut v_inst_545_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_546_ = l_Lake_instMonadStoreStateRefT_x27RBArrayOfMonadLiftTSTOfMonad(
        v_00_u03c9_539_,
        v_m_540_,
        v_00_u03ba_541_,
        v_00_u03b1_542_,
        v_cmp_543_,
        v_inst_544_,
        v_inst_545_,
    );
    crate::leanh::lean_dec_ref(v_inst_545_);
    return v_res_546_;
}
pub unsafe fn l_Lake_instMonadStoreNameStateTNameMapOfMonad___redArg___lam__0(
    mut v_inst_547_: *mut crate::leanh::LeanObject,
    mut v_k_548_: *mut crate::leanh::LeanObject,
    mut v___y_549_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_553_: u8 = 0;
    let mut v_toPure_554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_560_: u8 = 0;
    let mut v_unused_561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_550_ = crate::leanh::lean_ctor_get(v_inst_547_, 0);
                v_isSharedCheck_560_ = (!crate::leanh::lean_is_exclusive(v_inst_547_)) as u8;
                if v_isSharedCheck_560_ == 0 {
                    v_unused_561_ = crate::leanh::lean_ctor_get(v_inst_547_, 1);
                    crate::leanh::lean_dec(v_unused_561_);
                    v___x_552_ = v_inst_547_;
                    v_isShared_553_ = v_isSharedCheck_560_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_550_);
                    crate::leanh::lean_dec(v_inst_547_);
                    v___x_552_ = crate::leanh::lean_box(0);
                    v_isShared_553_ = v_isSharedCheck_560_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_554_ = crate::leanh::lean_ctor_get(v_toApplicative_550_, 1);
                crate::leanh::lean_inc(v_toPure_554_);
                crate::leanh::lean_dec_ref(v_toApplicative_550_);
                v___x_555_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___y_549_, v_k_548_);
                if v_isShared_553_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_552_, 1, v___y_549_);
                    crate::leanh::lean_ctor_set(v___x_552_, 0, v___x_555_);
                    v___x_557_ = v___x_552_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_559_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_559_, 0, v___x_555_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_559_, 1, v___y_549_);
                    v___x_557_ = v_reuseFailAlloc_559_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_558_ = crate::leanh::lean_apply_2(
                    v_toPure_554_,
                    crate::leanh::lean_box(0),
                    v___x_557_,
                );
                return v___x_558_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instMonadStoreNameStateTNameMapOfMonad___redArg___lam__0___boxed(
    mut v_inst_562_: *mut crate::leanh::LeanObject,
    mut v_k_563_: *mut crate::leanh::LeanObject,
    mut v___y_564_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_565_ = l_Lake_instMonadStoreNameStateTNameMapOfMonad___redArg___lam__0(
        v_inst_562_,
        v_k_563_,
        v___y_564_,
    );
    crate::leanh::lean_dec(v_k_563_);
    return v_res_565_;
}
pub unsafe fn l_Lake_instMonadStoreNameStateTNameMapOfMonad___redArg___lam__1(
    mut v_inst_566_: *mut crate::leanh::LeanObject,
    mut v_k_567_: *mut crate::leanh::LeanObject,
    mut v_a_568_: *mut crate::leanh::LeanObject,
    mut v___y_569_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_573_: u8 = 0;
    let mut v_toPure_574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_581_: u8 = 0;
    let mut v_unused_582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_570_ = crate::leanh::lean_ctor_get(v_inst_566_, 0);
                v_isSharedCheck_581_ = (!crate::leanh::lean_is_exclusive(v_inst_566_)) as u8;
                if v_isSharedCheck_581_ == 0 {
                    v_unused_582_ = crate::leanh::lean_ctor_get(v_inst_566_, 1);
                    crate::leanh::lean_dec(v_unused_582_);
                    v___x_572_ = v_inst_566_;
                    v_isShared_573_ = v_isSharedCheck_581_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_570_);
                    crate::leanh::lean_dec(v_inst_566_);
                    v___x_572_ = crate::leanh::lean_box(0);
                    v_isShared_573_ = v_isSharedCheck_581_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_574_ = crate::leanh::lean_ctor_get(v_toApplicative_570_, 1);
                crate::leanh::lean_inc(v_toPure_574_);
                crate::leanh::lean_dec_ref(v_toApplicative_570_);
                v___x_575_ = crate::leanh::lean_box(0);
                v___x_576_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_567_, v_a_568_, v___y_569_);
                if v_isShared_573_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_572_, 1, v___x_576_);
                    crate::leanh::lean_ctor_set(v___x_572_, 0, v___x_575_);
                    v___x_578_ = v___x_572_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_580_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_580_, 0, v___x_575_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_580_, 1, v___x_576_);
                    v___x_578_ = v_reuseFailAlloc_580_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_579_ = crate::leanh::lean_apply_2(
                    v_toPure_574_,
                    crate::leanh::lean_box(0),
                    v___x_578_,
                );
                return v___x_579_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instMonadStoreNameStateTNameMapOfMonad___redArg(
    mut v_inst_583_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_inst_583_);
    v___f_584_ = crate::leanh::lean_alloc_closure(
        l_Lake_instMonadStoreNameStateTNameMapOfMonad___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_584_, 0, v_inst_583_);
    v___f_585_ = crate::leanh::lean_alloc_closure(
        l_Lake_instMonadStoreNameStateTNameMapOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_585_, 0, v_inst_583_);
    v___x_586_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_586_, 0, v___f_584_);
    crate::leanh::lean_ctor_set(v___x_586_, 1, v___f_585_);
    return v___x_586_;
}
pub unsafe fn l_Lake_instMonadStoreNameStateTNameMapOfMonad(
    mut v_m_587_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_588_: *mut crate::leanh::LeanObject,
    mut v_inst_589_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_590_ = l_Lake_instMonadStoreNameStateTNameMapOfMonad___redArg(v_inst_589_);
    return v___x_590_;
}
pub unsafe fn l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg___lam__0(
    mut v_k_591_: *mut crate::leanh::LeanObject,
    mut v_m_592_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_593_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_m_592_, v_k_591_,
        );
    v___x_594_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_594_, 0, v___x_593_);
    crate::leanh::lean_ctor_set(v___x_594_, 1, v_m_592_);
    return v___x_594_;
}
pub unsafe fn l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg___lam__0___boxed(
    mut v_k_595_: *mut crate::leanh::LeanObject,
    mut v_m_596_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_597_ =
        l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg___lam__0(
            v_k_595_, v_m_596_,
        );
    crate::leanh::lean_dec(v_k_595_);
    return v_res_597_;
}
pub unsafe fn l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg___lam__1(
    mut v_inst_598_: *mut crate::leanh::LeanObject,
    mut v_k_599_: *mut crate::leanh::LeanObject,
    mut v___y_600_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_601_ = crate::leanh::lean_alloc_closure(
        l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_601_, 0, v_k_599_);
    crate::leanh::lean_inc(v___y_600_);
    v___x_602_ = crate::leanh::lean_alloc_closure(
        l_ST_Prim_Ref_modifyGetUnsafe___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___x_602_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_602_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_602_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_602_, 3, v___y_600_);
    crate::leanh::lean_closure_set(v___x_602_, 4, v___f_601_);
    v___x_603_ = crate::leanh::lean_apply_2(v_inst_598_, crate::leanh::lean_box(0), v___x_602_);
    return v___x_603_;
}
pub unsafe fn l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg___lam__1___boxed(
    mut v_inst_604_: *mut crate::leanh::LeanObject,
    mut v_k_605_: *mut crate::leanh::LeanObject,
    mut v___y_606_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_607_ =
        l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg___lam__1(
            v_inst_604_,
            v_k_605_,
            v___y_606_,
        );
    crate::leanh::lean_dec(v___y_606_);
    return v_res_607_;
}
pub unsafe fn l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg___lam__2(
    mut v_k_608_: *mut crate::leanh::LeanObject,
    mut v_a_609_: *mut crate::leanh::LeanObject,
    mut v_s_610_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_611_ = crate::leanh::lean_box(0);
    v___x_612_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(
        v_k_608_, v_a_609_, v_s_610_,
    );
    v___x_613_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_613_, 0, v___x_611_);
    crate::leanh::lean_ctor_set(v___x_613_, 1, v___x_612_);
    return v___x_613_;
}
pub unsafe fn l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg___lam__3(
    mut v_inst_614_: *mut crate::leanh::LeanObject,
    mut v_k_615_: *mut crate::leanh::LeanObject,
    mut v_a_616_: *mut crate::leanh::LeanObject,
    mut v___y_617_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_618_ = crate::leanh::lean_alloc_closure(
        l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg___lam__2
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_618_, 0, v_k_615_);
    crate::leanh::lean_closure_set(v___f_618_, 1, v_a_616_);
    crate::leanh::lean_inc(v___y_617_);
    v___x_619_ = crate::leanh::lean_alloc_closure(
        l_ST_Prim_Ref_modifyGetUnsafe___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___x_619_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_619_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_619_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_619_, 3, v___y_617_);
    crate::leanh::lean_closure_set(v___x_619_, 4, v___f_618_);
    v___x_620_ = crate::leanh::lean_apply_2(v_inst_614_, crate::leanh::lean_box(0), v___x_619_);
    return v___x_620_;
}
pub unsafe fn l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg___lam__3___boxed(
    mut v_inst_621_: *mut crate::leanh::LeanObject,
    mut v_k_622_: *mut crate::leanh::LeanObject,
    mut v_a_623_: *mut crate::leanh::LeanObject,
    mut v___y_624_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_625_ =
        l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg___lam__3(
            v_inst_621_,
            v_k_622_,
            v_a_623_,
            v___y_624_,
        );
    crate::leanh::lean_dec(v___y_624_);
    return v_res_625_;
}
pub unsafe fn l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg(
    mut v_inst_626_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_inst_626_);
    v___f_627_ = crate::leanh::lean_alloc_closure(
        l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg___lam__1___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_627_, 0, v_inst_626_);
    v___f_628_ = crate::leanh::lean_alloc_closure(
        l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg___lam__3___boxed
            as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_628_, 0, v_inst_626_);
    v___x_629_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_629_, 0, v___f_627_);
    crate::leanh::lean_ctor_set(v___x_629_, 1, v___f_628_);
    return v___x_629_;
}
pub unsafe fn l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad(
    mut v_00_u03c9_630_: *mut crate::leanh::LeanObject,
    mut v_m_631_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_632_: *mut crate::leanh::LeanObject,
    mut v_inst_633_: *mut crate::leanh::LeanObject,
    mut v_inst_634_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_635_ =
        l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___redArg(v_inst_633_);
    return v___x_635_;
}
pub unsafe fn l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad___boxed(
    mut v_00_u03c9_636_: *mut crate::leanh::LeanObject,
    mut v_m_637_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_638_: *mut crate::leanh::LeanObject,
    mut v_inst_639_: *mut crate::leanh::LeanObject,
    mut v_inst_640_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_641_ = l_Lake_instMonadStoreNameStateRefT_x27NameMapOfMonadLiftTSTOfMonad(
        v_00_u03c9_636_,
        v_m_637_,
        v_00_u03b1_638_,
        v_inst_639_,
        v_inst_640_,
    );
    crate::leanh::lean_dec_ref(v_inst_640_);
    return v_res_641_;
}
pub unsafe fn l_Lake_instMonadStore1OfOfMonadDStoreOfFamilyOut___redArg___lam__0(
    mut v_store_642_: *mut crate::leanh::LeanObject,
    mut v_k_643_: *mut crate::leanh::LeanObject,
    mut v_a_644_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_645_ = crate::leanh::lean_apply_2(v_store_642_, v_k_643_, v_a_644_);
    return v___x_645_;
}
pub unsafe fn l_Lake_instMonadStore1OfOfMonadDStoreOfFamilyOut___redArg(
    mut v_k_646_: *mut crate::leanh::LeanObject,
    mut v_inst_647_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fetch_x3f_648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_store_649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_652_: u8 = 0;
    let mut v___f_653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_658_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fetch_x3f_648_ = crate::leanh::lean_ctor_get(v_inst_647_, 0);
                v_store_649_ = crate::leanh::lean_ctor_get(v_inst_647_, 1);
                v_isSharedCheck_658_ = (!crate::leanh::lean_is_exclusive(v_inst_647_)) as u8;
                if v_isSharedCheck_658_ == 0 {
                    v___x_651_ = v_inst_647_;
                    v_isShared_652_ = v_isSharedCheck_658_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_store_649_);
                    crate::leanh::lean_inc(v_fetch_x3f_648_);
                    crate::leanh::lean_dec(v_inst_647_);
                    v___x_651_ = crate::leanh::lean_box(0);
                    v_isShared_652_ = v_isSharedCheck_658_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_k_646_);
                v___f_653_ = crate::leanh::lean_alloc_closure(
                    l_Lake_instMonadStore1OfOfMonadDStoreOfFamilyOut___redArg___lam__0
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_653_, 0, v_store_649_);
                crate::leanh::lean_closure_set(v___f_653_, 1, v_k_646_);
                v___x_654_ = crate::leanh::lean_apply_1(v_fetch_x3f_648_, v_k_646_);
                if v_isShared_652_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_651_, 1, v___f_653_);
                    crate::leanh::lean_ctor_set(v___x_651_, 0, v___x_654_);
                    v___x_656_ = v___x_651_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_657_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_657_, 0, v___x_654_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_657_, 1, v___f_653_);
                    v___x_656_ = v_reuseFailAlloc_657_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_656_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instMonadStore1OfOfMonadDStoreOfFamilyOut(
    mut v_00_u03ba_659_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_660_: *mut crate::leanh::LeanObject,
    mut v_m_661_: *mut crate::leanh::LeanObject,
    mut v_k_662_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_663_: *mut crate::leanh::LeanObject,
    mut v_inst_664_: *mut crate::leanh::LeanObject,
    mut v_t_665_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_666_ = l_Lake_instMonadStore1OfOfMonadDStoreOfFamilyOut___redArg(v_k_662_, v_inst_664_);
    return v___x_666_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Util_StoreInsts(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Order(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_NameMap_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_RBArray(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Family(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Store(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Util_StoreInsts(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Util_StoreInsts(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Order(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Data_NameMap_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Util_RBArray(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Util_Family(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Util_Store(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_StoreInsts(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Util_StoreInsts(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_Util_StoreInsts(builtin);
}
