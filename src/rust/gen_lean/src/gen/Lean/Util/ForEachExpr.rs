// Lean compiler output
// Module: Lean.Util.ForEachExpr
// Imports: Lean.Expr Lean.Util.MonadCache
use crate::r#gen::Init::System::ST::{
    l_ST_Prim_Ref_get___boxed, l_ST_Prim_Ref_modifyGetUnsafe___boxed, l_ST_Prim_mkRef___boxed,
};
use crate::r#gen::Lean::Expr::{
    initialize_Lean_Expr, l_Lean_Expr_eqv___boxed, l_Lean_Expr_hash___boxed,
    runtime_initialize_Lean_Expr,
};
use crate::r#gen::Lean::Util::MonadCache::{
    initialize_Lean_Util_MonadCache, runtime_initialize_Lean_Util_MonadCache,
};
use crate::r#gen::Std::Data::DHashMap::Internal::Defs::{
    l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_insert___redArg,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_mk_array;
pub static l_Lean_ForEachExpr_visit___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Expr_eqv___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_ForEachExpr_visit___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ForEachExpr_visit___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_ForEachExpr_visit___redArg___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Expr_hash___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_ForEachExpr_visit___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ForEachExpr_visit___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Expr_forEach_x27___redArg___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Expr_forEach_x27___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Expr_forEach_x27___redArg___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Expr_forEach_x27___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Expr_forEach_x27___redArg___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Expr_forEach_x27___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_ForEachExpr_visit___redArg___lam__9(
    mut v_toApplicative_337_: *mut crate::leanh::LeanObject,
    mut v___x_338_: *mut crate::leanh::LeanObject,
    mut v___x_339_: *mut crate::leanh::LeanObject,
    mut v_e_340_: *mut crate::leanh::LeanObject,
    mut v_a_341_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toPure_342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toPure_342_ = crate::leanh::lean_ctor_get(v_toApplicative_337_, 1);
    crate::leanh::lean_inc(v_toPure_342_);
    crate::leanh::lean_dec_ref(v_toApplicative_337_);
    v___x_343_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(
        v___x_338_, v___x_339_, v_a_341_, v_e_340_,
    );
    v___x_344_ = crate::leanh::lean_apply_2(v_toPure_342_, crate::leanh::lean_box(0), v___x_343_);
    return v___x_344_;
}
pub unsafe fn l_Lean_ForEachExpr_visit___redArg___lam__9___boxed(
    mut v_toApplicative_345_: *mut crate::leanh::LeanObject,
    mut v___x_346_: *mut crate::leanh::LeanObject,
    mut v___x_347_: *mut crate::leanh::LeanObject,
    mut v_e_348_: *mut crate::leanh::LeanObject,
    mut v_a_349_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_350_ = l_Lean_ForEachExpr_visit___redArg___lam__9(
        v_toApplicative_345_,
        v___x_346_,
        v___x_347_,
        v_e_348_,
        v_a_349_,
    );
    crate::leanh::lean_dec_ref(v_a_349_);
    return v_res_350_;
}
pub unsafe fn l_Lean_ForEachExpr_visit___redArg___lam__8(
    mut v_g_351_: *mut crate::leanh::LeanObject,
    mut v_e_352_: *mut crate::leanh::LeanObject,
    mut v_toBind_353_: *mut crate::leanh::LeanObject,
    mut v___f_354_: *mut crate::leanh::LeanObject,
    mut v___f_355_: *mut crate::leanh::LeanObject,
    mut v_toApplicative_356_: *mut crate::leanh::LeanObject,
    mut v_a_357_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_a_357_) == 0 {
        let mut v___x_358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_toApplicative_356_);
        v___x_358_ = crate::leanh::lean_apply_1(v_g_351_, v_e_352_);
        crate::leanh::lean_inc(v_toBind_353_);
        v___x_359_ = crate::leanh::lean_apply_4(
            v_toBind_353_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_358_,
            v___f_354_,
        );
        v___x_360_ = crate::leanh::lean_apply_4(
            v_toBind_353_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_359_,
            v___f_355_,
        );
        return v___x_360_;
    } else {
        let mut v_val_361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___f_355_);
        crate::leanh::lean_dec(v___f_354_);
        crate::leanh::lean_dec(v_toBind_353_);
        crate::leanh::lean_dec_ref(v_e_352_);
        crate::leanh::lean_dec(v_g_351_);
        v_val_361_ = crate::leanh::lean_ctor_get(v_a_357_, 0);
        crate::leanh::lean_inc(v_val_361_);
        crate::leanh::lean_dec_ref_known(v_a_357_, 1);
        v_toPure_362_ = crate::leanh::lean_ctor_get(v_toApplicative_356_, 1);
        crate::leanh::lean_inc(v_toPure_362_);
        crate::leanh::lean_dec_ref(v_toApplicative_356_);
        v___x_363_ =
            crate::leanh::lean_apply_2(v_toPure_362_, crate::leanh::lean_box(0), v_val_361_);
        return v___x_363_;
    }
}
pub unsafe fn l_Lean_ForEachExpr_visit___redArg___lam__5(
    mut v_toApplicative_364_: *mut crate::leanh::LeanObject,
    mut v_a_365_: *mut crate::leanh::LeanObject,
    mut v_a_366_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toPure_367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toPure_367_ = crate::leanh::lean_ctor_get(v_toApplicative_364_, 1);
    crate::leanh::lean_inc(v_toPure_367_);
    crate::leanh::lean_dec_ref(v_toApplicative_364_);
    v___x_368_ = crate::leanh::lean_apply_2(v_toPure_367_, crate::leanh::lean_box(0), v_a_365_);
    return v___x_368_;
}
pub unsafe fn l_Lean_ForEachExpr_visit___redArg___lam__6(
    mut v___x_369_: *mut crate::leanh::LeanObject,
    mut v___x_370_: *mut crate::leanh::LeanObject,
    mut v_e_371_: *mut crate::leanh::LeanObject,
    mut v_a_372_: *mut crate::leanh::LeanObject,
    mut v_s_373_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_374_ = crate::leanh::lean_box(0);
    v___x_375_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
        v___x_369_, v___x_370_, v_s_373_, v_e_371_, v_a_372_,
    );
    v___x_376_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_376_, 0, v___x_374_);
    crate::leanh::lean_ctor_set(v___x_376_, 1, v___x_375_);
    return v___x_376_;
}
pub unsafe fn l_Lean_ForEachExpr_visit___redArg___lam__7(
    mut v_toApplicative_377_: *mut crate::leanh::LeanObject,
    mut v___x_378_: *mut crate::leanh::LeanObject,
    mut v___x_379_: *mut crate::leanh::LeanObject,
    mut v_e_380_: *mut crate::leanh::LeanObject,
    mut v_a_381_: *mut crate::leanh::LeanObject,
    mut v_inst_382_: *mut crate::leanh::LeanObject,
    mut v_toBind_383_: *mut crate::leanh::LeanObject,
    mut v_a_384_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_385_ = crate::leanh::lean_alloc_closure(
        l_Lean_ForEachExpr_visit___redArg___lam__5 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_385_, 0, v_toApplicative_377_);
    crate::leanh::lean_closure_set(v___f_385_, 1, v_a_384_);
    v___f_386_ = crate::leanh::lean_alloc_closure(
        l_Lean_ForEachExpr_visit___redArg___lam__6 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_386_, 0, v___x_378_);
    crate::leanh::lean_closure_set(v___f_386_, 1, v___x_379_);
    crate::leanh::lean_closure_set(v___f_386_, 2, v_e_380_);
    crate::leanh::lean_closure_set(v___f_386_, 3, v_a_384_);
    crate::leanh::lean_inc(v_a_381_);
    v___x_387_ = crate::leanh::lean_alloc_closure(
        l_ST_Prim_Ref_modifyGetUnsafe___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___x_387_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_387_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_387_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_387_, 3, v_a_381_);
    crate::leanh::lean_closure_set(v___x_387_, 4, v___f_386_);
    v___x_388_ = crate::leanh::lean_apply_2(v_inst_382_, crate::leanh::lean_box(0), v___x_387_);
    v___x_389_ = crate::leanh::lean_apply_4(
        v_toBind_383_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_388_,
        v___f_385_,
    );
    return v___x_389_;
}
pub unsafe fn l_Lean_ForEachExpr_visit___redArg___lam__7___boxed(
    mut v_toApplicative_390_: *mut crate::leanh::LeanObject,
    mut v___x_391_: *mut crate::leanh::LeanObject,
    mut v___x_392_: *mut crate::leanh::LeanObject,
    mut v_e_393_: *mut crate::leanh::LeanObject,
    mut v_a_394_: *mut crate::leanh::LeanObject,
    mut v_inst_395_: *mut crate::leanh::LeanObject,
    mut v_toBind_396_: *mut crate::leanh::LeanObject,
    mut v_a_397_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_398_ = l_Lean_ForEachExpr_visit___redArg___lam__7(
        v_toApplicative_390_,
        v___x_391_,
        v___x_392_,
        v_e_393_,
        v_a_394_,
        v_inst_395_,
        v_toBind_396_,
        v_a_397_,
    );
    crate::leanh::lean_dec(v_a_394_);
    return v_res_398_;
}
pub unsafe fn l_Lean_ForEachExpr_visit___redArg___lam__0___boxed(
    mut v_inst_399_: *mut crate::leanh::LeanObject,
    mut v_inst_400_: *mut crate::leanh::LeanObject,
    mut v_g_401_: *mut crate::leanh::LeanObject,
    mut v_b_402_: *mut crate::leanh::LeanObject,
    mut v___y_403_: *mut crate::leanh::LeanObject,
    mut v_a_404_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_405_ = l_Lean_ForEachExpr_visit___redArg___lam__0(
        v_inst_399_,
        v_inst_400_,
        v_g_401_,
        v_b_402_,
        v___y_403_,
        v_a_404_,
    );
    crate::leanh::lean_dec(v___y_403_);
    return v_res_405_;
}
pub unsafe fn l_Lean_ForEachExpr_visit___redArg___lam__1(
    mut v_inst_406_: *mut crate::leanh::LeanObject,
    mut v_inst_407_: *mut crate::leanh::LeanObject,
    mut v_g_408_: *mut crate::leanh::LeanObject,
    mut v_body_409_: *mut crate::leanh::LeanObject,
    mut v_a_410_: *mut crate::leanh::LeanObject,
    mut v_a_411_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_412_ = l_Lean_ForEachExpr_visit___redArg(
        v_inst_406_,
        v_inst_407_,
        v_g_408_,
        v_body_409_,
        v_a_410_,
    );
    return v___x_412_;
}
pub unsafe fn l_Lean_ForEachExpr_visit___redArg___lam__1___boxed(
    mut v_inst_413_: *mut crate::leanh::LeanObject,
    mut v_inst_414_: *mut crate::leanh::LeanObject,
    mut v_g_415_: *mut crate::leanh::LeanObject,
    mut v_body_416_: *mut crate::leanh::LeanObject,
    mut v_a_417_: *mut crate::leanh::LeanObject,
    mut v_a_418_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_419_ = l_Lean_ForEachExpr_visit___redArg___lam__1(
        v_inst_413_,
        v_inst_414_,
        v_g_415_,
        v_body_416_,
        v_a_417_,
        v_a_418_,
    );
    crate::leanh::lean_dec(v_a_417_);
    return v_res_419_;
}
pub unsafe fn l_Lean_ForEachExpr_visit___redArg___lam__2(
    mut v_inst_420_: *mut crate::leanh::LeanObject,
    mut v_inst_421_: *mut crate::leanh::LeanObject,
    mut v_g_422_: *mut crate::leanh::LeanObject,
    mut v_value_423_: *mut crate::leanh::LeanObject,
    mut v_a_424_: *mut crate::leanh::LeanObject,
    mut v_toBind_425_: *mut crate::leanh::LeanObject,
    mut v___f_426_: *mut crate::leanh::LeanObject,
    mut v_a_427_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_428_ = l_Lean_ForEachExpr_visit___redArg(
        v_inst_420_,
        v_inst_421_,
        v_g_422_,
        v_value_423_,
        v_a_424_,
    );
    v___x_429_ = crate::leanh::lean_apply_4(
        v_toBind_425_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_428_,
        v___f_426_,
    );
    return v___x_429_;
}
pub unsafe fn l_Lean_ForEachExpr_visit___redArg___lam__2___boxed(
    mut v_inst_430_: *mut crate::leanh::LeanObject,
    mut v_inst_431_: *mut crate::leanh::LeanObject,
    mut v_g_432_: *mut crate::leanh::LeanObject,
    mut v_value_433_: *mut crate::leanh::LeanObject,
    mut v_a_434_: *mut crate::leanh::LeanObject,
    mut v_toBind_435_: *mut crate::leanh::LeanObject,
    mut v___f_436_: *mut crate::leanh::LeanObject,
    mut v_a_437_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_438_ = l_Lean_ForEachExpr_visit___redArg___lam__2(
        v_inst_430_,
        v_inst_431_,
        v_g_432_,
        v_value_433_,
        v_a_434_,
        v_toBind_435_,
        v___f_436_,
        v_a_437_,
    );
    crate::leanh::lean_dec(v_a_434_);
    return v_res_438_;
}
pub unsafe fn l_Lean_ForEachExpr_visit___redArg___lam__3(
    mut v_inst_439_: *mut crate::leanh::LeanObject,
    mut v_inst_440_: *mut crate::leanh::LeanObject,
    mut v_g_441_: *mut crate::leanh::LeanObject,
    mut v_arg_442_: *mut crate::leanh::LeanObject,
    mut v_a_443_: *mut crate::leanh::LeanObject,
    mut v_a_444_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_445_ =
        l_Lean_ForEachExpr_visit___redArg(v_inst_439_, v_inst_440_, v_g_441_, v_arg_442_, v_a_443_);
    return v___x_445_;
}
pub unsafe fn l_Lean_ForEachExpr_visit___redArg___lam__3___boxed(
    mut v_inst_446_: *mut crate::leanh::LeanObject,
    mut v_inst_447_: *mut crate::leanh::LeanObject,
    mut v_g_448_: *mut crate::leanh::LeanObject,
    mut v_arg_449_: *mut crate::leanh::LeanObject,
    mut v_a_450_: *mut crate::leanh::LeanObject,
    mut v_a_451_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_452_ = l_Lean_ForEachExpr_visit___redArg___lam__3(
        v_inst_446_,
        v_inst_447_,
        v_g_448_,
        v_arg_449_,
        v_a_450_,
        v_a_451_,
    );
    crate::leanh::lean_dec(v_a_450_);
    return v_res_452_;
}
pub unsafe fn l_Lean_ForEachExpr_visit___redArg___lam__4(
    mut v_toApplicative_453_: *mut crate::leanh::LeanObject,
    mut v_inst_454_: *mut crate::leanh::LeanObject,
    mut v_inst_455_: *mut crate::leanh::LeanObject,
    mut v_g_456_: *mut crate::leanh::LeanObject,
    mut v_toBind_457_: *mut crate::leanh::LeanObject,
    mut v_e_458_: *mut crate::leanh::LeanObject,
    mut v_a_459_: *mut crate::leanh::LeanObject,
    mut v_a_460_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v_d_462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_a_460_ == 0 {
                    crate::leanh::lean_dec_ref(v_e_458_);
                    crate::leanh::lean_dec(v_toBind_457_);
                    crate::leanh::lean_dec(v_g_456_);
                    crate::leanh::lean_dec_ref(v_inst_455_);
                    crate::leanh::lean_dec(v_inst_454_);
                    v_toPure_468_ = crate::leanh::lean_ctor_get(v_toApplicative_453_, 1);
                    crate::leanh::lean_inc(v_toPure_468_);
                    crate::leanh::lean_dec_ref(v_toApplicative_453_);
                    v___x_469_ = crate::leanh::lean_box(0);
                    v___x_470_ = crate::leanh::lean_apply_2(
                        v_toPure_468_,
                        crate::leanh::lean_box(0),
                        v___x_469_,
                    );
                    return v___x_470_;
                } else {
                    match crate::leanh::lean_obj_tag(v_e_458_) {
                        7 => {
                            crate::leanh::lean_dec_ref(v_toApplicative_453_);
                            v_binderType_471_ = crate::leanh::lean_ctor_get(v_e_458_, 1);
                            crate::leanh::lean_inc_ref(v_binderType_471_);
                            v_body_472_ = crate::leanh::lean_ctor_get(v_e_458_, 2);
                            crate::leanh::lean_inc_ref(v_body_472_);
                            crate::leanh::lean_dec_ref_known(v_e_458_, 3);
                            v_d_462_ = v_binderType_471_;
                            v_b_463_ = v_body_472_;
                            v___y_464_ = v_a_459_;
                            state = 1;
                            continue;
                        }
                        6 => {
                            crate::leanh::lean_dec_ref(v_toApplicative_453_);
                            v_binderType_473_ = crate::leanh::lean_ctor_get(v_e_458_, 1);
                            crate::leanh::lean_inc_ref(v_binderType_473_);
                            v_body_474_ = crate::leanh::lean_ctor_get(v_e_458_, 2);
                            crate::leanh::lean_inc_ref(v_body_474_);
                            crate::leanh::lean_dec_ref_known(v_e_458_, 3);
                            v_d_462_ = v_binderType_473_;
                            v_b_463_ = v_body_474_;
                            v___y_464_ = v_a_459_;
                            state = 1;
                            continue;
                        }
                        8 => {
                            crate::leanh::lean_dec_ref(v_toApplicative_453_);
                            v_type_475_ = crate::leanh::lean_ctor_get(v_e_458_, 1);
                            crate::leanh::lean_inc_ref(v_type_475_);
                            v_value_476_ = crate::leanh::lean_ctor_get(v_e_458_, 2);
                            crate::leanh::lean_inc_ref(v_value_476_);
                            v_body_477_ = crate::leanh::lean_ctor_get(v_e_458_, 3);
                            crate::leanh::lean_inc_ref(v_body_477_);
                            crate::leanh::lean_dec_ref_known(v_e_458_, 4);
                            crate::leanh::lean_inc_n(v_a_459_, 2);
                            crate::leanh::lean_inc_n(v_g_456_, 2);
                            crate::leanh::lean_inc_ref_n(v_inst_455_, 2);
                            crate::leanh::lean_inc_n(v_inst_454_, 2);
                            v___f_478_ = crate::leanh::lean_alloc_closure(
                                l_Lean_ForEachExpr_visit___redArg___lam__1___boxed
                                    as *mut core::ffi::c_void,
                                6,
                                5,
                            );
                            crate::leanh::lean_closure_set(v___f_478_, 0, v_inst_454_);
                            crate::leanh::lean_closure_set(v___f_478_, 1, v_inst_455_);
                            crate::leanh::lean_closure_set(v___f_478_, 2, v_g_456_);
                            crate::leanh::lean_closure_set(v___f_478_, 3, v_body_477_);
                            crate::leanh::lean_closure_set(v___f_478_, 4, v_a_459_);
                            crate::leanh::lean_inc(v_toBind_457_);
                            v___f_479_ = crate::leanh::lean_alloc_closure(
                                l_Lean_ForEachExpr_visit___redArg___lam__2___boxed
                                    as *mut core::ffi::c_void,
                                8,
                                7,
                            );
                            crate::leanh::lean_closure_set(v___f_479_, 0, v_inst_454_);
                            crate::leanh::lean_closure_set(v___f_479_, 1, v_inst_455_);
                            crate::leanh::lean_closure_set(v___f_479_, 2, v_g_456_);
                            crate::leanh::lean_closure_set(v___f_479_, 3, v_value_476_);
                            crate::leanh::lean_closure_set(v___f_479_, 4, v_a_459_);
                            crate::leanh::lean_closure_set(v___f_479_, 5, v_toBind_457_);
                            crate::leanh::lean_closure_set(v___f_479_, 6, v___f_478_);
                            v___x_480_ = l_Lean_ForEachExpr_visit___redArg(
                                v_inst_454_,
                                v_inst_455_,
                                v_g_456_,
                                v_type_475_,
                                v_a_459_,
                            );
                            v___x_481_ = crate::leanh::lean_apply_4(
                                v_toBind_457_,
                                crate::leanh::lean_box(0),
                                crate::leanh::lean_box(0),
                                v___x_480_,
                                v___f_479_,
                            );
                            return v___x_481_;
                        }
                        5 => {
                            crate::leanh::lean_dec_ref(v_toApplicative_453_);
                            v_fn_482_ = crate::leanh::lean_ctor_get(v_e_458_, 0);
                            crate::leanh::lean_inc_ref(v_fn_482_);
                            v_arg_483_ = crate::leanh::lean_ctor_get(v_e_458_, 1);
                            crate::leanh::lean_inc_ref(v_arg_483_);
                            crate::leanh::lean_dec_ref_known(v_e_458_, 2);
                            crate::leanh::lean_inc(v_a_459_);
                            crate::leanh::lean_inc(v_g_456_);
                            crate::leanh::lean_inc_ref(v_inst_455_);
                            crate::leanh::lean_inc(v_inst_454_);
                            v___f_484_ = crate::leanh::lean_alloc_closure(
                                l_Lean_ForEachExpr_visit___redArg___lam__3___boxed
                                    as *mut core::ffi::c_void,
                                6,
                                5,
                            );
                            crate::leanh::lean_closure_set(v___f_484_, 0, v_inst_454_);
                            crate::leanh::lean_closure_set(v___f_484_, 1, v_inst_455_);
                            crate::leanh::lean_closure_set(v___f_484_, 2, v_g_456_);
                            crate::leanh::lean_closure_set(v___f_484_, 3, v_arg_483_);
                            crate::leanh::lean_closure_set(v___f_484_, 4, v_a_459_);
                            v___x_485_ = l_Lean_ForEachExpr_visit___redArg(
                                v_inst_454_,
                                v_inst_455_,
                                v_g_456_,
                                v_fn_482_,
                                v_a_459_,
                            );
                            v___x_486_ = crate::leanh::lean_apply_4(
                                v_toBind_457_,
                                crate::leanh::lean_box(0),
                                crate::leanh::lean_box(0),
                                v___x_485_,
                                v___f_484_,
                            );
                            return v___x_486_;
                        }
                        10 => {
                            crate::leanh::lean_dec(v_toBind_457_);
                            crate::leanh::lean_dec_ref(v_toApplicative_453_);
                            v_expr_487_ = crate::leanh::lean_ctor_get(v_e_458_, 1);
                            crate::leanh::lean_inc_ref(v_expr_487_);
                            crate::leanh::lean_dec_ref_known(v_e_458_, 2);
                            v___x_488_ = l_Lean_ForEachExpr_visit___redArg(
                                v_inst_454_,
                                v_inst_455_,
                                v_g_456_,
                                v_expr_487_,
                                v_a_459_,
                            );
                            return v___x_488_;
                        }
                        11 => {
                            crate::leanh::lean_dec(v_toBind_457_);
                            crate::leanh::lean_dec_ref(v_toApplicative_453_);
                            v_struct_489_ = crate::leanh::lean_ctor_get(v_e_458_, 2);
                            crate::leanh::lean_inc_ref(v_struct_489_);
                            crate::leanh::lean_dec_ref_known(v_e_458_, 3);
                            v___x_490_ = l_Lean_ForEachExpr_visit___redArg(
                                v_inst_454_,
                                v_inst_455_,
                                v_g_456_,
                                v_struct_489_,
                                v_a_459_,
                            );
                            return v___x_490_;
                        }
                        _ => {
                            crate::leanh::lean_dec_ref(v_e_458_);
                            crate::leanh::lean_dec(v_toBind_457_);
                            crate::leanh::lean_dec(v_g_456_);
                            crate::leanh::lean_dec_ref(v_inst_455_);
                            crate::leanh::lean_dec(v_inst_454_);
                            v_toPure_491_ = crate::leanh::lean_ctor_get(v_toApplicative_453_, 1);
                            crate::leanh::lean_inc(v_toPure_491_);
                            crate::leanh::lean_dec_ref(v_toApplicative_453_);
                            v___x_492_ = crate::leanh::lean_box(0);
                            v___x_493_ = crate::leanh::lean_apply_2(
                                v_toPure_491_,
                                crate::leanh::lean_box(0),
                                v___x_492_,
                            );
                            return v___x_493_;
                        }
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v___y_464_);
                crate::leanh::lean_inc(v_g_456_);
                crate::leanh::lean_inc_ref(v_inst_455_);
                crate::leanh::lean_inc(v_inst_454_);
                v___f_465_ = crate::leanh::lean_alloc_closure(
                    l_Lean_ForEachExpr_visit___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    6,
                    5,
                );
                crate::leanh::lean_closure_set(v___f_465_, 0, v_inst_454_);
                crate::leanh::lean_closure_set(v___f_465_, 1, v_inst_455_);
                crate::leanh::lean_closure_set(v___f_465_, 2, v_g_456_);
                crate::leanh::lean_closure_set(v___f_465_, 3, v_b_463_);
                crate::leanh::lean_closure_set(v___f_465_, 4, v___y_464_);
                v___x_466_ = l_Lean_ForEachExpr_visit___redArg(
                    v_inst_454_,
                    v_inst_455_,
                    v_g_456_,
                    v_d_462_,
                    v___y_464_,
                );
                v___x_467_ = crate::leanh::lean_apply_4(
                    v_toBind_457_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_466_,
                    v___f_465_,
                );
                return v___x_467_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ForEachExpr_visit___redArg___lam__4___boxed(
    mut v_toApplicative_494_: *mut crate::leanh::LeanObject,
    mut v_inst_495_: *mut crate::leanh::LeanObject,
    mut v_inst_496_: *mut crate::leanh::LeanObject,
    mut v_g_497_: *mut crate::leanh::LeanObject,
    mut v_toBind_498_: *mut crate::leanh::LeanObject,
    mut v_e_499_: *mut crate::leanh::LeanObject,
    mut v_a_500_: *mut crate::leanh::LeanObject,
    mut v_a_501_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_502_: u8 = 0;
    let mut v_res_503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_502_ = (crate::leanh::lean_unbox(v_a_501_) as u8);
    v_res_503_ = l_Lean_ForEachExpr_visit___redArg___lam__4(
        v_toApplicative_494_,
        v_inst_495_,
        v_inst_496_,
        v_g_497_,
        v_toBind_498_,
        v_e_499_,
        v_a_500_,
        v_a_boxed_502_,
    );
    crate::leanh::lean_dec(v_a_500_);
    return v_res_503_;
}
pub unsafe fn l_Lean_ForEachExpr_visit___redArg(
    mut v_inst_506_: *mut crate::leanh::LeanObject,
    mut v_inst_507_: *mut crate::leanh::LeanObject,
    mut v_g_508_: *mut crate::leanh::LeanObject,
    mut v_e_509_: *mut crate::leanh::LeanObject,
    mut v_a_510_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_511_ = crate::leanh::lean_ctor_get(v_inst_507_, 0);
    crate::leanh::lean_inc_ref_n(v_toApplicative_511_, 4);
    v_toBind_512_ = crate::leanh::lean_ctor_get(v_inst_507_, 1);
    crate::leanh::lean_inc_n(v_toBind_512_, 5);
    crate::leanh::lean_inc_n(v_a_510_, 3);
    crate::leanh::lean_inc_ref_n(v_e_509_, 3);
    crate::leanh::lean_inc(v_g_508_);
    crate::leanh::lean_inc_n(v_inst_506_, 2);
    v___f_513_ = crate::leanh::lean_alloc_closure(
        l_Lean_ForEachExpr_visit___redArg___lam__4___boxed as *mut core::ffi::c_void,
        8,
        7,
    );
    crate::leanh::lean_closure_set(v___f_513_, 0, v_toApplicative_511_);
    crate::leanh::lean_closure_set(v___f_513_, 1, v_inst_506_);
    crate::leanh::lean_closure_set(v___f_513_, 2, v_inst_507_);
    crate::leanh::lean_closure_set(v___f_513_, 3, v_g_508_);
    crate::leanh::lean_closure_set(v___f_513_, 4, v_toBind_512_);
    crate::leanh::lean_closure_set(v___f_513_, 5, v_e_509_);
    crate::leanh::lean_closure_set(v___f_513_, 6, v_a_510_);
    v___x_514_ = l_Lean_ForEachExpr_visit___redArg___closed__0;
    v___x_515_ = l_Lean_ForEachExpr_visit___redArg___closed__1;
    v___f_516_ = crate::leanh::lean_alloc_closure(
        l_Lean_ForEachExpr_visit___redArg___lam__7___boxed as *mut core::ffi::c_void,
        8,
        7,
    );
    crate::leanh::lean_closure_set(v___f_516_, 0, v_toApplicative_511_);
    crate::leanh::lean_closure_set(v___f_516_, 1, v___x_514_);
    crate::leanh::lean_closure_set(v___f_516_, 2, v___x_515_);
    crate::leanh::lean_closure_set(v___f_516_, 3, v_e_509_);
    crate::leanh::lean_closure_set(v___f_516_, 4, v_a_510_);
    crate::leanh::lean_closure_set(v___f_516_, 5, v_inst_506_);
    crate::leanh::lean_closure_set(v___f_516_, 6, v_toBind_512_);
    v___f_517_ = crate::leanh::lean_alloc_closure(
        l_Lean_ForEachExpr_visit___redArg___lam__8 as *mut core::ffi::c_void,
        7,
        6,
    );
    crate::leanh::lean_closure_set(v___f_517_, 0, v_g_508_);
    crate::leanh::lean_closure_set(v___f_517_, 1, v_e_509_);
    crate::leanh::lean_closure_set(v___f_517_, 2, v_toBind_512_);
    crate::leanh::lean_closure_set(v___f_517_, 3, v___f_513_);
    crate::leanh::lean_closure_set(v___f_517_, 4, v___f_516_);
    crate::leanh::lean_closure_set(v___f_517_, 5, v_toApplicative_511_);
    v___f_518_ = crate::leanh::lean_alloc_closure(
        l_Lean_ForEachExpr_visit___redArg___lam__9___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_518_, 0, v_toApplicative_511_);
    crate::leanh::lean_closure_set(v___f_518_, 1, v___x_514_);
    crate::leanh::lean_closure_set(v___f_518_, 2, v___x_515_);
    crate::leanh::lean_closure_set(v___f_518_, 3, v_e_509_);
    v___x_519_ =
        crate::leanh::lean_alloc_closure(l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void, 4, 3);
    crate::leanh::lean_closure_set(v___x_519_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_519_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_519_, 2, v_a_510_);
    v___x_520_ = crate::leanh::lean_apply_2(v_inst_506_, crate::leanh::lean_box(0), v___x_519_);
    v___x_521_ = crate::leanh::lean_apply_4(
        v_toBind_512_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_520_,
        v___f_518_,
    );
    v___x_522_ = crate::leanh::lean_apply_4(
        v_toBind_512_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_521_,
        v___f_517_,
    );
    return v___x_522_;
}
pub unsafe fn l_Lean_ForEachExpr_visit___redArg___lam__0(
    mut v_inst_523_: *mut crate::leanh::LeanObject,
    mut v_inst_524_: *mut crate::leanh::LeanObject,
    mut v_g_525_: *mut crate::leanh::LeanObject,
    mut v_b_526_: *mut crate::leanh::LeanObject,
    mut v___y_527_: *mut crate::leanh::LeanObject,
    mut v_a_528_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_529_ =
        l_Lean_ForEachExpr_visit___redArg(v_inst_523_, v_inst_524_, v_g_525_, v_b_526_, v___y_527_);
    return v___x_529_;
}
pub unsafe fn l_Lean_ForEachExpr_visit___redArg___boxed(
    mut v_inst_530_: *mut crate::leanh::LeanObject,
    mut v_inst_531_: *mut crate::leanh::LeanObject,
    mut v_g_532_: *mut crate::leanh::LeanObject,
    mut v_e_533_: *mut crate::leanh::LeanObject,
    mut v_a_534_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_535_ =
        l_Lean_ForEachExpr_visit___redArg(v_inst_530_, v_inst_531_, v_g_532_, v_e_533_, v_a_534_);
    crate::leanh::lean_dec(v_a_534_);
    return v_res_535_;
}
pub unsafe fn l_Lean_ForEachExpr_visit(
    mut v_00_u03c9_536_: *mut crate::leanh::LeanObject,
    mut v_m_537_: *mut crate::leanh::LeanObject,
    mut v_inst_538_: *mut crate::leanh::LeanObject,
    mut v_inst_539_: *mut crate::leanh::LeanObject,
    mut v_inst_540_: *mut crate::leanh::LeanObject,
    mut v_g_541_: *mut crate::leanh::LeanObject,
    mut v_e_542_: *mut crate::leanh::LeanObject,
    mut v_a_543_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_544_ =
        l_Lean_ForEachExpr_visit___redArg(v_inst_539_, v_inst_540_, v_g_541_, v_e_542_, v_a_543_);
    return v___x_544_;
}
pub unsafe fn l_Lean_ForEachExpr_visit___boxed(
    mut v_00_u03c9_545_: *mut crate::leanh::LeanObject,
    mut v_m_546_: *mut crate::leanh::LeanObject,
    mut v_inst_547_: *mut crate::leanh::LeanObject,
    mut v_inst_548_: *mut crate::leanh::LeanObject,
    mut v_inst_549_: *mut crate::leanh::LeanObject,
    mut v_g_550_: *mut crate::leanh::LeanObject,
    mut v_e_551_: *mut crate::leanh::LeanObject,
    mut v_a_552_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_553_ = l_Lean_ForEachExpr_visit(
        v_00_u03c9_545_,
        v_m_546_,
        v_inst_547_,
        v_inst_548_,
        v_inst_549_,
        v_g_550_,
        v_e_551_,
        v_a_552_,
    );
    crate::leanh::lean_dec(v_a_552_);
    return v_res_553_;
}
pub unsafe fn l_Lean_Expr_forEach_x27___redArg___lam__0(
    mut v_toPure_554_: *mut crate::leanh::LeanObject,
    mut v_____x_555_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_556_ = crate::leanh::lean_ctor_get(v_____x_555_, 0);
    crate::leanh::lean_inc(v_fst_556_);
    crate::leanh::lean_dec_ref(v_____x_555_);
    v___x_557_ = crate::leanh::lean_apply_2(v_toPure_554_, crate::leanh::lean_box(0), v_fst_556_);
    return v___x_557_;
}
pub unsafe fn l_Lean_Expr_forEach_x27___redArg___lam__1(
    mut v_a_558_: *mut crate::leanh::LeanObject,
    mut v_toPure_559_: *mut crate::leanh::LeanObject,
    mut v_s_560_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_561_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_561_, 0, v_a_558_);
    crate::leanh::lean_ctor_set(v___x_561_, 1, v_s_560_);
    v___x_562_ = crate::leanh::lean_apply_2(v_toPure_559_, crate::leanh::lean_box(0), v___x_561_);
    return v___x_562_;
}
pub unsafe fn l_Lean_Expr_forEach_x27___redArg___lam__2(
    mut v_toPure_563_: *mut crate::leanh::LeanObject,
    mut v_ref_564_: *mut crate::leanh::LeanObject,
    mut v_inst_565_: *mut crate::leanh::LeanObject,
    mut v_toBind_566_: *mut crate::leanh::LeanObject,
    mut v_a_567_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_568_ = crate::leanh::lean_alloc_closure(
        l_Lean_Expr_forEach_x27___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_568_, 0, v_a_567_);
    crate::leanh::lean_closure_set(v___f_568_, 1, v_toPure_563_);
    v___x_569_ =
        crate::leanh::lean_alloc_closure(l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void, 4, 3);
    crate::leanh::lean_closure_set(v___x_569_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_569_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_569_, 2, v_ref_564_);
    v___x_570_ = crate::leanh::lean_apply_2(v_inst_565_, crate::leanh::lean_box(0), v___x_569_);
    v___x_571_ = crate::leanh::lean_apply_4(
        v_toBind_566_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_570_,
        v___f_568_,
    );
    return v___x_571_;
}
pub unsafe fn l_Lean_Expr_forEach_x27___redArg___lam__3(
    mut v_toPure_572_: *mut crate::leanh::LeanObject,
    mut v_inst_573_: *mut crate::leanh::LeanObject,
    mut v_toBind_574_: *mut crate::leanh::LeanObject,
    mut v_inst_575_: *mut crate::leanh::LeanObject,
    mut v_f_576_: *mut crate::leanh::LeanObject,
    mut v_e_577_: *mut crate::leanh::LeanObject,
    mut v_ref_578_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_toBind_574_);
    crate::leanh::lean_inc(v_inst_573_);
    crate::leanh::lean_inc(v_ref_578_);
    v___f_579_ = crate::leanh::lean_alloc_closure(
        l_Lean_Expr_forEach_x27___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_579_, 0, v_toPure_572_);
    crate::leanh::lean_closure_set(v___f_579_, 1, v_ref_578_);
    crate::leanh::lean_closure_set(v___f_579_, 2, v_inst_573_);
    crate::leanh::lean_closure_set(v___f_579_, 3, v_toBind_574_);
    v___x_580_ =
        l_Lean_ForEachExpr_visit___redArg(v_inst_573_, v_inst_575_, v_f_576_, v_e_577_, v_ref_578_);
    crate::leanh::lean_dec(v_ref_578_);
    v___x_581_ = crate::leanh::lean_apply_4(
        v_toBind_574_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_580_,
        v___f_579_,
    );
    return v___x_581_;
}
pub unsafe fn _init_l_Lean_Expr_forEach_x27___redArg___closed__0() -> *mut crate::leanh::LeanObject
{
    let mut v___x_582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_582_ = crate::leanh::lean_box(0);
    v___x_583_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_584_ = lean_mk_array(v___x_583_, v___x_582_);
    return v___x_584_;
}
pub unsafe fn _init_l_Lean_Expr_forEach_x27___redArg___closed__1() -> *mut crate::leanh::LeanObject
{
    let mut v___x_585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_585_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Expr_forEach_x27___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Expr_forEach_x27___redArg___closed__0_once),
        _init_l_Lean_Expr_forEach_x27___redArg___closed__0,
    );
    v___x_586_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_587_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_587_, 0, v___x_586_);
    crate::leanh::lean_ctor_set(v___x_587_, 1, v___x_585_);
    return v___x_587_;
}
pub unsafe fn _init_l_Lean_Expr_forEach_x27___redArg___closed__2() -> *mut crate::leanh::LeanObject
{
    let mut v___x_588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_588_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Expr_forEach_x27___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Expr_forEach_x27___redArg___closed__1_once),
        _init_l_Lean_Expr_forEach_x27___redArg___closed__1,
    );
    v___x_589_ =
        crate::leanh::lean_alloc_closure(l_ST_Prim_mkRef___boxed as *mut core::ffi::c_void, 4, 3);
    crate::leanh::lean_closure_set(v___x_589_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_589_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_589_, 2, v___x_588_);
    return v___x_589_;
}
pub unsafe fn l_Lean_Expr_forEach_x27___redArg(
    mut v_inst_590_: *mut crate::leanh::LeanObject,
    mut v_inst_591_: *mut crate::leanh::LeanObject,
    mut v_e_592_: *mut crate::leanh::LeanObject,
    mut v_f_593_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_594_ = crate::leanh::lean_ctor_get(v_inst_591_, 0);
    v_toBind_595_ = crate::leanh::lean_ctor_get(v_inst_591_, 1);
    crate::leanh::lean_inc_n(v_toBind_595_, 3);
    v_toPure_596_ = crate::leanh::lean_ctor_get(v_toApplicative_594_, 1);
    crate::leanh::lean_inc_n(v_toPure_596_, 2);
    v___x_597_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Expr_forEach_x27___redArg___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Expr_forEach_x27___redArg___closed__2_once),
        _init_l_Lean_Expr_forEach_x27___redArg___closed__2,
    );
    crate::leanh::lean_inc(v_inst_590_);
    v___x_598_ = crate::leanh::lean_apply_2(v_inst_590_, crate::leanh::lean_box(0), v___x_597_);
    v___f_599_ = crate::leanh::lean_alloc_closure(
        l_Lean_Expr_forEach_x27___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_599_, 0, v_toPure_596_);
    v___f_600_ = crate::leanh::lean_alloc_closure(
        l_Lean_Expr_forEach_x27___redArg___lam__3 as *mut core::ffi::c_void,
        7,
        6,
    );
    crate::leanh::lean_closure_set(v___f_600_, 0, v_toPure_596_);
    crate::leanh::lean_closure_set(v___f_600_, 1, v_inst_590_);
    crate::leanh::lean_closure_set(v___f_600_, 2, v_toBind_595_);
    crate::leanh::lean_closure_set(v___f_600_, 3, v_inst_591_);
    crate::leanh::lean_closure_set(v___f_600_, 4, v_f_593_);
    crate::leanh::lean_closure_set(v___f_600_, 5, v_e_592_);
    v___x_601_ = crate::leanh::lean_apply_4(
        v_toBind_595_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_598_,
        v___f_600_,
    );
    v___x_602_ = crate::leanh::lean_apply_4(
        v_toBind_595_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_601_,
        v___f_599_,
    );
    return v___x_602_;
}
pub unsafe fn l_Lean_Expr_forEach_x27(
    mut v_00_u03c9_603_: *mut crate::leanh::LeanObject,
    mut v_m_604_: *mut crate::leanh::LeanObject,
    mut v_inst_605_: *mut crate::leanh::LeanObject,
    mut v_inst_606_: *mut crate::leanh::LeanObject,
    mut v_inst_607_: *mut crate::leanh::LeanObject,
    mut v_e_608_: *mut crate::leanh::LeanObject,
    mut v_f_609_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_610_ = crate::leanh::lean_ctor_get(v_inst_607_, 0);
    v_toBind_611_ = crate::leanh::lean_ctor_get(v_inst_607_, 1);
    crate::leanh::lean_inc_n(v_toBind_611_, 3);
    v_toPure_612_ = crate::leanh::lean_ctor_get(v_toApplicative_610_, 1);
    crate::leanh::lean_inc_n(v_toPure_612_, 2);
    v___x_613_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Expr_forEach_x27___redArg___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Expr_forEach_x27___redArg___closed__2_once),
        _init_l_Lean_Expr_forEach_x27___redArg___closed__2,
    );
    crate::leanh::lean_inc(v_inst_606_);
    v___x_614_ = crate::leanh::lean_apply_2(v_inst_606_, crate::leanh::lean_box(0), v___x_613_);
    v___f_615_ = crate::leanh::lean_alloc_closure(
        l_Lean_Expr_forEach_x27___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_615_, 0, v_toPure_612_);
    v___f_616_ = crate::leanh::lean_alloc_closure(
        l_Lean_Expr_forEach_x27___redArg___lam__3 as *mut core::ffi::c_void,
        7,
        6,
    );
    crate::leanh::lean_closure_set(v___f_616_, 0, v_toPure_612_);
    crate::leanh::lean_closure_set(v___f_616_, 1, v_inst_606_);
    crate::leanh::lean_closure_set(v___f_616_, 2, v_toBind_611_);
    crate::leanh::lean_closure_set(v___f_616_, 3, v_inst_607_);
    crate::leanh::lean_closure_set(v___f_616_, 4, v_f_609_);
    crate::leanh::lean_closure_set(v___f_616_, 5, v_e_608_);
    v___x_617_ = crate::leanh::lean_apply_4(
        v_toBind_611_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_614_,
        v___f_616_,
    );
    v___x_618_ = crate::leanh::lean_apply_4(
        v_toBind_611_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_617_,
        v___f_615_,
    );
    return v___x_618_;
}
pub unsafe fn l_Lean_Expr_forEach___redArg___lam__1(
    mut v_toPure_619_: *mut crate::leanh::LeanObject,
    mut v_____r_620_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_621_: u8 = 0;
    let mut v___x_622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_621_ = 1;
    v___x_622_ = crate::leanh::lean_box((v___x_621_) as usize);
    v___x_623_ = crate::leanh::lean_apply_2(v_toPure_619_, crate::leanh::lean_box(0), v___x_622_);
    return v___x_623_;
}
pub unsafe fn l_Lean_Expr_forEach___redArg___lam__0(
    mut v_f_624_: *mut crate::leanh::LeanObject,
    mut v_toBind_625_: *mut crate::leanh::LeanObject,
    mut v___f_626_: *mut crate::leanh::LeanObject,
    mut v_e_627_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_628_ = crate::leanh::lean_apply_1(v_f_624_, v_e_627_);
    v___x_629_ = crate::leanh::lean_apply_4(
        v_toBind_625_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_628_,
        v___f_626_,
    );
    return v___x_629_;
}
pub unsafe fn l_Lean_Expr_forEach___redArg___lam__4(
    mut v_toPure_630_: *mut crate::leanh::LeanObject,
    mut v_inst_631_: *mut crate::leanh::LeanObject,
    mut v_toBind_632_: *mut crate::leanh::LeanObject,
    mut v_inst_633_: *mut crate::leanh::LeanObject,
    mut v___f_634_: *mut crate::leanh::LeanObject,
    mut v_e_635_: *mut crate::leanh::LeanObject,
    mut v_ref_636_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_toBind_632_);
    crate::leanh::lean_inc(v_inst_631_);
    crate::leanh::lean_inc(v_ref_636_);
    v___f_637_ = crate::leanh::lean_alloc_closure(
        l_Lean_Expr_forEach_x27___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_637_, 0, v_toPure_630_);
    crate::leanh::lean_closure_set(v___f_637_, 1, v_ref_636_);
    crate::leanh::lean_closure_set(v___f_637_, 2, v_inst_631_);
    crate::leanh::lean_closure_set(v___f_637_, 3, v_toBind_632_);
    v___x_638_ = l_Lean_ForEachExpr_visit___redArg(
        v_inst_631_,
        v_inst_633_,
        v___f_634_,
        v_e_635_,
        v_ref_636_,
    );
    crate::leanh::lean_dec(v_ref_636_);
    v___x_639_ = crate::leanh::lean_apply_4(
        v_toBind_632_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_638_,
        v___f_637_,
    );
    return v___x_639_;
}
pub unsafe fn l_Lean_Expr_forEach___redArg(
    mut v_inst_640_: *mut crate::leanh::LeanObject,
    mut v_inst_641_: *mut crate::leanh::LeanObject,
    mut v_e_642_: *mut crate::leanh::LeanObject,
    mut v_f_643_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_644_ = crate::leanh::lean_ctor_get(v_inst_641_, 0);
    v_toBind_645_ = crate::leanh::lean_ctor_get(v_inst_641_, 1);
    crate::leanh::lean_inc_n(v_toBind_645_, 4);
    v_toPure_646_ = crate::leanh::lean_ctor_get(v_toApplicative_644_, 1);
    crate::leanh::lean_inc_n(v_toPure_646_, 3);
    v___f_647_ = crate::leanh::lean_alloc_closure(
        l_Lean_Expr_forEach_x27___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_647_, 0, v_toPure_646_);
    v___f_648_ = crate::leanh::lean_alloc_closure(
        l_Lean_Expr_forEach___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_648_, 0, v_toPure_646_);
    v___f_649_ = crate::leanh::lean_alloc_closure(
        l_Lean_Expr_forEach___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_649_, 0, v_f_643_);
    crate::leanh::lean_closure_set(v___f_649_, 1, v_toBind_645_);
    crate::leanh::lean_closure_set(v___f_649_, 2, v___f_648_);
    crate::leanh::lean_inc(v_inst_640_);
    v___f_650_ = crate::leanh::lean_alloc_closure(
        l_Lean_Expr_forEach___redArg___lam__4 as *mut core::ffi::c_void,
        7,
        6,
    );
    crate::leanh::lean_closure_set(v___f_650_, 0, v_toPure_646_);
    crate::leanh::lean_closure_set(v___f_650_, 1, v_inst_640_);
    crate::leanh::lean_closure_set(v___f_650_, 2, v_toBind_645_);
    crate::leanh::lean_closure_set(v___f_650_, 3, v_inst_641_);
    crate::leanh::lean_closure_set(v___f_650_, 4, v___f_649_);
    crate::leanh::lean_closure_set(v___f_650_, 5, v_e_642_);
    v___x_651_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Expr_forEach_x27___redArg___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Expr_forEach_x27___redArg___closed__2_once),
        _init_l_Lean_Expr_forEach_x27___redArg___closed__2,
    );
    v___x_652_ = crate::leanh::lean_apply_2(v_inst_640_, crate::leanh::lean_box(0), v___x_651_);
    v___x_653_ = crate::leanh::lean_apply_4(
        v_toBind_645_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_652_,
        v___f_650_,
    );
    v___x_654_ = crate::leanh::lean_apply_4(
        v_toBind_645_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_653_,
        v___f_647_,
    );
    return v___x_654_;
}
pub unsafe fn l_Lean_Expr_forEach(
    mut v_00_u03c9_655_: *mut crate::leanh::LeanObject,
    mut v_m_656_: *mut crate::leanh::LeanObject,
    mut v_inst_657_: *mut crate::leanh::LeanObject,
    mut v_inst_658_: *mut crate::leanh::LeanObject,
    mut v_inst_659_: *mut crate::leanh::LeanObject,
    mut v_e_660_: *mut crate::leanh::LeanObject,
    mut v_f_661_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_662_ = crate::leanh::lean_ctor_get(v_inst_659_, 0);
    v_toBind_663_ = crate::leanh::lean_ctor_get(v_inst_659_, 1);
    crate::leanh::lean_inc_n(v_toBind_663_, 4);
    v_toPure_664_ = crate::leanh::lean_ctor_get(v_toApplicative_662_, 1);
    crate::leanh::lean_inc_n(v_toPure_664_, 3);
    v___f_665_ = crate::leanh::lean_alloc_closure(
        l_Lean_Expr_forEach_x27___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_665_, 0, v_toPure_664_);
    v___f_666_ = crate::leanh::lean_alloc_closure(
        l_Lean_Expr_forEach___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_666_, 0, v_toPure_664_);
    v___f_667_ = crate::leanh::lean_alloc_closure(
        l_Lean_Expr_forEach___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_667_, 0, v_f_661_);
    crate::leanh::lean_closure_set(v___f_667_, 1, v_toBind_663_);
    crate::leanh::lean_closure_set(v___f_667_, 2, v___f_666_);
    crate::leanh::lean_inc(v_inst_658_);
    v___f_668_ = crate::leanh::lean_alloc_closure(
        l_Lean_Expr_forEach___redArg___lam__4 as *mut core::ffi::c_void,
        7,
        6,
    );
    crate::leanh::lean_closure_set(v___f_668_, 0, v_toPure_664_);
    crate::leanh::lean_closure_set(v___f_668_, 1, v_inst_658_);
    crate::leanh::lean_closure_set(v___f_668_, 2, v_toBind_663_);
    crate::leanh::lean_closure_set(v___f_668_, 3, v_inst_659_);
    crate::leanh::lean_closure_set(v___f_668_, 4, v___f_667_);
    crate::leanh::lean_closure_set(v___f_668_, 5, v_e_660_);
    v___x_669_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Expr_forEach_x27___redArg___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Expr_forEach_x27___redArg___closed__2_once),
        _init_l_Lean_Expr_forEach_x27___redArg___closed__2,
    );
    v___x_670_ = crate::leanh::lean_apply_2(v_inst_658_, crate::leanh::lean_box(0), v___x_669_);
    v___x_671_ = crate::leanh::lean_apply_4(
        v_toBind_663_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_670_,
        v___f_668_,
    );
    v___x_672_ = crate::leanh::lean_apply_4(
        v_toBind_663_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_671_,
        v___f_665_,
    );
    return v___x_672_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Util_ForEachExpr(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Expr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_MonadCache(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Util_ForEachExpr(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Util_ForEachExpr(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Expr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Util_MonadCache(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_ForEachExpr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Util_ForEachExpr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Util_ForEachExpr(builtin);
}
