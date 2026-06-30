// Lean compiler output
// Module: Lean.Util.MonadBacktrack
// Imports: Init.Control.Except Init.Control.Do Init.Data.Option.Coe
use crate::r#gen::Init::Control::Do::{
    initialize_Init_Control_Do, runtime_initialize_Init_Control_Do,
};
use crate::r#gen::Init::Control::Except::{
    initialize_Init_Control_Except, runtime_initialize_Init_Control_Except,
};
use crate::r#gen::Init::Data::Option::Coe::{
    initialize_Init_Data_Option_Coe, runtime_initialize_Init_Data_Option_Coe,
};
pub static l_Lean_commitWhenSomeNoEx_x3f___redArg___lam__1___closed__0_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l_Lean_commitWhenSomeNoEx_x3f___redArg___lam__1___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_commitWhenSomeNoEx_x3f___redArg___lam__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_withoutModifyingState___redArg___closed__0_value:
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
    m_fun: l_Lean_withoutModifyingState___redArg___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_withoutModifyingState___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_withoutModifyingState___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instMonadBacktrackExceptTOfMonad___redArg___closed__0_value:
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
    m_fun: l_Lean_instMonadBacktrackExceptTOfMonad___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instMonadBacktrackExceptTOfMonad___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instMonadBacktrackExceptTOfMonad___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instMonadBacktrackExceptTOfMonad___redArg___closed__1_value:
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
    m_fun: l_Lean_instMonadBacktrackExceptTOfMonad___redArg___lam__1 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instMonadBacktrackExceptTOfMonad___redArg___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instMonadBacktrackExceptTOfMonad___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lean_commitWhenSome_x3f___redArg___lam__0(
    mut v_toPure_345_: *mut leanh::LeanObject,
    mut v_r_346_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_348_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_347_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_347_, 0, v_r_346_);
    v___x_348_ = leanh::lean_apply_2(v_toPure_345_, leanh::lean_box(0), v___x_347_);
    return v___x_348_;
}
pub unsafe fn l_Lean_commitWhenSome_x3f___redArg___lam__1(
    mut v_toPure_349_: *mut leanh::LeanObject,
    mut v_e_350_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_352_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_351_ = leanh::lean_ctor_get(v_e_350_, 0);
    leanh::lean_inc(v_a_351_);
    leanh::lean_dec_ref(v_e_350_);
    v___x_352_ = leanh::lean_apply_2(v_toPure_349_, leanh::lean_box(0), v_a_351_);
    return v___x_352_;
}
pub unsafe fn l_Lean_commitWhenSome_x3f___redArg___lam__2(
    mut v_____do__lift_353_: *mut leanh::LeanObject,
    mut v_toPure_354_: *mut leanh::LeanObject,
    mut v_____r_355_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_357_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_356_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_356_, 0, v_____do__lift_353_);
    v___x_357_ = leanh::lean_apply_2(v_toPure_354_, leanh::lean_box(0), v___x_356_);
    return v___x_357_;
}
pub unsafe fn l_Lean_commitWhenSome_x3f___redArg___lam__3(
    mut v_toPure_358_: *mut leanh::LeanObject,
    mut v_restoreState_359_: *mut leanh::LeanObject,
    mut v_s_360_: *mut leanh::LeanObject,
    mut v_toBind_361_: *mut leanh::LeanObject,
    mut v_____do__lift_362_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_362_) == 0 {
        let mut v___f_363_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_364_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_365_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_363_ = leanh::lean_alloc_closure(
            l_Lean_commitWhenSome_x3f___redArg___lam__2 as *mut core::ffi::c_void,
            3,
            2,
        );
        leanh::lean_closure_set(v___f_363_, 0, v_____do__lift_362_);
        leanh::lean_closure_set(v___f_363_, 1, v_toPure_358_);
        v___x_364_ = leanh::lean_apply_1(v_restoreState_359_, v_s_360_);
        v___x_365_ = leanh::lean_apply_4(
            v_toBind_361_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_364_,
            v___f_363_,
        );
        return v___x_365_;
    } else {
        let mut v___x_366_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_367_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_toBind_361_);
        leanh::lean_dec(v_s_360_);
        leanh::lean_dec(v_restoreState_359_);
        v___x_366_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_366_, 0, v_____do__lift_362_);
        v___x_367_ =
            leanh::lean_apply_2(v_toPure_358_, leanh::lean_box(0), v___x_366_);
        return v___x_367_;
    }
}
pub unsafe fn l_Lean_commitWhenSome_x3f___redArg___lam__4(
    mut v_throw_368_: *mut leanh::LeanObject,
    mut v_ex_369_: *mut leanh::LeanObject,
    mut v_toBind_370_: *mut leanh::LeanObject,
    mut v___f_371_: *mut leanh::LeanObject,
    mut v_____r_372_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_374_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_373_ = leanh::lean_apply_2(v_throw_368_, leanh::lean_box(0), v_ex_369_);
    v___x_374_ = leanh::lean_apply_4(
        v_toBind_370_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_373_,
        v___f_371_,
    );
    return v___x_374_;
}
pub unsafe fn l_Lean_commitWhenSome_x3f___redArg___lam__5(
    mut v_throw_375_: *mut leanh::LeanObject,
    mut v_toBind_376_: *mut leanh::LeanObject,
    mut v___f_377_: *mut leanh::LeanObject,
    mut v_restoreState_378_: *mut leanh::LeanObject,
    mut v_s_379_: *mut leanh::LeanObject,
    mut v_ex_380_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_383_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_toBind_376_);
    v___f_381_ = leanh::lean_alloc_closure(
        l_Lean_commitWhenSome_x3f___redArg___lam__4 as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_381_, 0, v_throw_375_);
    leanh::lean_closure_set(v___f_381_, 1, v_ex_380_);
    leanh::lean_closure_set(v___f_381_, 2, v_toBind_376_);
    leanh::lean_closure_set(v___f_381_, 3, v___f_377_);
    v___x_382_ = leanh::lean_apply_1(v_restoreState_378_, v_s_379_);
    v___x_383_ = leanh::lean_apply_4(
        v_toBind_376_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_382_,
        v___f_381_,
    );
    return v___x_383_;
}
pub unsafe fn l_Lean_commitWhenSome_x3f___redArg___lam__6(
    mut v_inst_384_: *mut leanh::LeanObject,
    mut v_toPure_385_: *mut leanh::LeanObject,
    mut v_restoreState_386_: *mut leanh::LeanObject,
    mut v_toBind_387_: *mut leanh::LeanObject,
    mut v___f_388_: *mut leanh::LeanObject,
    mut v_x_x3f_389_: *mut leanh::LeanObject,
    mut v___f_390_: *mut leanh::LeanObject,
    mut v_s_391_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_throw_392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tryCatch_393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_398_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_throw_392_ = leanh::lean_ctor_get(v_inst_384_, 0);
    leanh::lean_inc(v_throw_392_);
    v_tryCatch_393_ = leanh::lean_ctor_get(v_inst_384_, 1);
    leanh::lean_inc(v_tryCatch_393_);
    leanh::lean_dec_ref(v_inst_384_);
    leanh::lean_inc_n(v_toBind_387_, 3);
    leanh::lean_inc(v_s_391_);
    leanh::lean_inc(v_restoreState_386_);
    v___f_394_ = leanh::lean_alloc_closure(
        l_Lean_commitWhenSome_x3f___redArg___lam__3 as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_394_, 0, v_toPure_385_);
    leanh::lean_closure_set(v___f_394_, 1, v_restoreState_386_);
    leanh::lean_closure_set(v___f_394_, 2, v_s_391_);
    leanh::lean_closure_set(v___f_394_, 3, v_toBind_387_);
    v___f_395_ = leanh::lean_alloc_closure(
        l_Lean_commitWhenSome_x3f___redArg___lam__5 as *mut core::ffi::c_void,
        6,
        5,
    );
    leanh::lean_closure_set(v___f_395_, 0, v_throw_392_);
    leanh::lean_closure_set(v___f_395_, 1, v_toBind_387_);
    leanh::lean_closure_set(v___f_395_, 2, v___f_388_);
    leanh::lean_closure_set(v___f_395_, 3, v_restoreState_386_);
    leanh::lean_closure_set(v___f_395_, 4, v_s_391_);
    v___x_396_ = leanh::lean_apply_4(
        v_toBind_387_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_x_x3f_389_,
        v___f_394_,
    );
    v___x_397_ = leanh::lean_apply_3(
        v_tryCatch_393_,
        leanh::lean_box(0),
        v___x_396_,
        v___f_395_,
    );
    v___x_398_ = leanh::lean_apply_4(
        v_toBind_387_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_397_,
        v___f_390_,
    );
    return v___x_398_;
}
pub unsafe fn l_Lean_commitWhenSome_x3f___redArg(
    mut v_inst_399_: *mut leanh::LeanObject,
    mut v_inst_400_: *mut leanh::LeanObject,
    mut v_inst_401_: *mut leanh::LeanObject,
    mut v_x_x3f_402_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_saveState_405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_restoreState_406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_411_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_403_ = leanh::lean_ctor_get(v_inst_399_, 0);
    leanh::lean_inc_ref(v_toApplicative_403_);
    v_toBind_404_ = leanh::lean_ctor_get(v_inst_399_, 1);
    leanh::lean_inc_n(v_toBind_404_, 2);
    leanh::lean_dec_ref(v_inst_399_);
    v_saveState_405_ = leanh::lean_ctor_get(v_inst_400_, 0);
    leanh::lean_inc(v_saveState_405_);
    v_restoreState_406_ = leanh::lean_ctor_get(v_inst_400_, 1);
    leanh::lean_inc(v_restoreState_406_);
    leanh::lean_dec_ref(v_inst_400_);
    v_toPure_407_ = leanh::lean_ctor_get(v_toApplicative_403_, 1);
    leanh::lean_inc_n(v_toPure_407_, 3);
    leanh::lean_dec_ref(v_toApplicative_403_);
    v___f_408_ = leanh::lean_alloc_closure(
        l_Lean_commitWhenSome_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_408_, 0, v_toPure_407_);
    v___f_409_ = leanh::lean_alloc_closure(
        l_Lean_commitWhenSome_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_409_, 0, v_toPure_407_);
    v___f_410_ = leanh::lean_alloc_closure(
        l_Lean_commitWhenSome_x3f___redArg___lam__6 as *mut core::ffi::c_void,
        8,
        7,
    );
    leanh::lean_closure_set(v___f_410_, 0, v_inst_401_);
    leanh::lean_closure_set(v___f_410_, 1, v_toPure_407_);
    leanh::lean_closure_set(v___f_410_, 2, v_restoreState_406_);
    leanh::lean_closure_set(v___f_410_, 3, v_toBind_404_);
    leanh::lean_closure_set(v___f_410_, 4, v___f_408_);
    leanh::lean_closure_set(v___f_410_, 5, v_x_x3f_402_);
    leanh::lean_closure_set(v___f_410_, 6, v___f_409_);
    v___x_411_ = leanh::lean_apply_4(
        v_toBind_404_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_saveState_405_,
        v___f_410_,
    );
    return v___x_411_;
}
pub unsafe fn l_Lean_commitWhenSome_x3f(
    mut v_m_412_: *mut leanh::LeanObject,
    mut v_s_413_: *mut leanh::LeanObject,
    mut v_00_u03b5_414_: *mut leanh::LeanObject,
    mut v_00_u03b1_415_: *mut leanh::LeanObject,
    mut v_inst_416_: *mut leanh::LeanObject,
    mut v_inst_417_: *mut leanh::LeanObject,
    mut v_inst_418_: *mut leanh::LeanObject,
    mut v_x_x3f_419_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_420_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_420_ =
        l_Lean_commitWhenSome_x3f___redArg(v_inst_416_, v_inst_417_, v_inst_418_, v_x_x3f_419_);
    return v___x_420_;
}
pub unsafe fn l_Lean_commitWhenSomeNoEx_x3f___redArg___lam__1(
    mut v_toPure_423_: *mut leanh::LeanObject,
    mut v_x_424_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_426_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_425_ = l_Lean_commitWhenSomeNoEx_x3f___redArg___lam__1___closed__0;
    v___x_426_ = leanh::lean_apply_2(v_toPure_423_, leanh::lean_box(0), v___x_425_);
    return v___x_426_;
}
pub unsafe fn l_Lean_commitWhenSomeNoEx_x3f___redArg___lam__1___boxed(
    mut v_toPure_427_: *mut leanh::LeanObject,
    mut v_x_428_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_429_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_429_ = l_Lean_commitWhenSomeNoEx_x3f___redArg___lam__1(v_toPure_427_, v_x_428_);
    leanh::lean_dec(v_x_428_);
    return v_res_429_;
}
pub unsafe fn l_Lean_commitWhenSomeNoEx_x3f___redArg(
    mut v_inst_430_: *mut leanh::LeanObject,
    mut v_inst_431_: *mut leanh::LeanObject,
    mut v_inst_432_: *mut leanh::LeanObject,
    mut v_x_x3f_433_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tryCatch_436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_444_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_434_ = leanh::lean_ctor_get(v_inst_430_, 0);
    v_toBind_435_ = leanh::lean_ctor_get(v_inst_430_, 1);
    leanh::lean_inc_n(v_toBind_435_, 2);
    v_tryCatch_436_ = leanh::lean_ctor_get(v_inst_432_, 1);
    leanh::lean_inc(v_tryCatch_436_);
    v_toPure_437_ = leanh::lean_ctor_get(v_toApplicative_434_, 1);
    leanh::lean_inc_n(v_toPure_437_, 3);
    v___f_438_ = leanh::lean_alloc_closure(
        l_Lean_commitWhenSome_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_438_, 0, v_toPure_437_);
    v___f_439_ = leanh::lean_alloc_closure(
        l_Lean_commitWhenSomeNoEx_x3f___redArg___lam__1___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_439_, 0, v_toPure_437_);
    v___x_440_ =
        l_Lean_commitWhenSome_x3f___redArg(v_inst_430_, v_inst_431_, v_inst_432_, v_x_x3f_433_);
    v___f_441_ = leanh::lean_alloc_closure(
        l_Lean_commitWhenSome_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_441_, 0, v_toPure_437_);
    v___x_442_ = leanh::lean_apply_4(
        v_toBind_435_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_440_,
        v___f_438_,
    );
    v___x_443_ = leanh::lean_apply_3(
        v_tryCatch_436_,
        leanh::lean_box(0),
        v___x_442_,
        v___f_439_,
    );
    v___x_444_ = leanh::lean_apply_4(
        v_toBind_435_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_443_,
        v___f_441_,
    );
    return v___x_444_;
}
pub unsafe fn l_Lean_commitWhenSomeNoEx_x3f(
    mut v_m_445_: *mut leanh::LeanObject,
    mut v_s_446_: *mut leanh::LeanObject,
    mut v_00_u03b5_447_: *mut leanh::LeanObject,
    mut v_00_u03b1_448_: *mut leanh::LeanObject,
    mut v_inst_449_: *mut leanh::LeanObject,
    mut v_inst_450_: *mut leanh::LeanObject,
    mut v_inst_451_: *mut leanh::LeanObject,
    mut v_x_x3f_452_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_453_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_453_ =
        l_Lean_commitWhenSomeNoEx_x3f___redArg(v_inst_449_, v_inst_450_, v_inst_451_, v_x_x3f_452_);
    return v___x_453_;
}
pub unsafe fn l_Lean_commitWhen___redArg___lam__0(
    mut v_toPure_454_: *mut leanh::LeanObject,
    mut v_____do__lift_455_: u8,
    mut v_____r_456_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_458_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_457_ = leanh::lean_box((v_____do__lift_455_) as usize);
    v___x_458_ = leanh::lean_apply_2(v_toPure_454_, leanh::lean_box(0), v___x_457_);
    return v___x_458_;
}
pub unsafe fn l_Lean_commitWhen___redArg___lam__0___boxed(
    mut v_toPure_459_: *mut leanh::LeanObject,
    mut v_____do__lift_460_: *mut leanh::LeanObject,
    mut v_____r_461_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_____do__lift_82__boxed_462_: u8 = 0;
    let mut v_res_463_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_82__boxed_462_ = (leanh::lean_unbox(v_____do__lift_460_) as u8);
    v_res_463_ = l_Lean_commitWhen___redArg___lam__0(
        v_toPure_459_,
        v_____do__lift_82__boxed_462_,
        v_____r_461_,
    );
    return v_res_463_;
}
pub unsafe fn l_Lean_commitWhen___redArg___lam__1(
    mut v_toPure_464_: *mut leanh::LeanObject,
    mut v_restoreState_465_: *mut leanh::LeanObject,
    mut v_s_466_: *mut leanh::LeanObject,
    mut v_toBind_467_: *mut leanh::LeanObject,
    mut v_____do__lift_468_: u8,
) -> *mut leanh::LeanObject {
    if v_____do__lift_468_ == 0 {
        let mut v___x_469_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_470_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_471_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_472_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_469_ = leanh::lean_box((v_____do__lift_468_) as usize);
        v___f_470_ = leanh::lean_alloc_closure(
            l_Lean_commitWhen___redArg___lam__0___boxed as *mut core::ffi::c_void,
            3,
            2,
        );
        leanh::lean_closure_set(v___f_470_, 0, v_toPure_464_);
        leanh::lean_closure_set(v___f_470_, 1, v___x_469_);
        v___x_471_ = leanh::lean_apply_1(v_restoreState_465_, v_s_466_);
        v___x_472_ = leanh::lean_apply_4(
            v_toBind_467_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_471_,
            v___f_470_,
        );
        return v___x_472_;
    } else {
        let mut v___x_473_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_474_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_toBind_467_);
        leanh::lean_dec(v_s_466_);
        leanh::lean_dec(v_restoreState_465_);
        v___x_473_ = leanh::lean_box((v_____do__lift_468_) as usize);
        v___x_474_ =
            leanh::lean_apply_2(v_toPure_464_, leanh::lean_box(0), v___x_473_);
        return v___x_474_;
    }
}
pub unsafe fn l_Lean_commitWhen___redArg___lam__1___boxed(
    mut v_toPure_475_: *mut leanh::LeanObject,
    mut v_restoreState_476_: *mut leanh::LeanObject,
    mut v_s_477_: *mut leanh::LeanObject,
    mut v_toBind_478_: *mut leanh::LeanObject,
    mut v_____do__lift_479_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_____do__lift_92__boxed_480_: u8 = 0;
    let mut v_res_481_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_92__boxed_480_ = (leanh::lean_unbox(v_____do__lift_479_) as u8);
    v_res_481_ = l_Lean_commitWhen___redArg___lam__1(
        v_toPure_475_,
        v_restoreState_476_,
        v_s_477_,
        v_toBind_478_,
        v_____do__lift_92__boxed_480_,
    );
    return v_res_481_;
}
pub unsafe fn l_Lean_commitWhen___redArg___lam__2(
    mut v_throw_482_: *mut leanh::LeanObject,
    mut v_ex_483_: *mut leanh::LeanObject,
    mut v_____r_484_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_485_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_485_ = leanh::lean_apply_2(v_throw_482_, leanh::lean_box(0), v_ex_483_);
    return v___x_485_;
}
pub unsafe fn l_Lean_commitWhen___redArg___lam__3(
    mut v_throw_486_: *mut leanh::LeanObject,
    mut v_restoreState_487_: *mut leanh::LeanObject,
    mut v_s_488_: *mut leanh::LeanObject,
    mut v_toBind_489_: *mut leanh::LeanObject,
    mut v_ex_490_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_493_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_491_ = leanh::lean_alloc_closure(
        l_Lean_commitWhen___redArg___lam__2 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_491_, 0, v_throw_486_);
    leanh::lean_closure_set(v___f_491_, 1, v_ex_490_);
    v___x_492_ = leanh::lean_apply_1(v_restoreState_487_, v_s_488_);
    v___x_493_ = leanh::lean_apply_4(
        v_toBind_489_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_492_,
        v___f_491_,
    );
    return v___x_493_;
}
pub unsafe fn l_Lean_commitWhen___redArg___lam__4(
    mut v_inst_494_: *mut leanh::LeanObject,
    mut v_toPure_495_: *mut leanh::LeanObject,
    mut v_restoreState_496_: *mut leanh::LeanObject,
    mut v_toBind_497_: *mut leanh::LeanObject,
    mut v_x_498_: *mut leanh::LeanObject,
    mut v_s_499_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_throw_500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tryCatch_501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_505_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_throw_500_ = leanh::lean_ctor_get(v_inst_494_, 0);
    leanh::lean_inc(v_throw_500_);
    v_tryCatch_501_ = leanh::lean_ctor_get(v_inst_494_, 1);
    leanh::lean_inc(v_tryCatch_501_);
    leanh::lean_dec_ref(v_inst_494_);
    leanh::lean_inc_n(v_toBind_497_, 2);
    leanh::lean_inc(v_s_499_);
    leanh::lean_inc(v_restoreState_496_);
    v___f_502_ = leanh::lean_alloc_closure(
        l_Lean_commitWhen___redArg___lam__1___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_502_, 0, v_toPure_495_);
    leanh::lean_closure_set(v___f_502_, 1, v_restoreState_496_);
    leanh::lean_closure_set(v___f_502_, 2, v_s_499_);
    leanh::lean_closure_set(v___f_502_, 3, v_toBind_497_);
    v___f_503_ = leanh::lean_alloc_closure(
        l_Lean_commitWhen___redArg___lam__3 as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_503_, 0, v_throw_500_);
    leanh::lean_closure_set(v___f_503_, 1, v_restoreState_496_);
    leanh::lean_closure_set(v___f_503_, 2, v_s_499_);
    leanh::lean_closure_set(v___f_503_, 3, v_toBind_497_);
    v___x_504_ = leanh::lean_apply_4(
        v_toBind_497_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_x_498_,
        v___f_502_,
    );
    v___x_505_ = leanh::lean_apply_3(
        v_tryCatch_501_,
        leanh::lean_box(0),
        v___x_504_,
        v___f_503_,
    );
    return v___x_505_;
}
pub unsafe fn l_Lean_commitWhen___redArg(
    mut v_inst_506_: *mut leanh::LeanObject,
    mut v_inst_507_: *mut leanh::LeanObject,
    mut v_inst_508_: *mut leanh::LeanObject,
    mut v_x_509_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_saveState_512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_restoreState_513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_516_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_510_ = leanh::lean_ctor_get(v_inst_506_, 0);
    leanh::lean_inc_ref(v_toApplicative_510_);
    v_toBind_511_ = leanh::lean_ctor_get(v_inst_506_, 1);
    leanh::lean_inc_n(v_toBind_511_, 2);
    leanh::lean_dec_ref(v_inst_506_);
    v_saveState_512_ = leanh::lean_ctor_get(v_inst_507_, 0);
    leanh::lean_inc(v_saveState_512_);
    v_restoreState_513_ = leanh::lean_ctor_get(v_inst_507_, 1);
    leanh::lean_inc(v_restoreState_513_);
    leanh::lean_dec_ref(v_inst_507_);
    v_toPure_514_ = leanh::lean_ctor_get(v_toApplicative_510_, 1);
    leanh::lean_inc(v_toPure_514_);
    leanh::lean_dec_ref(v_toApplicative_510_);
    v___f_515_ = leanh::lean_alloc_closure(
        l_Lean_commitWhen___redArg___lam__4 as *mut core::ffi::c_void,
        6,
        5,
    );
    leanh::lean_closure_set(v___f_515_, 0, v_inst_508_);
    leanh::lean_closure_set(v___f_515_, 1, v_toPure_514_);
    leanh::lean_closure_set(v___f_515_, 2, v_restoreState_513_);
    leanh::lean_closure_set(v___f_515_, 3, v_toBind_511_);
    leanh::lean_closure_set(v___f_515_, 4, v_x_509_);
    v___x_516_ = leanh::lean_apply_4(
        v_toBind_511_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_saveState_512_,
        v___f_515_,
    );
    return v___x_516_;
}
pub unsafe fn l_Lean_commitWhen(
    mut v_m_517_: *mut leanh::LeanObject,
    mut v_s_518_: *mut leanh::LeanObject,
    mut v_00_u03b5_519_: *mut leanh::LeanObject,
    mut v_inst_520_: *mut leanh::LeanObject,
    mut v_inst_521_: *mut leanh::LeanObject,
    mut v_inst_522_: *mut leanh::LeanObject,
    mut v_x_523_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_524_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_524_ = l_Lean_commitWhen___redArg(v_inst_520_, v_inst_521_, v_inst_522_, v_x_523_);
    return v___x_524_;
}
pub unsafe fn l_Lean_commitIfNoEx___redArg___lam__2(
    mut v_inst_525_: *mut leanh::LeanObject,
    mut v_restoreState_526_: *mut leanh::LeanObject,
    mut v_toBind_527_: *mut leanh::LeanObject,
    mut v_x_528_: *mut leanh::LeanObject,
    mut v_s_529_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_throw_530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tryCatch_531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_533_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_throw_530_ = leanh::lean_ctor_get(v_inst_525_, 0);
    leanh::lean_inc(v_throw_530_);
    v_tryCatch_531_ = leanh::lean_ctor_get(v_inst_525_, 1);
    leanh::lean_inc(v_tryCatch_531_);
    leanh::lean_dec_ref(v_inst_525_);
    v___f_532_ = leanh::lean_alloc_closure(
        l_Lean_commitWhen___redArg___lam__3 as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_532_, 0, v_throw_530_);
    leanh::lean_closure_set(v___f_532_, 1, v_restoreState_526_);
    leanh::lean_closure_set(v___f_532_, 2, v_s_529_);
    leanh::lean_closure_set(v___f_532_, 3, v_toBind_527_);
    v___x_533_ = leanh::lean_apply_3(
        v_tryCatch_531_,
        leanh::lean_box(0),
        v_x_528_,
        v___f_532_,
    );
    return v___x_533_;
}
pub unsafe fn l_Lean_commitIfNoEx___redArg(
    mut v_inst_534_: *mut leanh::LeanObject,
    mut v_inst_535_: *mut leanh::LeanObject,
    mut v_inst_536_: *mut leanh::LeanObject,
    mut v_x_537_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toBind_538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_saveState_539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_restoreState_540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_542_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toBind_538_ = leanh::lean_ctor_get(v_inst_534_, 1);
    leanh::lean_inc_n(v_toBind_538_, 2);
    leanh::lean_dec_ref(v_inst_534_);
    v_saveState_539_ = leanh::lean_ctor_get(v_inst_535_, 0);
    leanh::lean_inc(v_saveState_539_);
    v_restoreState_540_ = leanh::lean_ctor_get(v_inst_535_, 1);
    leanh::lean_inc(v_restoreState_540_);
    leanh::lean_dec_ref(v_inst_535_);
    v___f_541_ = leanh::lean_alloc_closure(
        l_Lean_commitIfNoEx___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_541_, 0, v_inst_536_);
    leanh::lean_closure_set(v___f_541_, 1, v_restoreState_540_);
    leanh::lean_closure_set(v___f_541_, 2, v_toBind_538_);
    leanh::lean_closure_set(v___f_541_, 3, v_x_537_);
    v___x_542_ = leanh::lean_apply_4(
        v_toBind_538_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_saveState_539_,
        v___f_541_,
    );
    return v___x_542_;
}
pub unsafe fn l_Lean_commitIfNoEx(
    mut v_m_543_: *mut leanh::LeanObject,
    mut v_s_544_: *mut leanh::LeanObject,
    mut v_00_u03b5_545_: *mut leanh::LeanObject,
    mut v_00_u03b1_546_: *mut leanh::LeanObject,
    mut v_inst_547_: *mut leanh::LeanObject,
    mut v_inst_548_: *mut leanh::LeanObject,
    mut v_inst_549_: *mut leanh::LeanObject,
    mut v_x_550_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_551_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_551_ = l_Lean_commitIfNoEx___redArg(v_inst_547_, v_inst_548_, v_inst_549_, v_x_550_);
    return v___x_551_;
}
pub unsafe fn l_Lean_withoutModifyingState___redArg___lam__0(
    mut v_x_552_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_553_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_553_ = leanh::lean_ctor_get(v_x_552_, 0);
    leanh::lean_inc(v_fst_553_);
    return v_fst_553_;
}
pub unsafe fn l_Lean_withoutModifyingState___redArg___lam__0___boxed(
    mut v_x_554_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_555_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_555_ = l_Lean_withoutModifyingState___redArg___lam__0(v_x_554_);
    leanh::lean_dec_ref(v_x_554_);
    return v_res_555_;
}
pub unsafe fn l_Lean_withoutModifyingState___redArg___lam__1(
    mut v___x_556_: *mut leanh::LeanObject,
    mut v_x_557_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v___x_556_);
    return v___x_556_;
}
pub unsafe fn l_Lean_withoutModifyingState___redArg___lam__1___boxed(
    mut v___x_558_: *mut leanh::LeanObject,
    mut v_x_559_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_560_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_560_ = l_Lean_withoutModifyingState___redArg___lam__1(v___x_558_, v_x_559_);
    leanh::lean_dec(v_x_559_);
    leanh::lean_dec(v___x_558_);
    return v_res_560_;
}
pub unsafe fn l_Lean_withoutModifyingState___redArg___lam__2(
    mut v_toFunctor_561_: *mut leanh::LeanObject,
    mut v_restoreState_562_: *mut leanh::LeanObject,
    mut v_inst_563_: *mut leanh::LeanObject,
    mut v_x_564_: *mut leanh::LeanObject,
    mut v___f_565_: *mut leanh::LeanObject,
    mut v_s_566_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_map_567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_571_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_map_567_ = leanh::lean_ctor_get(v_toFunctor_561_, 0);
    leanh::lean_inc(v_map_567_);
    leanh::lean_dec_ref(v_toFunctor_561_);
    v___x_568_ = leanh::lean_apply_1(v_restoreState_562_, v_s_566_);
    v___f_569_ = leanh::lean_alloc_closure(
        l_Lean_withoutModifyingState___redArg___lam__1___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_569_, 0, v___x_568_);
    v_y_570_ = leanh::lean_apply_4(
        v_inst_563_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_x_564_,
        v___f_569_,
    );
    v___x_571_ = leanh::lean_apply_4(
        v_map_567_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_565_,
        v_y_570_,
    );
    return v___x_571_;
}
pub unsafe fn l_Lean_withoutModifyingState___redArg(
    mut v_inst_573_: *mut leanh::LeanObject,
    mut v_inst_574_: *mut leanh::LeanObject,
    mut v_inst_575_: *mut leanh::LeanObject,
    mut v_x_576_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_saveState_579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_restoreState_580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_584_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_577_ = leanh::lean_ctor_get(v_inst_573_, 0);
    leanh::lean_inc_ref(v_toApplicative_577_);
    v_toBind_578_ = leanh::lean_ctor_get(v_inst_573_, 1);
    leanh::lean_inc(v_toBind_578_);
    leanh::lean_dec_ref(v_inst_573_);
    v_saveState_579_ = leanh::lean_ctor_get(v_inst_575_, 0);
    leanh::lean_inc(v_saveState_579_);
    v_restoreState_580_ = leanh::lean_ctor_get(v_inst_575_, 1);
    leanh::lean_inc(v_restoreState_580_);
    leanh::lean_dec_ref(v_inst_575_);
    v_toFunctor_581_ = leanh::lean_ctor_get(v_toApplicative_577_, 0);
    leanh::lean_inc_ref(v_toFunctor_581_);
    leanh::lean_dec_ref(v_toApplicative_577_);
    v___f_582_ = l_Lean_withoutModifyingState___redArg___closed__0;
    v___f_583_ = leanh::lean_alloc_closure(
        l_Lean_withoutModifyingState___redArg___lam__2 as *mut core::ffi::c_void,
        6,
        5,
    );
    leanh::lean_closure_set(v___f_583_, 0, v_toFunctor_581_);
    leanh::lean_closure_set(v___f_583_, 1, v_restoreState_580_);
    leanh::lean_closure_set(v___f_583_, 2, v_inst_574_);
    leanh::lean_closure_set(v___f_583_, 3, v_x_576_);
    leanh::lean_closure_set(v___f_583_, 4, v___f_582_);
    v___x_584_ = leanh::lean_apply_4(
        v_toBind_578_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_saveState_579_,
        v___f_583_,
    );
    return v___x_584_;
}
pub unsafe fn l_Lean_withoutModifyingState(
    mut v_m_585_: *mut leanh::LeanObject,
    mut v_s_586_: *mut leanh::LeanObject,
    mut v_00_u03b1_587_: *mut leanh::LeanObject,
    mut v_inst_588_: *mut leanh::LeanObject,
    mut v_inst_589_: *mut leanh::LeanObject,
    mut v_inst_590_: *mut leanh::LeanObject,
    mut v_x_591_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_592_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_592_ =
        l_Lean_withoutModifyingState___redArg(v_inst_588_, v_inst_589_, v_inst_590_, v_x_591_);
    return v___x_592_;
}
pub unsafe fn l_Lean_observing_x3f___redArg___lam__0(
    mut v_toPure_593_: *mut leanh::LeanObject,
    mut v_____r_594_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_596_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_595_ = l_Lean_commitWhenSomeNoEx_x3f___redArg___lam__1___closed__0;
    v___x_596_ = leanh::lean_apply_2(v_toPure_593_, leanh::lean_box(0), v___x_595_);
    return v___x_596_;
}
pub unsafe fn l_Lean_observing_x3f___redArg___lam__3(
    mut v_toPure_597_: *mut leanh::LeanObject,
    mut v_a_598_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_600_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_599_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_599_, 0, v_a_598_);
    v___x_600_ = leanh::lean_apply_2(v_toPure_597_, leanh::lean_box(0), v___x_599_);
    return v___x_600_;
}
pub unsafe fn l_Lean_observing_x3f___redArg___lam__1(
    mut v_restoreState_601_: *mut leanh::LeanObject,
    mut v_s_602_: *mut leanh::LeanObject,
    mut v_toBind_603_: *mut leanh::LeanObject,
    mut v___f_604_: *mut leanh::LeanObject,
    mut v_x_605_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_607_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_606_ = leanh::lean_apply_1(v_restoreState_601_, v_s_602_);
    v___x_607_ = leanh::lean_apply_4(
        v_toBind_603_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_606_,
        v___f_604_,
    );
    return v___x_607_;
}
pub unsafe fn l_Lean_observing_x3f___redArg___lam__1___boxed(
    mut v_restoreState_608_: *mut leanh::LeanObject,
    mut v_s_609_: *mut leanh::LeanObject,
    mut v_toBind_610_: *mut leanh::LeanObject,
    mut v___f_611_: *mut leanh::LeanObject,
    mut v_x_612_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_613_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_613_ = l_Lean_observing_x3f___redArg___lam__1(
        v_restoreState_608_,
        v_s_609_,
        v_toBind_610_,
        v___f_611_,
        v_x_612_,
    );
    leanh::lean_dec(v_x_612_);
    return v_res_613_;
}
pub unsafe fn l_Lean_observing_x3f___redArg___lam__2(
    mut v_inst_614_: *mut leanh::LeanObject,
    mut v_restoreState_615_: *mut leanh::LeanObject,
    mut v_toBind_616_: *mut leanh::LeanObject,
    mut v___f_617_: *mut leanh::LeanObject,
    mut v_x_618_: *mut leanh::LeanObject,
    mut v___f_619_: *mut leanh::LeanObject,
    mut v___f_620_: *mut leanh::LeanObject,
    mut v___f_621_: *mut leanh::LeanObject,
    mut v_s_622_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_tryCatch_623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_628_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_tryCatch_623_ = leanh::lean_ctor_get(v_inst_614_, 1);
    leanh::lean_inc(v_tryCatch_623_);
    leanh::lean_dec_ref(v_inst_614_);
    leanh::lean_inc_n(v_toBind_616_, 3);
    v___f_624_ = leanh::lean_alloc_closure(
        l_Lean_observing_x3f___redArg___lam__1___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_624_, 0, v_restoreState_615_);
    leanh::lean_closure_set(v___f_624_, 1, v_s_622_);
    leanh::lean_closure_set(v___f_624_, 2, v_toBind_616_);
    leanh::lean_closure_set(v___f_624_, 3, v___f_617_);
    v___x_625_ = leanh::lean_apply_4(
        v_toBind_616_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_x_618_,
        v___f_619_,
    );
    v___x_626_ = leanh::lean_apply_4(
        v_toBind_616_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_625_,
        v___f_620_,
    );
    v___x_627_ = leanh::lean_apply_3(
        v_tryCatch_623_,
        leanh::lean_box(0),
        v___x_626_,
        v___f_624_,
    );
    v___x_628_ = leanh::lean_apply_4(
        v_toBind_616_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_627_,
        v___f_621_,
    );
    return v___x_628_;
}
pub unsafe fn l_Lean_observing_x3f___redArg(
    mut v_inst_629_: *mut leanh::LeanObject,
    mut v_inst_630_: *mut leanh::LeanObject,
    mut v_inst_631_: *mut leanh::LeanObject,
    mut v_x_632_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_saveState_635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_restoreState_636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_643_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_633_ = leanh::lean_ctor_get(v_inst_629_, 0);
    leanh::lean_inc_ref(v_toApplicative_633_);
    v_toBind_634_ = leanh::lean_ctor_get(v_inst_629_, 1);
    leanh::lean_inc_n(v_toBind_634_, 2);
    leanh::lean_dec_ref(v_inst_629_);
    v_saveState_635_ = leanh::lean_ctor_get(v_inst_630_, 0);
    leanh::lean_inc(v_saveState_635_);
    v_restoreState_636_ = leanh::lean_ctor_get(v_inst_630_, 1);
    leanh::lean_inc(v_restoreState_636_);
    leanh::lean_dec_ref(v_inst_630_);
    v_toPure_637_ = leanh::lean_ctor_get(v_toApplicative_633_, 1);
    leanh::lean_inc_n(v_toPure_637_, 4);
    leanh::lean_dec_ref(v_toApplicative_633_);
    v___f_638_ = leanh::lean_alloc_closure(
        l_Lean_observing_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_638_, 0, v_toPure_637_);
    v___f_639_ = leanh::lean_alloc_closure(
        l_Lean_commitWhenSome_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_639_, 0, v_toPure_637_);
    v___f_640_ = leanh::lean_alloc_closure(
        l_Lean_commitWhenSome_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_640_, 0, v_toPure_637_);
    v___f_641_ = leanh::lean_alloc_closure(
        l_Lean_observing_x3f___redArg___lam__3 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_641_, 0, v_toPure_637_);
    v___f_642_ = leanh::lean_alloc_closure(
        l_Lean_observing_x3f___redArg___lam__2 as *mut core::ffi::c_void,
        9,
        8,
    );
    leanh::lean_closure_set(v___f_642_, 0, v_inst_631_);
    leanh::lean_closure_set(v___f_642_, 1, v_restoreState_636_);
    leanh::lean_closure_set(v___f_642_, 2, v_toBind_634_);
    leanh::lean_closure_set(v___f_642_, 3, v___f_638_);
    leanh::lean_closure_set(v___f_642_, 4, v_x_632_);
    leanh::lean_closure_set(v___f_642_, 5, v___f_641_);
    leanh::lean_closure_set(v___f_642_, 6, v___f_639_);
    leanh::lean_closure_set(v___f_642_, 7, v___f_640_);
    v___x_643_ = leanh::lean_apply_4(
        v_toBind_634_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_saveState_635_,
        v___f_642_,
    );
    return v___x_643_;
}
pub unsafe fn l_Lean_observing_x3f(
    mut v_m_644_: *mut leanh::LeanObject,
    mut v_s_645_: *mut leanh::LeanObject,
    mut v_00_u03b5_646_: *mut leanh::LeanObject,
    mut v_00_u03b1_647_: *mut leanh::LeanObject,
    mut v_inst_648_: *mut leanh::LeanObject,
    mut v_inst_649_: *mut leanh::LeanObject,
    mut v_inst_650_: *mut leanh::LeanObject,
    mut v_x_651_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_652_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_652_ = l_Lean_observing_x3f___redArg(v_inst_648_, v_inst_649_, v_inst_650_, v_x_651_);
    return v___x_652_;
}
pub unsafe fn l_Lean_instMonadBacktrackExceptTOfMonad___redArg___lam__0(
    mut v_a_653_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_654_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_654_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_654_, 0, v_a_653_);
    return v___x_654_;
}
pub unsafe fn l_Lean_instMonadBacktrackExceptTOfMonad___redArg___lam__1(
    mut v_a_655_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_656_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_656_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_656_, 0, v_a_655_);
    return v___x_656_;
}
pub unsafe fn l_Lean_instMonadBacktrackExceptTOfMonad___redArg___lam__2(
    mut v_restoreState_657_: *mut leanh::LeanObject,
    mut v_map_658_: *mut leanh::LeanObject,
    mut v___f_659_: *mut leanh::LeanObject,
    mut v_s_660_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_662_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_661_ = leanh::lean_apply_1(v_restoreState_657_, v_s_660_);
    v___x_662_ = leanh::lean_apply_4(
        v_map_658_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_659_,
        v___x_661_,
    );
    return v___x_662_;
}
pub unsafe fn l_Lean_instMonadBacktrackExceptTOfMonad___redArg(
    mut v_inst_665_: *mut leanh::LeanObject,
    mut v_inst_666_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_saveState_669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_restoreState_670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_673_: u8 = 0;
    let mut v_map_674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_682_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_667_ = leanh::lean_ctor_get(v_inst_666_, 0);
                leanh::lean_inc_ref(v_toApplicative_667_);
                leanh::lean_dec_ref(v_inst_666_);
                v_toFunctor_668_ = leanh::lean_ctor_get(v_toApplicative_667_, 0);
                leanh::lean_inc_ref(v_toFunctor_668_);
                leanh::lean_dec_ref(v_toApplicative_667_);
                v_saveState_669_ = leanh::lean_ctor_get(v_inst_665_, 0);
                v_restoreState_670_ = leanh::lean_ctor_get(v_inst_665_, 1);
                v_isSharedCheck_682_ = (!leanh::lean_is_exclusive(v_inst_665_)) as u8;
                if v_isSharedCheck_682_ == 0 {
                    v___x_672_ = v_inst_665_;
                    v_isShared_673_ = v_isSharedCheck_682_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_restoreState_670_);
                    leanh::lean_inc(v_saveState_669_);
                    leanh::lean_dec(v_inst_665_);
                    v___x_672_ = leanh::lean_box(0);
                    v_isShared_673_ = v_isSharedCheck_682_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_map_674_ = leanh::lean_ctor_get(v_toFunctor_668_, 0);
                leanh::lean_inc_n(v_map_674_, 2);
                leanh::lean_dec_ref(v_toFunctor_668_);
                v___f_675_ = l_Lean_instMonadBacktrackExceptTOfMonad___redArg___closed__0;
                v___f_676_ = l_Lean_instMonadBacktrackExceptTOfMonad___redArg___closed__1;
                v___f_677_ = leanh::lean_alloc_closure(
                    l_Lean_instMonadBacktrackExceptTOfMonad___redArg___lam__2
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                leanh::lean_closure_set(v___f_677_, 0, v_restoreState_670_);
                leanh::lean_closure_set(v___f_677_, 1, v_map_674_);
                leanh::lean_closure_set(v___f_677_, 2, v___f_676_);
                v___x_678_ = leanh::lean_apply_4(
                    v_map_674_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___f_675_,
                    v_saveState_669_,
                );
                if v_isShared_673_ == 0 {
                    leanh::lean_ctor_set(v___x_672_, 1, v___f_677_);
                    leanh::lean_ctor_set(v___x_672_, 0, v___x_678_);
                    v___x_680_ = v___x_672_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_681_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_681_, 0, v___x_678_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_681_, 1, v___f_677_);
                    v___x_680_ = v_reuseFailAlloc_681_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_680_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instMonadBacktrackExceptTOfMonad(
    mut v_s_683_: *mut leanh::LeanObject,
    mut v_m_684_: *mut leanh::LeanObject,
    mut v_00_u03b5_685_: *mut leanh::LeanObject,
    mut v_inst_686_: *mut leanh::LeanObject,
    mut v_inst_687_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_688_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_688_ = l_Lean_instMonadBacktrackExceptTOfMonad___redArg(v_inst_686_, v_inst_687_);
    return v___x_688_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Util_MonadBacktrack(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Control_Except(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Control_Do(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Coe(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Util_MonadBacktrack(
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
pub unsafe fn initialize_Lean_Util_MonadBacktrack(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Control_Except(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Control_Do(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_Coe(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_MonadBacktrack(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Util_MonadBacktrack(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Util_MonadBacktrack(builtin);
}