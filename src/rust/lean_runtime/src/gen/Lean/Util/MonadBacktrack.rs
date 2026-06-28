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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get,
    lean_ctor_set, lean_dec, lean_dec_ref, lean_inc, lean_inc_n, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_tag, lean_unbox,
};
pub static l_Lean_commitWhenSomeNoEx_x3f___redArg___lam__1___closed__0_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Lean_commitWhenSomeNoEx_x3f___redArg___lam__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_commitWhenSomeNoEx_x3f___redArg___lam__1___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_withoutModifyingState___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_withoutModifyingState___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_withoutModifyingState___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_withoutModifyingState___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_instMonadBacktrackExceptTOfMonad___redArg___closed__0_value: LeanClosureObject<
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
    m_fun: l_Lean_instMonadBacktrackExceptTOfMonad___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instMonadBacktrackExceptTOfMonad___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instMonadBacktrackExceptTOfMonad___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_instMonadBacktrackExceptTOfMonad___redArg___closed__1_value: LeanClosureObject<
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
    m_fun: l_Lean_instMonadBacktrackExceptTOfMonad___redArg___lam__1 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instMonadBacktrackExceptTOfMonad___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instMonadBacktrackExceptTOfMonad___redArg___closed__1_value)
        as *mut LeanObject;
pub unsafe fn l_Lean_commitWhenSome_x3f___redArg___lam__0(
    mut v_toPure_345_: *mut LeanObject,
    mut v_r_346_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_348_: *mut LeanObject = core::ptr::null_mut();
    v___x_347_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_347_, 0, v_r_346_);
    v___x_348_ = lean_apply_2(v_toPure_345_, lean_box(0), v___x_347_);
    return v___x_348_;
}
pub unsafe fn l_Lean_commitWhenSome_x3f___redArg___lam__1(
    mut v_toPure_349_: *mut LeanObject,
    mut v_e_350_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_352_: *mut LeanObject = core::ptr::null_mut();
    v_a_351_ = lean_ctor_get(v_e_350_, 0);
    lean_inc(v_a_351_);
    lean_dec_ref(v_e_350_);
    v___x_352_ = lean_apply_2(v_toPure_349_, lean_box(0), v_a_351_);
    return v___x_352_;
}
pub unsafe fn l_Lean_commitWhenSome_x3f___redArg___lam__2(
    mut v_____do__lift_353_: *mut LeanObject,
    mut v_toPure_354_: *mut LeanObject,
    mut v_____r_355_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_357_: *mut LeanObject = core::ptr::null_mut();
    v___x_356_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_356_, 0, v_____do__lift_353_);
    v___x_357_ = lean_apply_2(v_toPure_354_, lean_box(0), v___x_356_);
    return v___x_357_;
}
pub unsafe fn l_Lean_commitWhenSome_x3f___redArg___lam__3(
    mut v_toPure_358_: *mut LeanObject,
    mut v_restoreState_359_: *mut LeanObject,
    mut v_s_360_: *mut LeanObject,
    mut v_toBind_361_: *mut LeanObject,
    mut v_____do__lift_362_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_362_) == 0 {
        let mut v___f_363_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_364_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_365_: *mut LeanObject = core::ptr::null_mut();
        v___f_363_ = lean_alloc_closure(
            l_Lean_commitWhenSome_x3f___redArg___lam__2 as *mut core::ffi::c_void,
            3,
            2,
        );
        lean_closure_set(v___f_363_, 0, v_____do__lift_362_);
        lean_closure_set(v___f_363_, 1, v_toPure_358_);
        v___x_364_ = lean_apply_1(v_restoreState_359_, v_s_360_);
        v___x_365_ = lean_apply_4(
            v_toBind_361_,
            lean_box(0),
            lean_box(0),
            v___x_364_,
            v___f_363_,
        );
        return v___x_365_;
    } else {
        let mut v___x_366_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_367_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toBind_361_);
        lean_dec(v_s_360_);
        lean_dec(v_restoreState_359_);
        v___x_366_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_366_, 0, v_____do__lift_362_);
        v___x_367_ = lean_apply_2(v_toPure_358_, lean_box(0), v___x_366_);
        return v___x_367_;
    }
}
pub unsafe fn l_Lean_commitWhenSome_x3f___redArg___lam__4(
    mut v_throw_368_: *mut LeanObject,
    mut v_ex_369_: *mut LeanObject,
    mut v_toBind_370_: *mut LeanObject,
    mut v___f_371_: *mut LeanObject,
    mut v_____r_372_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_374_: *mut LeanObject = core::ptr::null_mut();
    v___x_373_ = lean_apply_2(v_throw_368_, lean_box(0), v_ex_369_);
    v___x_374_ = lean_apply_4(
        v_toBind_370_,
        lean_box(0),
        lean_box(0),
        v___x_373_,
        v___f_371_,
    );
    return v___x_374_;
}
pub unsafe fn l_Lean_commitWhenSome_x3f___redArg___lam__5(
    mut v_throw_375_: *mut LeanObject,
    mut v_toBind_376_: *mut LeanObject,
    mut v___f_377_: *mut LeanObject,
    mut v_restoreState_378_: *mut LeanObject,
    mut v_s_379_: *mut LeanObject,
    mut v_ex_380_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_383_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_toBind_376_);
    v___f_381_ = lean_alloc_closure(
        l_Lean_commitWhenSome_x3f___redArg___lam__4 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_381_, 0, v_throw_375_);
    lean_closure_set(v___f_381_, 1, v_ex_380_);
    lean_closure_set(v___f_381_, 2, v_toBind_376_);
    lean_closure_set(v___f_381_, 3, v___f_377_);
    v___x_382_ = lean_apply_1(v_restoreState_378_, v_s_379_);
    v___x_383_ = lean_apply_4(
        v_toBind_376_,
        lean_box(0),
        lean_box(0),
        v___x_382_,
        v___f_381_,
    );
    return v___x_383_;
}
pub unsafe fn l_Lean_commitWhenSome_x3f___redArg___lam__6(
    mut v_inst_384_: *mut LeanObject,
    mut v_toPure_385_: *mut LeanObject,
    mut v_restoreState_386_: *mut LeanObject,
    mut v_toBind_387_: *mut LeanObject,
    mut v___f_388_: *mut LeanObject,
    mut v_x_x3f_389_: *mut LeanObject,
    mut v___f_390_: *mut LeanObject,
    mut v_s_391_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_throw_392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tryCatch_393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_398_: *mut LeanObject = core::ptr::null_mut();
    v_throw_392_ = lean_ctor_get(v_inst_384_, 0);
    lean_inc(v_throw_392_);
    v_tryCatch_393_ = lean_ctor_get(v_inst_384_, 1);
    lean_inc(v_tryCatch_393_);
    lean_dec_ref(v_inst_384_);
    lean_inc_n(v_toBind_387_, 3);
    lean_inc(v_s_391_);
    lean_inc(v_restoreState_386_);
    v___f_394_ = lean_alloc_closure(
        l_Lean_commitWhenSome_x3f___redArg___lam__3 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_394_, 0, v_toPure_385_);
    lean_closure_set(v___f_394_, 1, v_restoreState_386_);
    lean_closure_set(v___f_394_, 2, v_s_391_);
    lean_closure_set(v___f_394_, 3, v_toBind_387_);
    v___f_395_ = lean_alloc_closure(
        l_Lean_commitWhenSome_x3f___redArg___lam__5 as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_395_, 0, v_throw_392_);
    lean_closure_set(v___f_395_, 1, v_toBind_387_);
    lean_closure_set(v___f_395_, 2, v___f_388_);
    lean_closure_set(v___f_395_, 3, v_restoreState_386_);
    lean_closure_set(v___f_395_, 4, v_s_391_);
    v___x_396_ = lean_apply_4(
        v_toBind_387_,
        lean_box(0),
        lean_box(0),
        v_x_x3f_389_,
        v___f_394_,
    );
    v___x_397_ = lean_apply_3(v_tryCatch_393_, lean_box(0), v___x_396_, v___f_395_);
    v___x_398_ = lean_apply_4(
        v_toBind_387_,
        lean_box(0),
        lean_box(0),
        v___x_397_,
        v___f_390_,
    );
    return v___x_398_;
}
pub unsafe fn l_Lean_commitWhenSome_x3f___redArg(
    mut v_inst_399_: *mut LeanObject,
    mut v_inst_400_: *mut LeanObject,
    mut v_inst_401_: *mut LeanObject,
    mut v_x_x3f_402_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_saveState_405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_restoreState_406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_411_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_403_ = lean_ctor_get(v_inst_399_, 0);
    lean_inc_ref(v_toApplicative_403_);
    v_toBind_404_ = lean_ctor_get(v_inst_399_, 1);
    lean_inc_n(v_toBind_404_, 2);
    lean_dec_ref(v_inst_399_);
    v_saveState_405_ = lean_ctor_get(v_inst_400_, 0);
    lean_inc(v_saveState_405_);
    v_restoreState_406_ = lean_ctor_get(v_inst_400_, 1);
    lean_inc(v_restoreState_406_);
    lean_dec_ref(v_inst_400_);
    v_toPure_407_ = lean_ctor_get(v_toApplicative_403_, 1);
    lean_inc_n(v_toPure_407_, 3);
    lean_dec_ref(v_toApplicative_403_);
    v___f_408_ = lean_alloc_closure(
        l_Lean_commitWhenSome_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_408_, 0, v_toPure_407_);
    v___f_409_ = lean_alloc_closure(
        l_Lean_commitWhenSome_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_409_, 0, v_toPure_407_);
    v___f_410_ = lean_alloc_closure(
        l_Lean_commitWhenSome_x3f___redArg___lam__6 as *mut core::ffi::c_void,
        8,
        7,
    );
    lean_closure_set(v___f_410_, 0, v_inst_401_);
    lean_closure_set(v___f_410_, 1, v_toPure_407_);
    lean_closure_set(v___f_410_, 2, v_restoreState_406_);
    lean_closure_set(v___f_410_, 3, v_toBind_404_);
    lean_closure_set(v___f_410_, 4, v___f_408_);
    lean_closure_set(v___f_410_, 5, v_x_x3f_402_);
    lean_closure_set(v___f_410_, 6, v___f_409_);
    v___x_411_ = lean_apply_4(
        v_toBind_404_,
        lean_box(0),
        lean_box(0),
        v_saveState_405_,
        v___f_410_,
    );
    return v___x_411_;
}
pub unsafe fn l_Lean_commitWhenSome_x3f(
    mut v_m_412_: *mut LeanObject,
    mut v_s_413_: *mut LeanObject,
    mut v_00_u03b5_414_: *mut LeanObject,
    mut v_00_u03b1_415_: *mut LeanObject,
    mut v_inst_416_: *mut LeanObject,
    mut v_inst_417_: *mut LeanObject,
    mut v_inst_418_: *mut LeanObject,
    mut v_x_x3f_419_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_420_: *mut LeanObject = core::ptr::null_mut();
    v___x_420_ =
        l_Lean_commitWhenSome_x3f___redArg(v_inst_416_, v_inst_417_, v_inst_418_, v_x_x3f_419_);
    return v___x_420_;
}
pub unsafe fn l_Lean_commitWhenSomeNoEx_x3f___redArg___lam__1(
    mut v_toPure_423_: *mut LeanObject,
    mut v_x_424_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_426_: *mut LeanObject = core::ptr::null_mut();
    v___x_425_ = l_Lean_commitWhenSomeNoEx_x3f___redArg___lam__1___closed__0;
    v___x_426_ = lean_apply_2(v_toPure_423_, lean_box(0), v___x_425_);
    return v___x_426_;
}
pub unsafe fn l_Lean_commitWhenSomeNoEx_x3f___redArg___lam__1___boxed(
    mut v_toPure_427_: *mut LeanObject,
    mut v_x_428_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_429_: *mut LeanObject = core::ptr::null_mut();
    v_res_429_ = l_Lean_commitWhenSomeNoEx_x3f___redArg___lam__1(v_toPure_427_, v_x_428_);
    lean_dec(v_x_428_);
    return v_res_429_;
}
pub unsafe fn l_Lean_commitWhenSomeNoEx_x3f___redArg(
    mut v_inst_430_: *mut LeanObject,
    mut v_inst_431_: *mut LeanObject,
    mut v_inst_432_: *mut LeanObject,
    mut v_x_x3f_433_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tryCatch_436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_444_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_434_ = lean_ctor_get(v_inst_430_, 0);
    v_toBind_435_ = lean_ctor_get(v_inst_430_, 1);
    lean_inc_n(v_toBind_435_, 2);
    v_tryCatch_436_ = lean_ctor_get(v_inst_432_, 1);
    lean_inc(v_tryCatch_436_);
    v_toPure_437_ = lean_ctor_get(v_toApplicative_434_, 1);
    lean_inc_n(v_toPure_437_, 3);
    v___f_438_ = lean_alloc_closure(
        l_Lean_commitWhenSome_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_438_, 0, v_toPure_437_);
    v___f_439_ = lean_alloc_closure(
        l_Lean_commitWhenSomeNoEx_x3f___redArg___lam__1___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_439_, 0, v_toPure_437_);
    v___x_440_ =
        l_Lean_commitWhenSome_x3f___redArg(v_inst_430_, v_inst_431_, v_inst_432_, v_x_x3f_433_);
    v___f_441_ = lean_alloc_closure(
        l_Lean_commitWhenSome_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_441_, 0, v_toPure_437_);
    v___x_442_ = lean_apply_4(
        v_toBind_435_,
        lean_box(0),
        lean_box(0),
        v___x_440_,
        v___f_438_,
    );
    v___x_443_ = lean_apply_3(v_tryCatch_436_, lean_box(0), v___x_442_, v___f_439_);
    v___x_444_ = lean_apply_4(
        v_toBind_435_,
        lean_box(0),
        lean_box(0),
        v___x_443_,
        v___f_441_,
    );
    return v___x_444_;
}
pub unsafe fn l_Lean_commitWhenSomeNoEx_x3f(
    mut v_m_445_: *mut LeanObject,
    mut v_s_446_: *mut LeanObject,
    mut v_00_u03b5_447_: *mut LeanObject,
    mut v_00_u03b1_448_: *mut LeanObject,
    mut v_inst_449_: *mut LeanObject,
    mut v_inst_450_: *mut LeanObject,
    mut v_inst_451_: *mut LeanObject,
    mut v_x_x3f_452_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_453_: *mut LeanObject = core::ptr::null_mut();
    v___x_453_ =
        l_Lean_commitWhenSomeNoEx_x3f___redArg(v_inst_449_, v_inst_450_, v_inst_451_, v_x_x3f_452_);
    return v___x_453_;
}
pub unsafe fn l_Lean_commitWhen___redArg___lam__0(
    mut v_toPure_454_: *mut LeanObject,
    mut v_____do__lift_455_: u8,
    mut v_____r_456_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_458_: *mut LeanObject = core::ptr::null_mut();
    v___x_457_ = lean_box((v_____do__lift_455_) as usize);
    v___x_458_ = lean_apply_2(v_toPure_454_, lean_box(0), v___x_457_);
    return v___x_458_;
}
pub unsafe fn l_Lean_commitWhen___redArg___lam__0___boxed(
    mut v_toPure_459_: *mut LeanObject,
    mut v_____do__lift_460_: *mut LeanObject,
    mut v_____r_461_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____do__lift_82__boxed_462_: u8 = 0;
    let mut v_res_463_: *mut LeanObject = core::ptr::null_mut();
    v_____do__lift_82__boxed_462_ = (lean_unbox(v_____do__lift_460_) as u8);
    v_res_463_ = l_Lean_commitWhen___redArg___lam__0(
        v_toPure_459_,
        v_____do__lift_82__boxed_462_,
        v_____r_461_,
    );
    return v_res_463_;
}
pub unsafe fn l_Lean_commitWhen___redArg___lam__1(
    mut v_toPure_464_: *mut LeanObject,
    mut v_restoreState_465_: *mut LeanObject,
    mut v_s_466_: *mut LeanObject,
    mut v_toBind_467_: *mut LeanObject,
    mut v_____do__lift_468_: u8,
) -> *mut LeanObject {
    if v_____do__lift_468_ == 0 {
        let mut v___x_469_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_470_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_471_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_472_: *mut LeanObject = core::ptr::null_mut();
        v___x_469_ = lean_box((v_____do__lift_468_) as usize);
        v___f_470_ = lean_alloc_closure(
            l_Lean_commitWhen___redArg___lam__0___boxed as *mut core::ffi::c_void,
            3,
            2,
        );
        lean_closure_set(v___f_470_, 0, v_toPure_464_);
        lean_closure_set(v___f_470_, 1, v___x_469_);
        v___x_471_ = lean_apply_1(v_restoreState_465_, v_s_466_);
        v___x_472_ = lean_apply_4(
            v_toBind_467_,
            lean_box(0),
            lean_box(0),
            v___x_471_,
            v___f_470_,
        );
        return v___x_472_;
    } else {
        let mut v___x_473_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_474_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toBind_467_);
        lean_dec(v_s_466_);
        lean_dec(v_restoreState_465_);
        v___x_473_ = lean_box((v_____do__lift_468_) as usize);
        v___x_474_ = lean_apply_2(v_toPure_464_, lean_box(0), v___x_473_);
        return v___x_474_;
    }
}
pub unsafe fn l_Lean_commitWhen___redArg___lam__1___boxed(
    mut v_toPure_475_: *mut LeanObject,
    mut v_restoreState_476_: *mut LeanObject,
    mut v_s_477_: *mut LeanObject,
    mut v_toBind_478_: *mut LeanObject,
    mut v_____do__lift_479_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____do__lift_92__boxed_480_: u8 = 0;
    let mut v_res_481_: *mut LeanObject = core::ptr::null_mut();
    v_____do__lift_92__boxed_480_ = (lean_unbox(v_____do__lift_479_) as u8);
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
    mut v_throw_482_: *mut LeanObject,
    mut v_ex_483_: *mut LeanObject,
    mut v_____r_484_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_485_: *mut LeanObject = core::ptr::null_mut();
    v___x_485_ = lean_apply_2(v_throw_482_, lean_box(0), v_ex_483_);
    return v___x_485_;
}
pub unsafe fn l_Lean_commitWhen___redArg___lam__3(
    mut v_throw_486_: *mut LeanObject,
    mut v_restoreState_487_: *mut LeanObject,
    mut v_s_488_: *mut LeanObject,
    mut v_toBind_489_: *mut LeanObject,
    mut v_ex_490_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_493_: *mut LeanObject = core::ptr::null_mut();
    v___f_491_ = lean_alloc_closure(
        l_Lean_commitWhen___redArg___lam__2 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_491_, 0, v_throw_486_);
    lean_closure_set(v___f_491_, 1, v_ex_490_);
    v___x_492_ = lean_apply_1(v_restoreState_487_, v_s_488_);
    v___x_493_ = lean_apply_4(
        v_toBind_489_,
        lean_box(0),
        lean_box(0),
        v___x_492_,
        v___f_491_,
    );
    return v___x_493_;
}
pub unsafe fn l_Lean_commitWhen___redArg___lam__4(
    mut v_inst_494_: *mut LeanObject,
    mut v_toPure_495_: *mut LeanObject,
    mut v_restoreState_496_: *mut LeanObject,
    mut v_toBind_497_: *mut LeanObject,
    mut v_x_498_: *mut LeanObject,
    mut v_s_499_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_throw_500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tryCatch_501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_505_: *mut LeanObject = core::ptr::null_mut();
    v_throw_500_ = lean_ctor_get(v_inst_494_, 0);
    lean_inc(v_throw_500_);
    v_tryCatch_501_ = lean_ctor_get(v_inst_494_, 1);
    lean_inc(v_tryCatch_501_);
    lean_dec_ref(v_inst_494_);
    lean_inc_n(v_toBind_497_, 2);
    lean_inc(v_s_499_);
    lean_inc(v_restoreState_496_);
    v___f_502_ = lean_alloc_closure(
        l_Lean_commitWhen___redArg___lam__1___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_502_, 0, v_toPure_495_);
    lean_closure_set(v___f_502_, 1, v_restoreState_496_);
    lean_closure_set(v___f_502_, 2, v_s_499_);
    lean_closure_set(v___f_502_, 3, v_toBind_497_);
    v___f_503_ = lean_alloc_closure(
        l_Lean_commitWhen___redArg___lam__3 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_503_, 0, v_throw_500_);
    lean_closure_set(v___f_503_, 1, v_restoreState_496_);
    lean_closure_set(v___f_503_, 2, v_s_499_);
    lean_closure_set(v___f_503_, 3, v_toBind_497_);
    v___x_504_ = lean_apply_4(
        v_toBind_497_,
        lean_box(0),
        lean_box(0),
        v_x_498_,
        v___f_502_,
    );
    v___x_505_ = lean_apply_3(v_tryCatch_501_, lean_box(0), v___x_504_, v___f_503_);
    return v___x_505_;
}
pub unsafe fn l_Lean_commitWhen___redArg(
    mut v_inst_506_: *mut LeanObject,
    mut v_inst_507_: *mut LeanObject,
    mut v_inst_508_: *mut LeanObject,
    mut v_x_509_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_saveState_512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_restoreState_513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_516_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_510_ = lean_ctor_get(v_inst_506_, 0);
    lean_inc_ref(v_toApplicative_510_);
    v_toBind_511_ = lean_ctor_get(v_inst_506_, 1);
    lean_inc_n(v_toBind_511_, 2);
    lean_dec_ref(v_inst_506_);
    v_saveState_512_ = lean_ctor_get(v_inst_507_, 0);
    lean_inc(v_saveState_512_);
    v_restoreState_513_ = lean_ctor_get(v_inst_507_, 1);
    lean_inc(v_restoreState_513_);
    lean_dec_ref(v_inst_507_);
    v_toPure_514_ = lean_ctor_get(v_toApplicative_510_, 1);
    lean_inc(v_toPure_514_);
    lean_dec_ref(v_toApplicative_510_);
    v___f_515_ = lean_alloc_closure(
        l_Lean_commitWhen___redArg___lam__4 as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_515_, 0, v_inst_508_);
    lean_closure_set(v___f_515_, 1, v_toPure_514_);
    lean_closure_set(v___f_515_, 2, v_restoreState_513_);
    lean_closure_set(v___f_515_, 3, v_toBind_511_);
    lean_closure_set(v___f_515_, 4, v_x_509_);
    v___x_516_ = lean_apply_4(
        v_toBind_511_,
        lean_box(0),
        lean_box(0),
        v_saveState_512_,
        v___f_515_,
    );
    return v___x_516_;
}
pub unsafe fn l_Lean_commitWhen(
    mut v_m_517_: *mut LeanObject,
    mut v_s_518_: *mut LeanObject,
    mut v_00_u03b5_519_: *mut LeanObject,
    mut v_inst_520_: *mut LeanObject,
    mut v_inst_521_: *mut LeanObject,
    mut v_inst_522_: *mut LeanObject,
    mut v_x_523_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_524_: *mut LeanObject = core::ptr::null_mut();
    v___x_524_ = l_Lean_commitWhen___redArg(v_inst_520_, v_inst_521_, v_inst_522_, v_x_523_);
    return v___x_524_;
}
pub unsafe fn l_Lean_commitIfNoEx___redArg___lam__2(
    mut v_inst_525_: *mut LeanObject,
    mut v_restoreState_526_: *mut LeanObject,
    mut v_toBind_527_: *mut LeanObject,
    mut v_x_528_: *mut LeanObject,
    mut v_s_529_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_throw_530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tryCatch_531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_533_: *mut LeanObject = core::ptr::null_mut();
    v_throw_530_ = lean_ctor_get(v_inst_525_, 0);
    lean_inc(v_throw_530_);
    v_tryCatch_531_ = lean_ctor_get(v_inst_525_, 1);
    lean_inc(v_tryCatch_531_);
    lean_dec_ref(v_inst_525_);
    v___f_532_ = lean_alloc_closure(
        l_Lean_commitWhen___redArg___lam__3 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_532_, 0, v_throw_530_);
    lean_closure_set(v___f_532_, 1, v_restoreState_526_);
    lean_closure_set(v___f_532_, 2, v_s_529_);
    lean_closure_set(v___f_532_, 3, v_toBind_527_);
    v___x_533_ = lean_apply_3(v_tryCatch_531_, lean_box(0), v_x_528_, v___f_532_);
    return v___x_533_;
}
pub unsafe fn l_Lean_commitIfNoEx___redArg(
    mut v_inst_534_: *mut LeanObject,
    mut v_inst_535_: *mut LeanObject,
    mut v_inst_536_: *mut LeanObject,
    mut v_x_537_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_saveState_539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_restoreState_540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_542_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_538_ = lean_ctor_get(v_inst_534_, 1);
    lean_inc_n(v_toBind_538_, 2);
    lean_dec_ref(v_inst_534_);
    v_saveState_539_ = lean_ctor_get(v_inst_535_, 0);
    lean_inc(v_saveState_539_);
    v_restoreState_540_ = lean_ctor_get(v_inst_535_, 1);
    lean_inc(v_restoreState_540_);
    lean_dec_ref(v_inst_535_);
    v___f_541_ = lean_alloc_closure(
        l_Lean_commitIfNoEx___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_541_, 0, v_inst_536_);
    lean_closure_set(v___f_541_, 1, v_restoreState_540_);
    lean_closure_set(v___f_541_, 2, v_toBind_538_);
    lean_closure_set(v___f_541_, 3, v_x_537_);
    v___x_542_ = lean_apply_4(
        v_toBind_538_,
        lean_box(0),
        lean_box(0),
        v_saveState_539_,
        v___f_541_,
    );
    return v___x_542_;
}
pub unsafe fn l_Lean_commitIfNoEx(
    mut v_m_543_: *mut LeanObject,
    mut v_s_544_: *mut LeanObject,
    mut v_00_u03b5_545_: *mut LeanObject,
    mut v_00_u03b1_546_: *mut LeanObject,
    mut v_inst_547_: *mut LeanObject,
    mut v_inst_548_: *mut LeanObject,
    mut v_inst_549_: *mut LeanObject,
    mut v_x_550_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_551_: *mut LeanObject = core::ptr::null_mut();
    v___x_551_ = l_Lean_commitIfNoEx___redArg(v_inst_547_, v_inst_548_, v_inst_549_, v_x_550_);
    return v___x_551_;
}
pub unsafe fn l_Lean_withoutModifyingState___redArg___lam__0(
    mut v_x_552_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_553_: *mut LeanObject = core::ptr::null_mut();
    v_fst_553_ = lean_ctor_get(v_x_552_, 0);
    lean_inc(v_fst_553_);
    return v_fst_553_;
}
pub unsafe fn l_Lean_withoutModifyingState___redArg___lam__0___boxed(
    mut v_x_554_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_555_: *mut LeanObject = core::ptr::null_mut();
    v_res_555_ = l_Lean_withoutModifyingState___redArg___lam__0(v_x_554_);
    lean_dec_ref(v_x_554_);
    return v_res_555_;
}
pub unsafe fn l_Lean_withoutModifyingState___redArg___lam__1(
    mut v___x_556_: *mut LeanObject,
    mut v_x_557_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v___x_556_);
    return v___x_556_;
}
pub unsafe fn l_Lean_withoutModifyingState___redArg___lam__1___boxed(
    mut v___x_558_: *mut LeanObject,
    mut v_x_559_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_560_: *mut LeanObject = core::ptr::null_mut();
    v_res_560_ = l_Lean_withoutModifyingState___redArg___lam__1(v___x_558_, v_x_559_);
    lean_dec(v_x_559_);
    lean_dec(v___x_558_);
    return v_res_560_;
}
pub unsafe fn l_Lean_withoutModifyingState___redArg___lam__2(
    mut v_toFunctor_561_: *mut LeanObject,
    mut v_restoreState_562_: *mut LeanObject,
    mut v_inst_563_: *mut LeanObject,
    mut v_x_564_: *mut LeanObject,
    mut v___f_565_: *mut LeanObject,
    mut v_s_566_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_y_570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_571_: *mut LeanObject = core::ptr::null_mut();
    v_map_567_ = lean_ctor_get(v_toFunctor_561_, 0);
    lean_inc(v_map_567_);
    lean_dec_ref(v_toFunctor_561_);
    v___x_568_ = lean_apply_1(v_restoreState_562_, v_s_566_);
    v___f_569_ = lean_alloc_closure(
        l_Lean_withoutModifyingState___redArg___lam__1___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_569_, 0, v___x_568_);
    v_y_570_ = lean_apply_4(v_inst_563_, lean_box(0), lean_box(0), v_x_564_, v___f_569_);
    v___x_571_ = lean_apply_4(v_map_567_, lean_box(0), lean_box(0), v___f_565_, v_y_570_);
    return v___x_571_;
}
pub unsafe fn l_Lean_withoutModifyingState___redArg(
    mut v_inst_573_: *mut LeanObject,
    mut v_inst_574_: *mut LeanObject,
    mut v_inst_575_: *mut LeanObject,
    mut v_x_576_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_saveState_579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_restoreState_580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_584_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_577_ = lean_ctor_get(v_inst_573_, 0);
    lean_inc_ref(v_toApplicative_577_);
    v_toBind_578_ = lean_ctor_get(v_inst_573_, 1);
    lean_inc(v_toBind_578_);
    lean_dec_ref(v_inst_573_);
    v_saveState_579_ = lean_ctor_get(v_inst_575_, 0);
    lean_inc(v_saveState_579_);
    v_restoreState_580_ = lean_ctor_get(v_inst_575_, 1);
    lean_inc(v_restoreState_580_);
    lean_dec_ref(v_inst_575_);
    v_toFunctor_581_ = lean_ctor_get(v_toApplicative_577_, 0);
    lean_inc_ref(v_toFunctor_581_);
    lean_dec_ref(v_toApplicative_577_);
    v___f_582_ = l_Lean_withoutModifyingState___redArg___closed__0;
    v___f_583_ = lean_alloc_closure(
        l_Lean_withoutModifyingState___redArg___lam__2 as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_583_, 0, v_toFunctor_581_);
    lean_closure_set(v___f_583_, 1, v_restoreState_580_);
    lean_closure_set(v___f_583_, 2, v_inst_574_);
    lean_closure_set(v___f_583_, 3, v_x_576_);
    lean_closure_set(v___f_583_, 4, v___f_582_);
    v___x_584_ = lean_apply_4(
        v_toBind_578_,
        lean_box(0),
        lean_box(0),
        v_saveState_579_,
        v___f_583_,
    );
    return v___x_584_;
}
pub unsafe fn l_Lean_withoutModifyingState(
    mut v_m_585_: *mut LeanObject,
    mut v_s_586_: *mut LeanObject,
    mut v_00_u03b1_587_: *mut LeanObject,
    mut v_inst_588_: *mut LeanObject,
    mut v_inst_589_: *mut LeanObject,
    mut v_inst_590_: *mut LeanObject,
    mut v_x_591_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_592_: *mut LeanObject = core::ptr::null_mut();
    v___x_592_ =
        l_Lean_withoutModifyingState___redArg(v_inst_588_, v_inst_589_, v_inst_590_, v_x_591_);
    return v___x_592_;
}
pub unsafe fn l_Lean_observing_x3f___redArg___lam__0(
    mut v_toPure_593_: *mut LeanObject,
    mut v_____r_594_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_596_: *mut LeanObject = core::ptr::null_mut();
    v___x_595_ = l_Lean_commitWhenSomeNoEx_x3f___redArg___lam__1___closed__0;
    v___x_596_ = lean_apply_2(v_toPure_593_, lean_box(0), v___x_595_);
    return v___x_596_;
}
pub unsafe fn l_Lean_observing_x3f___redArg___lam__3(
    mut v_toPure_597_: *mut LeanObject,
    mut v_a_598_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_600_: *mut LeanObject = core::ptr::null_mut();
    v___x_599_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_599_, 0, v_a_598_);
    v___x_600_ = lean_apply_2(v_toPure_597_, lean_box(0), v___x_599_);
    return v___x_600_;
}
pub unsafe fn l_Lean_observing_x3f___redArg___lam__1(
    mut v_restoreState_601_: *mut LeanObject,
    mut v_s_602_: *mut LeanObject,
    mut v_toBind_603_: *mut LeanObject,
    mut v___f_604_: *mut LeanObject,
    mut v_x_605_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_607_: *mut LeanObject = core::ptr::null_mut();
    v___x_606_ = lean_apply_1(v_restoreState_601_, v_s_602_);
    v___x_607_ = lean_apply_4(
        v_toBind_603_,
        lean_box(0),
        lean_box(0),
        v___x_606_,
        v___f_604_,
    );
    return v___x_607_;
}
pub unsafe fn l_Lean_observing_x3f___redArg___lam__1___boxed(
    mut v_restoreState_608_: *mut LeanObject,
    mut v_s_609_: *mut LeanObject,
    mut v_toBind_610_: *mut LeanObject,
    mut v___f_611_: *mut LeanObject,
    mut v_x_612_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_613_: *mut LeanObject = core::ptr::null_mut();
    v_res_613_ = l_Lean_observing_x3f___redArg___lam__1(
        v_restoreState_608_,
        v_s_609_,
        v_toBind_610_,
        v___f_611_,
        v_x_612_,
    );
    lean_dec(v_x_612_);
    return v_res_613_;
}
pub unsafe fn l_Lean_observing_x3f___redArg___lam__2(
    mut v_inst_614_: *mut LeanObject,
    mut v_restoreState_615_: *mut LeanObject,
    mut v_toBind_616_: *mut LeanObject,
    mut v___f_617_: *mut LeanObject,
    mut v_x_618_: *mut LeanObject,
    mut v___f_619_: *mut LeanObject,
    mut v___f_620_: *mut LeanObject,
    mut v___f_621_: *mut LeanObject,
    mut v_s_622_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_tryCatch_623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_628_: *mut LeanObject = core::ptr::null_mut();
    v_tryCatch_623_ = lean_ctor_get(v_inst_614_, 1);
    lean_inc(v_tryCatch_623_);
    lean_dec_ref(v_inst_614_);
    lean_inc_n(v_toBind_616_, 3);
    v___f_624_ = lean_alloc_closure(
        l_Lean_observing_x3f___redArg___lam__1___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_624_, 0, v_restoreState_615_);
    lean_closure_set(v___f_624_, 1, v_s_622_);
    lean_closure_set(v___f_624_, 2, v_toBind_616_);
    lean_closure_set(v___f_624_, 3, v___f_617_);
    v___x_625_ = lean_apply_4(
        v_toBind_616_,
        lean_box(0),
        lean_box(0),
        v_x_618_,
        v___f_619_,
    );
    v___x_626_ = lean_apply_4(
        v_toBind_616_,
        lean_box(0),
        lean_box(0),
        v___x_625_,
        v___f_620_,
    );
    v___x_627_ = lean_apply_3(v_tryCatch_623_, lean_box(0), v___x_626_, v___f_624_);
    v___x_628_ = lean_apply_4(
        v_toBind_616_,
        lean_box(0),
        lean_box(0),
        v___x_627_,
        v___f_621_,
    );
    return v___x_628_;
}
pub unsafe fn l_Lean_observing_x3f___redArg(
    mut v_inst_629_: *mut LeanObject,
    mut v_inst_630_: *mut LeanObject,
    mut v_inst_631_: *mut LeanObject,
    mut v_x_632_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_saveState_635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_restoreState_636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_643_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_633_ = lean_ctor_get(v_inst_629_, 0);
    lean_inc_ref(v_toApplicative_633_);
    v_toBind_634_ = lean_ctor_get(v_inst_629_, 1);
    lean_inc_n(v_toBind_634_, 2);
    lean_dec_ref(v_inst_629_);
    v_saveState_635_ = lean_ctor_get(v_inst_630_, 0);
    lean_inc(v_saveState_635_);
    v_restoreState_636_ = lean_ctor_get(v_inst_630_, 1);
    lean_inc(v_restoreState_636_);
    lean_dec_ref(v_inst_630_);
    v_toPure_637_ = lean_ctor_get(v_toApplicative_633_, 1);
    lean_inc_n(v_toPure_637_, 4);
    lean_dec_ref(v_toApplicative_633_);
    v___f_638_ = lean_alloc_closure(
        l_Lean_observing_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_638_, 0, v_toPure_637_);
    v___f_639_ = lean_alloc_closure(
        l_Lean_commitWhenSome_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_639_, 0, v_toPure_637_);
    v___f_640_ = lean_alloc_closure(
        l_Lean_commitWhenSome_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_640_, 0, v_toPure_637_);
    v___f_641_ = lean_alloc_closure(
        l_Lean_observing_x3f___redArg___lam__3 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_641_, 0, v_toPure_637_);
    v___f_642_ = lean_alloc_closure(
        l_Lean_observing_x3f___redArg___lam__2 as *mut core::ffi::c_void,
        9,
        8,
    );
    lean_closure_set(v___f_642_, 0, v_inst_631_);
    lean_closure_set(v___f_642_, 1, v_restoreState_636_);
    lean_closure_set(v___f_642_, 2, v_toBind_634_);
    lean_closure_set(v___f_642_, 3, v___f_638_);
    lean_closure_set(v___f_642_, 4, v_x_632_);
    lean_closure_set(v___f_642_, 5, v___f_641_);
    lean_closure_set(v___f_642_, 6, v___f_639_);
    lean_closure_set(v___f_642_, 7, v___f_640_);
    v___x_643_ = lean_apply_4(
        v_toBind_634_,
        lean_box(0),
        lean_box(0),
        v_saveState_635_,
        v___f_642_,
    );
    return v___x_643_;
}
pub unsafe fn l_Lean_observing_x3f(
    mut v_m_644_: *mut LeanObject,
    mut v_s_645_: *mut LeanObject,
    mut v_00_u03b5_646_: *mut LeanObject,
    mut v_00_u03b1_647_: *mut LeanObject,
    mut v_inst_648_: *mut LeanObject,
    mut v_inst_649_: *mut LeanObject,
    mut v_inst_650_: *mut LeanObject,
    mut v_x_651_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_652_: *mut LeanObject = core::ptr::null_mut();
    v___x_652_ = l_Lean_observing_x3f___redArg(v_inst_648_, v_inst_649_, v_inst_650_, v_x_651_);
    return v___x_652_;
}
pub unsafe fn l_Lean_instMonadBacktrackExceptTOfMonad___redArg___lam__0(
    mut v_a_653_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_654_: *mut LeanObject = core::ptr::null_mut();
    v___x_654_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_654_, 0, v_a_653_);
    return v___x_654_;
}
pub unsafe fn l_Lean_instMonadBacktrackExceptTOfMonad___redArg___lam__1(
    mut v_a_655_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_656_: *mut LeanObject = core::ptr::null_mut();
    v___x_656_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_656_, 0, v_a_655_);
    return v___x_656_;
}
pub unsafe fn l_Lean_instMonadBacktrackExceptTOfMonad___redArg___lam__2(
    mut v_restoreState_657_: *mut LeanObject,
    mut v_map_658_: *mut LeanObject,
    mut v___f_659_: *mut LeanObject,
    mut v_s_660_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_662_: *mut LeanObject = core::ptr::null_mut();
    v___x_661_ = lean_apply_1(v_restoreState_657_, v_s_660_);
    v___x_662_ = lean_apply_4(v_map_658_, lean_box(0), lean_box(0), v___f_659_, v___x_661_);
    return v___x_662_;
}
pub unsafe fn l_Lean_instMonadBacktrackExceptTOfMonad___redArg(
    mut v_inst_665_: *mut LeanObject,
    mut v_inst_666_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_saveState_669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_restoreState_670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_673_: u8 = 0;
    let mut v_map_674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_682_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_667_ = lean_ctor_get(v_inst_666_, 0);
                lean_inc_ref(v_toApplicative_667_);
                lean_dec_ref(v_inst_666_);
                v_toFunctor_668_ = lean_ctor_get(v_toApplicative_667_, 0);
                lean_inc_ref(v_toFunctor_668_);
                lean_dec_ref(v_toApplicative_667_);
                v_saveState_669_ = lean_ctor_get(v_inst_665_, 0);
                v_restoreState_670_ = lean_ctor_get(v_inst_665_, 1);
                v_isSharedCheck_682_ = (!lean_is_exclusive(v_inst_665_)) as u8;
                if v_isSharedCheck_682_ == 0 {
                    v___x_672_ = v_inst_665_;
                    v_isShared_673_ = v_isSharedCheck_682_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_restoreState_670_);
                    lean_inc(v_saveState_669_);
                    lean_dec(v_inst_665_);
                    v___x_672_ = lean_box(0);
                    v_isShared_673_ = v_isSharedCheck_682_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_map_674_ = lean_ctor_get(v_toFunctor_668_, 0);
                lean_inc_n(v_map_674_, 2);
                lean_dec_ref(v_toFunctor_668_);
                v___f_675_ = l_Lean_instMonadBacktrackExceptTOfMonad___redArg___closed__0;
                v___f_676_ = l_Lean_instMonadBacktrackExceptTOfMonad___redArg___closed__1;
                v___f_677_ = lean_alloc_closure(
                    l_Lean_instMonadBacktrackExceptTOfMonad___redArg___lam__2
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                lean_closure_set(v___f_677_, 0, v_restoreState_670_);
                lean_closure_set(v___f_677_, 1, v_map_674_);
                lean_closure_set(v___f_677_, 2, v___f_676_);
                v___x_678_ = lean_apply_4(
                    v_map_674_,
                    lean_box(0),
                    lean_box(0),
                    v___f_675_,
                    v_saveState_669_,
                );
                if v_isShared_673_ == 0 {
                    lean_ctor_set(v___x_672_, 1, v___f_677_);
                    lean_ctor_set(v___x_672_, 0, v___x_678_);
                    v___x_680_ = v___x_672_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_681_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_681_, 0, v___x_678_);
                    lean_ctor_set(v_reuseFailAlloc_681_, 1, v___f_677_);
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
    mut v_s_683_: *mut LeanObject,
    mut v_m_684_: *mut LeanObject,
    mut v_00_u03b5_685_: *mut LeanObject,
    mut v_inst_686_: *mut LeanObject,
    mut v_inst_687_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_688_: *mut LeanObject = core::ptr::null_mut();
    v___x_688_ = l_Lean_instMonadBacktrackExceptTOfMonad___redArg(v_inst_686_, v_inst_687_);
    return v___x_688_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Util_MonadBacktrack(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Control_Except(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Control_Do(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Coe(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Util_MonadBacktrack(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Util_MonadBacktrack(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Control_Except(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Control_Do(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Option_Coe(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_MonadBacktrack(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Util_MonadBacktrack(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Util_MonadBacktrack(builtin);
}
