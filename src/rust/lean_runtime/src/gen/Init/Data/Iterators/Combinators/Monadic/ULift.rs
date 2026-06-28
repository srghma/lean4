// Lean compiler output
// Module: Init.Data.Iterators.Combinators.Monadic.ULift
// Imports: Init.Data.Iterators.Consumers.Monadic
use crate::r#gen::Init::Data::Iterators::Consumers::Monadic::{
    initialize_Init_Data_Iterators_Consumers_Monadic,
    runtime_initialize_Init_Data_Iterators_Consumers_Monadic,
};
use crate::r#gen::Init::Prelude::l_Function_comp;
use crate::r#gen::Init::WFExtrinsicFix::l_WellFounded_opaqueFix_u2083___redArg;
pub unsafe fn l_Std_Iterators_ULiftT_run___redArg(
    mut v_x_366_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_x_366_);
    return v_x_366_;
}
pub unsafe fn l_Std_Iterators_ULiftT_run___redArg___boxed(
    mut v_x_367_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_368_ = l_Std_Iterators_ULiftT_run___redArg(v_x_367_);
    crate::leanh::lean_dec(v_x_367_);
    return v_res_368_;
}
pub unsafe fn l_Std_Iterators_ULiftT_run(
    mut v_n_369_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_370_: *mut crate::leanh::LeanObject,
    mut v_x_371_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_x_371_);
    return v_x_371_;
}
pub unsafe fn l_Std_Iterators_ULiftT_run___boxed(
    mut v_n_372_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_373_: *mut crate::leanh::LeanObject,
    mut v_x_374_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_375_ = l_Std_Iterators_ULiftT_run(v_n_372_, v_00_u03b1_373_, v_x_374_);
    crate::leanh::lean_dec(v_x_374_);
    return v_res_375_;
}
pub unsafe fn l_Std_Iterators_instMonadULiftT___redArg___lam__0(
    mut v_f_376_: *mut crate::leanh::LeanObject,
    mut v_a_377_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_378_ = crate::leanh::lean_apply_1(v_f_376_, v_a_377_);
    return v___x_378_;
}
pub unsafe fn l_Std_Iterators_instMonadULiftT___redArg___lam__1(
    mut v_toBind_379_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_380_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_381_: *mut crate::leanh::LeanObject,
    mut v_x_382_: *mut crate::leanh::LeanObject,
    mut v_f_383_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_384_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_instMonadULiftT___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_384_, 0, v_f_383_);
    v___x_385_ = crate::leanh::lean_apply_4(
        v_toBind_379_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_x_382_,
        v___f_384_,
    );
    return v___x_385_;
}
pub unsafe fn l_Std_Iterators_instMonadULiftT___redArg___lam__4(
    mut v_y_386_: *mut crate::leanh::LeanObject,
    mut v_a_387_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_388_ = crate::leanh::lean_box(0);
    v___x_389_ = crate::leanh::lean_apply_1(v_y_386_, v___x_388_);
    return v___x_389_;
}
pub unsafe fn l_Std_Iterators_instMonadULiftT___redArg___lam__4___boxed(
    mut v_y_390_: *mut crate::leanh::LeanObject,
    mut v_a_391_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_392_ = l_Std_Iterators_instMonadULiftT___redArg___lam__4(v_y_390_, v_a_391_);
    crate::leanh::lean_dec(v_a_391_);
    return v_res_392_;
}
pub unsafe fn l_Std_Iterators_instMonadULiftT___redArg___lam__2(
    mut v_toBind_393_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_394_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_395_: *mut crate::leanh::LeanObject,
    mut v_x_396_: *mut crate::leanh::LeanObject,
    mut v_y_397_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_398_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_instMonadULiftT___redArg___lam__4___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_398_, 0, v_y_397_);
    v___x_399_ = crate::leanh::lean_apply_4(
        v_toBind_393_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_x_396_,
        v___f_398_,
    );
    return v___x_399_;
}
pub unsafe fn l_Std_Iterators_instMonadULiftT___redArg___lam__6(
    mut v_f_400_: *mut crate::leanh::LeanObject,
    mut v_toPure_401_: *mut crate::leanh::LeanObject,
    mut v_a_402_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_403_ = crate::leanh::lean_apply_1(v_f_400_, v_a_402_);
    v___x_404_ = crate::leanh::lean_apply_2(v_toPure_401_, crate::leanh::lean_box(0), v___x_403_);
    return v___x_404_;
}
pub unsafe fn l_Std_Iterators_instMonadULiftT___redArg___lam__3(
    mut v_toPure_405_: *mut crate::leanh::LeanObject,
    mut v_toBind_406_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_407_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_408_: *mut crate::leanh::LeanObject,
    mut v_f_409_: *mut crate::leanh::LeanObject,
    mut v_x_410_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_411_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_instMonadULiftT___redArg___lam__6 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_411_, 0, v_f_409_);
    crate::leanh::lean_closure_set(v___f_411_, 1, v_toPure_405_);
    v___x_412_ = crate::leanh::lean_apply_4(
        v_toBind_406_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_x_410_,
        v___f_411_,
    );
    return v___x_412_;
}
pub unsafe fn l_Std_Iterators_instMonadULiftT___redArg___lam__5(
    mut v_toPure_413_: *mut crate::leanh::LeanObject,
    mut v___y_414_: *mut crate::leanh::LeanObject,
    mut v_a_415_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_416_ = crate::leanh::lean_apply_2(v_toPure_413_, crate::leanh::lean_box(0), v___y_414_);
    return v___x_416_;
}
pub unsafe fn l_Std_Iterators_instMonadULiftT___redArg___lam__5___boxed(
    mut v_toPure_417_: *mut crate::leanh::LeanObject,
    mut v___y_418_: *mut crate::leanh::LeanObject,
    mut v_a_419_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_420_ =
        l_Std_Iterators_instMonadULiftT___redArg___lam__5(v_toPure_417_, v___y_418_, v_a_419_);
    crate::leanh::lean_dec(v_a_419_);
    return v_res_420_;
}
pub unsafe fn l_Std_Iterators_instMonadULiftT___redArg___lam__7(
    mut v_toPure_421_: *mut crate::leanh::LeanObject,
    mut v_toBind_422_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_423_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_424_: *mut crate::leanh::LeanObject,
    mut v___y_425_: *mut crate::leanh::LeanObject,
    mut v___y_426_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_427_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_instMonadULiftT___redArg___lam__5___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_427_, 0, v_toPure_421_);
    crate::leanh::lean_closure_set(v___f_427_, 1, v___y_425_);
    v___x_428_ = crate::leanh::lean_apply_4(
        v_toBind_422_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___y_426_,
        v___f_427_,
    );
    return v___x_428_;
}
pub unsafe fn l_Std_Iterators_instMonadULiftT___redArg___lam__8(
    mut v_toPure_429_: *mut crate::leanh::LeanObject,
    mut v_a_430_: *mut crate::leanh::LeanObject,
    mut v_x_431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_432_ = crate::leanh::lean_apply_2(v_toPure_429_, crate::leanh::lean_box(0), v_a_430_);
    return v___x_432_;
}
pub unsafe fn l_Std_Iterators_instMonadULiftT___redArg___lam__8___boxed(
    mut v_toPure_433_: *mut crate::leanh::LeanObject,
    mut v_a_434_: *mut crate::leanh::LeanObject,
    mut v_x_435_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_436_ =
        l_Std_Iterators_instMonadULiftT___redArg___lam__8(v_toPure_433_, v_a_434_, v_x_435_);
    crate::leanh::lean_dec(v_x_435_);
    return v_res_436_;
}
pub unsafe fn l_Std_Iterators_instMonadULiftT___redArg___lam__9(
    mut v_toPure_437_: *mut crate::leanh::LeanObject,
    mut v_y_438_: *mut crate::leanh::LeanObject,
    mut v___f_439_: *mut crate::leanh::LeanObject,
    mut v_a_440_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_441_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_instMonadULiftT___redArg___lam__8___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_441_, 0, v_toPure_437_);
    crate::leanh::lean_closure_set(v___f_441_, 1, v_a_440_);
    v___x_442_ = crate::leanh::lean_box(0);
    v___x_443_ = crate::leanh::lean_apply_1(v_y_438_, v___x_442_);
    v___x_444_ = crate::leanh::lean_apply_4(
        v___f_439_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_443_,
        v___f_441_,
    );
    return v___x_444_;
}
pub unsafe fn l_Std_Iterators_instMonadULiftT___redArg___lam__10(
    mut v_toPure_445_: *mut crate::leanh::LeanObject,
    mut v___f_446_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_447_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_448_: *mut crate::leanh::LeanObject,
    mut v_x_449_: *mut crate::leanh::LeanObject,
    mut v_y_450_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___f_446_);
    v___f_451_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_instMonadULiftT___redArg___lam__9 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_451_, 0, v_toPure_445_);
    crate::leanh::lean_closure_set(v___f_451_, 1, v_y_450_);
    crate::leanh::lean_closure_set(v___f_451_, 2, v___f_446_);
    v___x_452_ = crate::leanh::lean_apply_4(
        v___f_446_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_x_449_,
        v___f_451_,
    );
    return v___x_452_;
}
pub unsafe fn l_Std_Iterators_instMonadULiftT___redArg___lam__11(
    mut v_toPure_453_: *mut crate::leanh::LeanObject,
    mut v___y_454_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_455_ = crate::leanh::lean_apply_2(v_toPure_453_, crate::leanh::lean_box(0), v___y_454_);
    return v___x_455_;
}
pub unsafe fn l_Std_Iterators_instMonadULiftT___redArg___lam__12(
    mut v_x_456_: *mut crate::leanh::LeanObject,
    mut v___f_457_: *mut crate::leanh::LeanObject,
    mut v___f_458_: *mut crate::leanh::LeanObject,
    mut v_y_459_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_460_ = crate::leanh::lean_box(0);
    v___x_461_ = crate::leanh::lean_apply_1(v_x_456_, v___x_460_);
    v___x_462_ = crate::leanh::lean_alloc_closure(l_Function_comp as *mut core::ffi::c_void, 6, 5);
    crate::leanh::lean_closure_set(v___x_462_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_462_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_462_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_462_, 3, v___f_457_);
    crate::leanh::lean_closure_set(v___x_462_, 4, v_y_459_);
    v___x_463_ = crate::leanh::lean_apply_4(
        v___f_458_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_461_,
        v___x_462_,
    );
    return v___x_463_;
}
pub unsafe fn l_Std_Iterators_instMonadULiftT___redArg___lam__13(
    mut v___f_464_: *mut crate::leanh::LeanObject,
    mut v___f_465_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_466_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_467_: *mut crate::leanh::LeanObject,
    mut v_f_468_: *mut crate::leanh::LeanObject,
    mut v_x_469_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___f_465_);
    v___f_470_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_instMonadULiftT___redArg___lam__12 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_470_, 0, v_x_469_);
    crate::leanh::lean_closure_set(v___f_470_, 1, v___f_464_);
    crate::leanh::lean_closure_set(v___f_470_, 2, v___f_465_);
    v___x_471_ = crate::leanh::lean_apply_4(
        v___f_465_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_f_468_,
        v___f_470_,
    );
    return v___x_471_;
}
pub unsafe fn l_Std_Iterators_instMonadULiftT___redArg___lam__14(
    mut v_toPure_472_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_473_: *mut crate::leanh::LeanObject,
    mut v_a_474_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_475_ = crate::leanh::lean_apply_2(v_toPure_472_, crate::leanh::lean_box(0), v_a_474_);
    return v___x_475_;
}
pub unsafe fn l_Std_Iterators_instMonadULiftT___redArg(
    mut v_inst_476_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_481_: u8 = 0;
    let mut v_toPure_482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_485_: u8 = 0;
    let mut v___f_486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_501_: u8 = 0;
    let mut v_unused_502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_506_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_477_ = crate::leanh::lean_ctor_get(v_inst_476_, 0);
                v_toBind_478_ = crate::leanh::lean_ctor_get(v_inst_476_, 1);
                v_isSharedCheck_506_ = (!crate::leanh::lean_is_exclusive(v_inst_476_)) as u8;
                if v_isSharedCheck_506_ == 0 {
                    v___x_480_ = v_inst_476_;
                    v_isShared_481_ = v_isSharedCheck_506_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toBind_478_);
                    crate::leanh::lean_inc(v_toApplicative_477_);
                    crate::leanh::lean_dec(v_inst_476_);
                    v___x_480_ = crate::leanh::lean_box(0);
                    v_isShared_481_ = v_isSharedCheck_506_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_482_ = crate::leanh::lean_ctor_get(v_toApplicative_477_, 1);
                v_isSharedCheck_501_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_477_)) as u8;
                if v_isSharedCheck_501_ == 0 {
                    v_unused_502_ = crate::leanh::lean_ctor_get(v_toApplicative_477_, 4);
                    crate::leanh::lean_dec(v_unused_502_);
                    v_unused_503_ = crate::leanh::lean_ctor_get(v_toApplicative_477_, 3);
                    crate::leanh::lean_dec(v_unused_503_);
                    v_unused_504_ = crate::leanh::lean_ctor_get(v_toApplicative_477_, 2);
                    crate::leanh::lean_dec(v_unused_504_);
                    v_unused_505_ = crate::leanh::lean_ctor_get(v_toApplicative_477_, 0);
                    crate::leanh::lean_dec(v_unused_505_);
                    v___x_484_ = v_toApplicative_477_;
                    v_isShared_485_ = v_isSharedCheck_501_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toPure_482_);
                    crate::leanh::lean_dec(v_toApplicative_477_);
                    v___x_484_ = crate::leanh::lean_box(0);
                    v_isShared_485_ = v_isSharedCheck_501_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc_n(v_toBind_478_, 3);
                v___f_486_ = crate::leanh::lean_alloc_closure(
                    l_Std_Iterators_instMonadULiftT___redArg___lam__1 as *mut core::ffi::c_void,
                    5,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_486_, 0, v_toBind_478_);
                v___f_487_ = crate::leanh::lean_alloc_closure(
                    l_Std_Iterators_instMonadULiftT___redArg___lam__2 as *mut core::ffi::c_void,
                    5,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_487_, 0, v_toBind_478_);
                crate::leanh::lean_inc_n(v_toPure_482_, 4);
                v___f_488_ = crate::leanh::lean_alloc_closure(
                    l_Std_Iterators_instMonadULiftT___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_488_, 0, v_toPure_482_);
                crate::leanh::lean_closure_set(v___f_488_, 1, v_toBind_478_);
                v___f_489_ = crate::leanh::lean_alloc_closure(
                    l_Std_Iterators_instMonadULiftT___redArg___lam__7 as *mut core::ffi::c_void,
                    6,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_489_, 0, v_toPure_482_);
                crate::leanh::lean_closure_set(v___f_489_, 1, v_toBind_478_);
                crate::leanh::lean_inc_ref_n(v___f_486_, 2);
                v___f_490_ = crate::leanh::lean_alloc_closure(
                    l_Std_Iterators_instMonadULiftT___redArg___lam__10 as *mut core::ffi::c_void,
                    6,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_490_, 0, v_toPure_482_);
                crate::leanh::lean_closure_set(v___f_490_, 1, v___f_486_);
                v___f_491_ = crate::leanh::lean_alloc_closure(
                    l_Std_Iterators_instMonadULiftT___redArg___lam__11 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_491_, 0, v_toPure_482_);
                v___f_492_ = crate::leanh::lean_alloc_closure(
                    l_Std_Iterators_instMonadULiftT___redArg___lam__13 as *mut core::ffi::c_void,
                    6,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_492_, 0, v___f_491_);
                crate::leanh::lean_closure_set(v___f_492_, 1, v___f_486_);
                v___f_493_ = crate::leanh::lean_alloc_closure(
                    l_Std_Iterators_instMonadULiftT___redArg___lam__14 as *mut core::ffi::c_void,
                    3,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_493_, 0, v_toPure_482_);
                v___x_494_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_494_, 0, v___f_488_);
                crate::leanh::lean_ctor_set(v___x_494_, 1, v___f_489_);
                if v_isShared_485_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_484_, 4, v___f_487_);
                    crate::leanh::lean_ctor_set(v___x_484_, 3, v___f_490_);
                    crate::leanh::lean_ctor_set(v___x_484_, 2, v___f_492_);
                    crate::leanh::lean_ctor_set(v___x_484_, 1, v___f_493_);
                    crate::leanh::lean_ctor_set(v___x_484_, 0, v___x_494_);
                    v___x_496_ = v___x_484_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_500_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_500_, 0, v___x_494_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_500_, 1, v___f_493_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_500_, 2, v___f_492_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_500_, 3, v___f_490_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_500_, 4, v___f_487_);
                    v___x_496_ = v_reuseFailAlloc_500_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_481_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_480_, 1, v___f_486_);
                    crate::leanh::lean_ctor_set(v___x_480_, 0, v___x_496_);
                    v___x_498_ = v___x_480_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_499_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_499_, 0, v___x_496_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_499_, 1, v___f_486_);
                    v___x_498_ = v_reuseFailAlloc_499_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_498_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Iterators_instMonadULiftT(
    mut v_n_507_: *mut crate::leanh::LeanObject,
    mut v_inst_508_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_509_ = l_Std_Iterators_instMonadULiftT___redArg(v_inst_508_);
    return v___x_509_;
}
pub unsafe fn l_Std_Iterators_Types_ULiftIterator_Monadic_modifyStep___redArg(
    mut v_step_510_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_it_511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_515_: u8 = 0;
    let mut v___x_517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_519_: u8 = 0;
    let mut v_it_520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_523_: u8 = 0;
    let mut v___x_525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_527_: u8 = 0;
    let mut v___x_528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_step_510_) {
                0 => {
                    v_it_511_ = crate::leanh::lean_ctor_get(v_step_510_, 0);
                    v_out_512_ = crate::leanh::lean_ctor_get(v_step_510_, 1);
                    v_isSharedCheck_519_ = (!crate::leanh::lean_is_exclusive(v_step_510_)) as u8;
                    if v_isSharedCheck_519_ == 0 {
                        v___x_514_ = v_step_510_;
                        v_isShared_515_ = v_isSharedCheck_519_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_out_512_);
                        crate::leanh::lean_inc(v_it_511_);
                        crate::leanh::lean_dec(v_step_510_);
                        v___x_514_ = crate::leanh::lean_box(0);
                        v_isShared_515_ = v_isSharedCheck_519_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_it_520_ = crate::leanh::lean_ctor_get(v_step_510_, 0);
                    v_isSharedCheck_527_ = (!crate::leanh::lean_is_exclusive(v_step_510_)) as u8;
                    if v_isSharedCheck_527_ == 0 {
                        v___x_522_ = v_step_510_;
                        v_isShared_523_ = v_isSharedCheck_527_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_it_520_);
                        crate::leanh::lean_dec(v_step_510_);
                        v___x_522_ = crate::leanh::lean_box(0);
                        v_isShared_523_ = v_isSharedCheck_527_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    v___x_528_ = crate::leanh::lean_box(2);
                    return v___x_528_;
                }
            },
            1 => {
                if v_isShared_515_ == 0 {
                    v___x_517_ = v___x_514_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_518_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_518_, 0, v_it_511_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_518_, 1, v_out_512_);
                    v___x_517_ = v_reuseFailAlloc_518_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_517_;
            }
            3 => {
                if v_isShared_523_ == 0 {
                    v___x_525_ = v___x_522_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_526_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_526_, 0, v_it_520_);
                    v___x_525_ = v_reuseFailAlloc_526_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_525_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Iterators_Types_ULiftIterator_Monadic_modifyStep(
    mut v_00_u03b1_529_: *mut crate::leanh::LeanObject,
    mut v_m_530_: *mut crate::leanh::LeanObject,
    mut v_n_531_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_532_: *mut crate::leanh::LeanObject,
    mut v_lift_533_: *mut crate::leanh::LeanObject,
    mut v_step_534_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_it_535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_539_: u8 = 0;
    let mut v___x_541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_543_: u8 = 0;
    let mut v_it_544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_547_: u8 = 0;
    let mut v___x_549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_551_: u8 = 0;
    let mut v___x_552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_step_534_) {
                0 => {
                    v_it_535_ = crate::leanh::lean_ctor_get(v_step_534_, 0);
                    v_out_536_ = crate::leanh::lean_ctor_get(v_step_534_, 1);
                    v_isSharedCheck_543_ = (!crate::leanh::lean_is_exclusive(v_step_534_)) as u8;
                    if v_isSharedCheck_543_ == 0 {
                        v___x_538_ = v_step_534_;
                        v_isShared_539_ = v_isSharedCheck_543_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_out_536_);
                        crate::leanh::lean_inc(v_it_535_);
                        crate::leanh::lean_dec(v_step_534_);
                        v___x_538_ = crate::leanh::lean_box(0);
                        v_isShared_539_ = v_isSharedCheck_543_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_it_544_ = crate::leanh::lean_ctor_get(v_step_534_, 0);
                    v_isSharedCheck_551_ = (!crate::leanh::lean_is_exclusive(v_step_534_)) as u8;
                    if v_isSharedCheck_551_ == 0 {
                        v___x_546_ = v_step_534_;
                        v_isShared_547_ = v_isSharedCheck_551_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_it_544_);
                        crate::leanh::lean_dec(v_step_534_);
                        v___x_546_ = crate::leanh::lean_box(0);
                        v_isShared_547_ = v_isSharedCheck_551_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    v___x_552_ = crate::leanh::lean_box(2);
                    return v___x_552_;
                }
            },
            1 => {
                if v_isShared_539_ == 0 {
                    v___x_541_ = v___x_538_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_542_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_542_, 0, v_it_535_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_542_, 1, v_out_536_);
                    v___x_541_ = v_reuseFailAlloc_542_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_541_;
            }
            3 => {
                if v_isShared_547_ == 0 {
                    v___x_549_ = v___x_546_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_550_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_550_, 0, v_it_544_);
                    v___x_549_ = v_reuseFailAlloc_550_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_549_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Iterators_Types_ULiftIterator_Monadic_modifyStep___boxed(
    mut v_00_u03b1_553_: *mut crate::leanh::LeanObject,
    mut v_m_554_: *mut crate::leanh::LeanObject,
    mut v_n_555_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_556_: *mut crate::leanh::LeanObject,
    mut v_lift_557_: *mut crate::leanh::LeanObject,
    mut v_step_558_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_559_ = l_Std_Iterators_Types_ULiftIterator_Monadic_modifyStep(
        v_00_u03b1_553_,
        v_m_554_,
        v_n_555_,
        v_00_u03b2_556_,
        v_lift_557_,
        v_step_558_,
    );
    crate::leanh::lean_dec(v_lift_557_);
    return v_res_559_;
}
pub unsafe fn l_Std_Iterators_Types_ULiftIterator_instIterator___redArg___lam__0(
    mut v_toPure_560_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_561_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_it_562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_566_: u8 = 0;
    let mut v___x_568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_571_: u8 = 0;
    let mut v_it_572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_575_: u8 = 0;
    let mut v___x_577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_580_: u8 = 0;
    let mut v___x_581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_____do__lift_561_) {
                0 => {
                    v_it_562_ = crate::leanh::lean_ctor_get(v_____do__lift_561_, 0);
                    v_out_563_ = crate::leanh::lean_ctor_get(v_____do__lift_561_, 1);
                    v_isSharedCheck_571_ =
                        (!crate::leanh::lean_is_exclusive(v_____do__lift_561_)) as u8;
                    if v_isSharedCheck_571_ == 0 {
                        v___x_565_ = v_____do__lift_561_;
                        v_isShared_566_ = v_isSharedCheck_571_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_out_563_);
                        crate::leanh::lean_inc(v_it_562_);
                        crate::leanh::lean_dec(v_____do__lift_561_);
                        v___x_565_ = crate::leanh::lean_box(0);
                        v_isShared_566_ = v_isSharedCheck_571_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_it_572_ = crate::leanh::lean_ctor_get(v_____do__lift_561_, 0);
                    v_isSharedCheck_580_ =
                        (!crate::leanh::lean_is_exclusive(v_____do__lift_561_)) as u8;
                    if v_isSharedCheck_580_ == 0 {
                        v___x_574_ = v_____do__lift_561_;
                        v_isShared_575_ = v_isSharedCheck_580_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_it_572_);
                        crate::leanh::lean_dec(v_____do__lift_561_);
                        v___x_574_ = crate::leanh::lean_box(0);
                        v_isShared_575_ = v_isSharedCheck_580_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    v___x_581_ = crate::leanh::lean_box(2);
                    v___x_582_ = crate::leanh::lean_apply_2(
                        v_toPure_560_,
                        crate::leanh::lean_box(0),
                        v___x_581_,
                    );
                    return v___x_582_;
                }
            },
            1 => {
                if v_isShared_566_ == 0 {
                    v___x_568_ = v___x_565_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_570_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_570_, 0, v_it_562_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_570_, 1, v_out_563_);
                    v___x_568_ = v_reuseFailAlloc_570_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_569_ = crate::leanh::lean_apply_2(
                    v_toPure_560_,
                    crate::leanh::lean_box(0),
                    v___x_568_,
                );
                return v___x_569_;
            }
            3 => {
                if v_isShared_575_ == 0 {
                    v___x_577_ = v___x_574_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_579_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_579_, 0, v_it_572_);
                    v___x_577_ = v_reuseFailAlloc_579_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_578_ = crate::leanh::lean_apply_2(
                    v_toPure_560_,
                    crate::leanh::lean_box(0),
                    v___x_577_,
                );
                return v___x_578_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Iterators_Types_ULiftIterator_instIterator___redArg___lam__1(
    mut v_inst_583_: *mut crate::leanh::LeanObject,
    mut v_lift_584_: *mut crate::leanh::LeanObject,
    mut v_toBind_585_: *mut crate::leanh::LeanObject,
    mut v___f_586_: *mut crate::leanh::LeanObject,
    mut v_it_587_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_588_ = crate::leanh::lean_apply_1(v_inst_583_, v_it_587_);
    v___x_589_ = crate::leanh::lean_apply_2(v_lift_584_, crate::leanh::lean_box(0), v___x_588_);
    v___x_590_ = crate::leanh::lean_apply_4(
        v_toBind_585_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_589_,
        v___f_586_,
    );
    return v___x_590_;
}
pub unsafe fn l_Std_Iterators_Types_ULiftIterator_instIterator___redArg(
    mut v_lift_591_: *mut crate::leanh::LeanObject,
    mut v_inst_592_: *mut crate::leanh::LeanObject,
    mut v_inst_593_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_594_ = crate::leanh::lean_ctor_get(v_inst_593_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_594_);
    v_toBind_595_ = crate::leanh::lean_ctor_get(v_inst_593_, 1);
    crate::leanh::lean_inc(v_toBind_595_);
    crate::leanh::lean_dec_ref(v_inst_593_);
    v_toPure_596_ = crate::leanh::lean_ctor_get(v_toApplicative_594_, 1);
    crate::leanh::lean_inc(v_toPure_596_);
    crate::leanh::lean_dec_ref(v_toApplicative_594_);
    v___f_597_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_Types_ULiftIterator_instIterator___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_597_, 0, v_toPure_596_);
    v___f_598_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_Types_ULiftIterator_instIterator___redArg___lam__1
            as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_598_, 0, v_inst_592_);
    crate::leanh::lean_closure_set(v___f_598_, 1, v_lift_591_);
    crate::leanh::lean_closure_set(v___f_598_, 2, v_toBind_595_);
    crate::leanh::lean_closure_set(v___f_598_, 3, v___f_597_);
    return v___f_598_;
}
pub unsafe fn l_Std_Iterators_Types_ULiftIterator_instIterator(
    mut v_00_u03b1_599_: *mut crate::leanh::LeanObject,
    mut v_m_600_: *mut crate::leanh::LeanObject,
    mut v_n_601_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_602_: *mut crate::leanh::LeanObject,
    mut v_lift_603_: *mut crate::leanh::LeanObject,
    mut v_inst_604_: *mut crate::leanh::LeanObject,
    mut v_inst_605_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_606_ = l_Std_Iterators_Types_ULiftIterator_instIterator___redArg(
        v_lift_603_,
        v_inst_604_,
        v_inst_605_,
    );
    return v___x_606_;
}
pub unsafe fn l___private_Init_Data_Iterators_Combinators_Monadic_ULift_0__Std_Iterators_Types_ULiftIterator_instFinitenessRelation(
    mut v_00_u03b1_607_: *mut crate::leanh::LeanObject,
    mut v_m_608_: *mut crate::leanh::LeanObject,
    mut v_n_609_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_610_: *mut crate::leanh::LeanObject,
    mut v_lift_611_: *mut crate::leanh::LeanObject,
    mut v_inst_612_: *mut crate::leanh::LeanObject,
    mut v_inst_613_: *mut crate::leanh::LeanObject,
    mut v_inst_614_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_615_ = crate::leanh::lean_box(0);
    return v___x_615_;
}
pub unsafe fn l___private_Init_Data_Iterators_Combinators_Monadic_ULift_0__Std_Iterators_Types_ULiftIterator_instFinitenessRelation___boxed(
    mut v_00_u03b1_616_: *mut crate::leanh::LeanObject,
    mut v_m_617_: *mut crate::leanh::LeanObject,
    mut v_n_618_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_619_: *mut crate::leanh::LeanObject,
    mut v_lift_620_: *mut crate::leanh::LeanObject,
    mut v_inst_621_: *mut crate::leanh::LeanObject,
    mut v_inst_622_: *mut crate::leanh::LeanObject,
    mut v_inst_623_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_624_ = l___private_Init_Data_Iterators_Combinators_Monadic_ULift_0__Std_Iterators_Types_ULiftIterator_instFinitenessRelation(v_00_u03b1_616_, v_m_617_, v_n_618_, v_00_u03b2_619_, v_lift_620_, v_inst_621_, v_inst_622_, v_inst_623_);
    crate::leanh::lean_dec_ref(v_inst_623_);
    crate::leanh::lean_dec(v_inst_621_);
    crate::leanh::lean_dec(v_lift_620_);
    return v_res_624_;
}
pub unsafe fn l___private_Init_Data_Iterators_Combinators_Monadic_ULift_0__Std_Iterators_Types_ULiftIterator_instProductivenessRelation(
    mut v_00_u03b1_625_: *mut crate::leanh::LeanObject,
    mut v_m_626_: *mut crate::leanh::LeanObject,
    mut v_n_627_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_628_: *mut crate::leanh::LeanObject,
    mut v_lift_629_: *mut crate::leanh::LeanObject,
    mut v_inst_630_: *mut crate::leanh::LeanObject,
    mut v_inst_631_: *mut crate::leanh::LeanObject,
    mut v_inst_632_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_633_ = crate::leanh::lean_box(0);
    return v___x_633_;
}
pub unsafe fn l___private_Init_Data_Iterators_Combinators_Monadic_ULift_0__Std_Iterators_Types_ULiftIterator_instProductivenessRelation___boxed(
    mut v_00_u03b1_634_: *mut crate::leanh::LeanObject,
    mut v_m_635_: *mut crate::leanh::LeanObject,
    mut v_n_636_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_637_: *mut crate::leanh::LeanObject,
    mut v_lift_638_: *mut crate::leanh::LeanObject,
    mut v_inst_639_: *mut crate::leanh::LeanObject,
    mut v_inst_640_: *mut crate::leanh::LeanObject,
    mut v_inst_641_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_642_ = l___private_Init_Data_Iterators_Combinators_Monadic_ULift_0__Std_Iterators_Types_ULiftIterator_instProductivenessRelation(v_00_u03b1_634_, v_m_635_, v_n_636_, v_00_u03b2_637_, v_lift_638_, v_inst_639_, v_inst_640_, v_inst_641_);
    crate::leanh::lean_dec_ref(v_inst_641_);
    crate::leanh::lean_dec(v_inst_639_);
    crate::leanh::lean_dec(v_lift_638_);
    return v_res_642_;
}
pub unsafe fn l_Std_Iterators_Types_ULiftIterator_instIteratorLoop___redArg___lam__0(
    mut v_toPure_643_: *mut crate::leanh::LeanObject,
    mut v_recur_644_: *mut crate::leanh::LeanObject,
    mut v_it_645_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_646_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_646_) == 0 {
        let mut v_a_647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_it_645_);
        crate::leanh::lean_dec(v_recur_644_);
        v_a_647_ = crate::leanh::lean_ctor_get(v_____do__lift_646_, 0);
        crate::leanh::lean_inc(v_a_647_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_646_, 1);
        v___x_648_ = crate::leanh::lean_apply_2(v_toPure_643_, crate::leanh::lean_box(0), v_a_647_);
        return v___x_648_;
    } else {
        let mut v_a_649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_643_);
        v_a_649_ = crate::leanh::lean_ctor_get(v_____do__lift_646_, 0);
        crate::leanh::lean_inc(v_a_649_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_646_, 1);
        v___x_650_ = crate::leanh::lean_apply_4(
            v_recur_644_,
            v_it_645_,
            v_a_649_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_650_;
    }
}
pub unsafe fn l_Std_Iterators_Types_ULiftIterator_instIteratorLoop___redArg___lam__1(
    mut v_toPure_651_: *mut crate::leanh::LeanObject,
    mut v_recur_652_: *mut crate::leanh::LeanObject,
    mut v___y_653_: *mut crate::leanh::LeanObject,
    mut v_acc_654_: *mut crate::leanh::LeanObject,
    mut v_toBind_655_: *mut crate::leanh::LeanObject,
    mut v_s_656_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_s_656_) {
        0 => {
            let mut v_it_657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_it_657_ = crate::leanh::lean_ctor_get(v_s_656_, 0);
            crate::leanh::lean_inc(v_it_657_);
            v_out_658_ = crate::leanh::lean_ctor_get(v_s_656_, 1);
            crate::leanh::lean_inc(v_out_658_);
            crate::leanh::lean_dec_ref_known(v_s_656_, 2);
            v___f_659_ = crate::leanh::lean_alloc_closure(
                l_Std_Iterators_Types_ULiftIterator_instIteratorLoop___redArg___lam__0
                    as *mut core::ffi::c_void,
                4,
                3,
            );
            crate::leanh::lean_closure_set(v___f_659_, 0, v_toPure_651_);
            crate::leanh::lean_closure_set(v___f_659_, 1, v_recur_652_);
            crate::leanh::lean_closure_set(v___f_659_, 2, v_it_657_);
            v___x_660_ = crate::leanh::lean_apply_3(
                v___y_653_,
                v_out_658_,
                crate::leanh::lean_box(0),
                v_acc_654_,
            );
            v___x_661_ = crate::leanh::lean_apply_4(
                v_toBind_655_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_660_,
                v___f_659_,
            );
            return v___x_661_;
        }
        1 => {
            let mut v_it_662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_toBind_655_);
            crate::leanh::lean_dec(v___y_653_);
            crate::leanh::lean_dec(v_toPure_651_);
            v_it_662_ = crate::leanh::lean_ctor_get(v_s_656_, 0);
            crate::leanh::lean_inc(v_it_662_);
            crate::leanh::lean_dec_ref_known(v_s_656_, 1);
            v___x_663_ = crate::leanh::lean_apply_4(
                v_recur_652_,
                v_it_662_,
                v_acc_654_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_663_;
        }
        _ => {
            let mut v___x_664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_toBind_655_);
            crate::leanh::lean_dec(v___y_653_);
            crate::leanh::lean_dec(v_recur_652_);
            v___x_664_ =
                crate::leanh::lean_apply_2(v_toPure_651_, crate::leanh::lean_box(0), v_acc_654_);
            return v___x_664_;
        }
    }
}
pub unsafe fn l_Std_Iterators_Types_ULiftIterator_instIteratorLoop___redArg___lam__3(
    mut v_inst_665_: *mut crate::leanh::LeanObject,
    mut v_toPure_666_: *mut crate::leanh::LeanObject,
    mut v___y_667_: *mut crate::leanh::LeanObject,
    mut v_toBind_668_: *mut crate::leanh::LeanObject,
    mut v_inst_669_: *mut crate::leanh::LeanObject,
    mut v_lift_670_: *mut crate::leanh::LeanObject,
    mut v_lift_671_: *mut crate::leanh::LeanObject,
    mut v_it_672_: *mut crate::leanh::LeanObject,
    mut v_acc_673_: *mut crate::leanh::LeanObject,
    mut v_hP_674_: *mut crate::leanh::LeanObject,
    mut v_recur_675_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_676_ = crate::leanh::lean_ctor_get(v_inst_665_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_676_);
    v_toBind_677_ = crate::leanh::lean_ctor_get(v_inst_665_, 1);
    crate::leanh::lean_inc(v_toBind_677_);
    crate::leanh::lean_dec_ref(v_inst_665_);
    v_toPure_678_ = crate::leanh::lean_ctor_get(v_toApplicative_676_, 1);
    crate::leanh::lean_inc(v_toPure_678_);
    crate::leanh::lean_dec_ref(v_toApplicative_676_);
    v___f_679_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_Types_ULiftIterator_instIteratorLoop___redArg___lam__1
            as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___f_679_, 0, v_toPure_666_);
    crate::leanh::lean_closure_set(v___f_679_, 1, v_recur_675_);
    crate::leanh::lean_closure_set(v___f_679_, 2, v___y_667_);
    crate::leanh::lean_closure_set(v___f_679_, 3, v_acc_673_);
    crate::leanh::lean_closure_set(v___f_679_, 4, v_toBind_668_);
    v___f_680_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_Types_ULiftIterator_instIterator___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_680_, 0, v_toPure_678_);
    v___x_681_ = crate::leanh::lean_apply_1(v_inst_669_, v_it_672_);
    v___x_682_ = crate::leanh::lean_apply_2(v_lift_670_, crate::leanh::lean_box(0), v___x_681_);
    v___x_683_ = crate::leanh::lean_apply_4(
        v_toBind_677_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_682_,
        v___f_680_,
    );
    v___x_684_ = crate::leanh::lean_apply_4(
        v_lift_671_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_679_,
        v___x_683_,
    );
    return v___x_684_;
}
pub unsafe fn l_Std_Iterators_Types_ULiftIterator_instIteratorLoop___redArg___lam__2(
    mut v_inst_685_: *mut crate::leanh::LeanObject,
    mut v_inst_686_: *mut crate::leanh::LeanObject,
    mut v_inst_687_: *mut crate::leanh::LeanObject,
    mut v_lift_688_: *mut crate::leanh::LeanObject,
    mut v_lift_689_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_690_: *mut crate::leanh::LeanObject,
    mut v_Pl_691_: *mut crate::leanh::LeanObject,
    mut v_it_692_: *mut crate::leanh::LeanObject,
    mut v_init_693_: *mut crate::leanh::LeanObject,
    mut v___y_694_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_695_ = crate::leanh::lean_ctor_get(v_inst_685_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_695_);
    v_toBind_696_ = crate::leanh::lean_ctor_get(v_inst_685_, 1);
    crate::leanh::lean_inc(v_toBind_696_);
    crate::leanh::lean_dec_ref(v_inst_685_);
    v_toPure_697_ = crate::leanh::lean_ctor_get(v_toApplicative_695_, 1);
    crate::leanh::lean_inc(v_toPure_697_);
    crate::leanh::lean_dec_ref(v_toApplicative_695_);
    v___f_698_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_Types_ULiftIterator_instIteratorLoop___redArg___lam__3
            as *mut core::ffi::c_void,
        11,
        7,
    );
    crate::leanh::lean_closure_set(v___f_698_, 0, v_inst_686_);
    crate::leanh::lean_closure_set(v___f_698_, 1, v_toPure_697_);
    crate::leanh::lean_closure_set(v___f_698_, 2, v___y_694_);
    crate::leanh::lean_closure_set(v___f_698_, 3, v_toBind_696_);
    crate::leanh::lean_closure_set(v___f_698_, 4, v_inst_687_);
    crate::leanh::lean_closure_set(v___f_698_, 5, v_lift_688_);
    crate::leanh::lean_closure_set(v___f_698_, 6, v_lift_689_);
    v___x_699_ = l_WellFounded_opaqueFix_u2083___redArg(
        v___f_698_,
        v_it_692_,
        v_init_693_,
        crate::leanh::lean_box(0),
    );
    return v___x_699_;
}
pub unsafe fn l_Std_Iterators_Types_ULiftIterator_instIteratorLoop___redArg(
    mut v_lift_700_: *mut crate::leanh::LeanObject,
    mut v_inst_701_: *mut crate::leanh::LeanObject,
    mut v_inst_702_: *mut crate::leanh::LeanObject,
    mut v_inst_703_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_704_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_Types_ULiftIterator_instIteratorLoop___redArg___lam__2
            as *mut core::ffi::c_void,
        10,
        4,
    );
    crate::leanh::lean_closure_set(v___f_704_, 0, v_inst_702_);
    crate::leanh::lean_closure_set(v___f_704_, 1, v_inst_701_);
    crate::leanh::lean_closure_set(v___f_704_, 2, v_inst_703_);
    crate::leanh::lean_closure_set(v___f_704_, 3, v_lift_700_);
    return v___f_704_;
}
pub unsafe fn l_Std_Iterators_Types_ULiftIterator_instIteratorLoop(
    mut v_00_u03b1_705_: *mut crate::leanh::LeanObject,
    mut v_m_706_: *mut crate::leanh::LeanObject,
    mut v_n_707_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_708_: *mut crate::leanh::LeanObject,
    mut v_lift_709_: *mut crate::leanh::LeanObject,
    mut v_o_710_: *mut crate::leanh::LeanObject,
    mut v_inst_711_: *mut crate::leanh::LeanObject,
    mut v_inst_712_: *mut crate::leanh::LeanObject,
    mut v_inst_713_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_714_ = crate::leanh::lean_alloc_closure(
        l_Std_Iterators_Types_ULiftIterator_instIteratorLoop___redArg___lam__2
            as *mut core::ffi::c_void,
        10,
        4,
    );
    crate::leanh::lean_closure_set(v___f_714_, 0, v_inst_712_);
    crate::leanh::lean_closure_set(v___f_714_, 1, v_inst_711_);
    crate::leanh::lean_closure_set(v___f_714_, 2, v_inst_713_);
    crate::leanh::lean_closure_set(v___f_714_, 3, v_lift_709_);
    return v___f_714_;
}
pub unsafe fn l_Std_IterM_uLift___redArg(
    mut v_it_715_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_it_715_);
    return v_it_715_;
}
pub unsafe fn l_Std_IterM_uLift___redArg___boxed(
    mut v_it_716_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_717_ = l_Std_IterM_uLift___redArg(v_it_716_);
    crate::leanh::lean_dec(v_it_716_);
    return v_res_717_;
}
pub unsafe fn l_Std_IterM_uLift(
    mut v_00_u03b1_718_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_719_: *mut crate::leanh::LeanObject,
    mut v_m_720_: *mut crate::leanh::LeanObject,
    mut v_it_721_: *mut crate::leanh::LeanObject,
    mut v_n_722_: *mut crate::leanh::LeanObject,
    mut v_lift_723_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_it_721_);
    return v_it_721_;
}
pub unsafe fn l_Std_IterM_uLift___boxed(
    mut v_00_u03b1_724_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_725_: *mut crate::leanh::LeanObject,
    mut v_m_726_: *mut crate::leanh::LeanObject,
    mut v_it_727_: *mut crate::leanh::LeanObject,
    mut v_n_728_: *mut crate::leanh::LeanObject,
    mut v_lift_729_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_730_ = l_Std_IterM_uLift(
        v_00_u03b1_724_,
        v_00_u03b2_725_,
        v_m_726_,
        v_it_727_,
        v_n_728_,
        v_lift_729_,
    );
    crate::leanh::lean_dec(v_lift_729_);
    crate::leanh::lean_dec(v_it_727_);
    return v_res_730_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_Combinators_Monadic_ULift(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Iterators_Combinators_Monadic_ULift(
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
pub unsafe fn initialize_Init_Data_Iterators_Combinators_Monadic_ULift(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Consumers_Monadic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Combinators_Monadic_ULift(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_Combinators_Monadic_ULift(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Iterators_Combinators_Monadic_ULift(builtin);
}
