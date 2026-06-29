// Lean compiler output
// Module: Init.Data.Nat.Control
// Imports: Init.Notation Init.Omega
use crate::r#gen::Init::Notation::{initialize_Init_Notation, runtime_initialize_Init_Notation};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::ffi::{lean_nat_dec_eq, lean_nat_sub};
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_forM_loop___redArg___lam__0___boxed(
    mut v_inst_363_: *mut crate::leanh::LeanObject,
    mut v_n_364_: *mut crate::leanh::LeanObject,
    mut v_f_365_: *mut crate::leanh::LeanObject,
    mut v_n_366_: *mut crate::leanh::LeanObject,
    mut v_____r_367_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_368_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___redArg___lam__0(
        v_inst_363_,
        v_n_364_,
        v_f_365_,
        v_n_366_,
        v_____r_367_,
    );
    crate::leanh::lean_dec(v_n_366_);
    return v_res_368_;
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_forM_loop___redArg(
    mut v_inst_369_: *mut crate::leanh::LeanObject,
    mut v_n_370_: *mut crate::leanh::LeanObject,
    mut v_f_371_: *mut crate::leanh::LeanObject,
    mut v_i_372_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zero_376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_377_: u8 = 0;
    v_toApplicative_373_ = crate::leanh::lean_ctor_get(v_inst_369_, 0);
    v_toBind_374_ = crate::leanh::lean_ctor_get(v_inst_369_, 1);
    crate::leanh::lean_inc(v_toBind_374_);
    v_toPure_375_ = crate::leanh::lean_ctor_get(v_toApplicative_373_, 1);
    v_zero_376_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_377_ = lean_nat_dec_eq(v_i_372_, v_zero_376_);
    if v_isZero_377_ == 1 {
        let mut v___x_378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc(v_toPure_375_);
        crate::leanh::lean_dec(v_toBind_374_);
        crate::leanh::lean_dec(v_f_371_);
        crate::leanh::lean_dec(v_n_370_);
        crate::leanh::lean_dec_ref(v_inst_369_);
        v___x_378_ = crate::leanh::lean_box(0);
        v___x_379_ =
            crate::leanh::lean_apply_2(v_toPure_375_, crate::leanh::lean_box(0), v___x_378_);
        return v___x_379_;
    } else {
        let mut v_one_380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_one_380_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_381_ = lean_nat_sub(v_i_372_, v_one_380_);
        crate::leanh::lean_inc(v_n_381_);
        crate::leanh::lean_inc(v_f_371_);
        crate::leanh::lean_inc(v_n_370_);
        v___f_382_ = crate::leanh::lean_alloc_closure(
            l___private_Init_Data_Nat_Control_0__Nat_forM_loop___redArg___lam__0___boxed
                as *mut core::ffi::c_void,
            5,
            4,
        );
        crate::leanh::lean_closure_set(v___f_382_, 0, v_inst_369_);
        crate::leanh::lean_closure_set(v___f_382_, 1, v_n_370_);
        crate::leanh::lean_closure_set(v___f_382_, 2, v_f_371_);
        crate::leanh::lean_closure_set(v___f_382_, 3, v_n_381_);
        v___x_383_ = lean_nat_sub(v_n_370_, v_n_381_);
        crate::leanh::lean_dec(v_n_381_);
        crate::leanh::lean_dec(v_n_370_);
        v___x_384_ = lean_nat_sub(v___x_383_, v_one_380_);
        crate::leanh::lean_dec(v___x_383_);
        v___x_385_ = crate::leanh::lean_apply_2(v_f_371_, v___x_384_, crate::leanh::lean_box(0));
        v___x_386_ = crate::leanh::lean_apply_4(
            v_toBind_374_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_385_,
            v___f_382_,
        );
        return v___x_386_;
    }
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_forM_loop___redArg___lam__0(
    mut v_inst_387_: *mut crate::leanh::LeanObject,
    mut v_n_388_: *mut crate::leanh::LeanObject,
    mut v_f_389_: *mut crate::leanh::LeanObject,
    mut v_n_390_: *mut crate::leanh::LeanObject,
    mut v_____r_391_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_392_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___redArg(
        v_inst_387_,
        v_n_388_,
        v_f_389_,
        v_n_390_,
    );
    return v___x_392_;
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_forM_loop___redArg___boxed(
    mut v_inst_393_: *mut crate::leanh::LeanObject,
    mut v_n_394_: *mut crate::leanh::LeanObject,
    mut v_f_395_: *mut crate::leanh::LeanObject,
    mut v_i_396_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_397_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___redArg(
        v_inst_393_,
        v_n_394_,
        v_f_395_,
        v_i_396_,
    );
    crate::leanh::lean_dec(v_i_396_);
    return v_res_397_;
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_forM_loop(
    mut v_m_398_: *mut crate::leanh::LeanObject,
    mut v_inst_399_: *mut crate::leanh::LeanObject,
    mut v_n_400_: *mut crate::leanh::LeanObject,
    mut v_f_401_: *mut crate::leanh::LeanObject,
    mut v_i_402_: *mut crate::leanh::LeanObject,
    mut v_a_403_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_404_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___redArg(
        v_inst_399_,
        v_n_400_,
        v_f_401_,
        v_i_402_,
    );
    return v___x_404_;
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_forM_loop___boxed(
    mut v_m_405_: *mut crate::leanh::LeanObject,
    mut v_inst_406_: *mut crate::leanh::LeanObject,
    mut v_n_407_: *mut crate::leanh::LeanObject,
    mut v_f_408_: *mut crate::leanh::LeanObject,
    mut v_i_409_: *mut crate::leanh::LeanObject,
    mut v_a_410_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_411_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop(
        v_m_405_,
        v_inst_406_,
        v_n_407_,
        v_f_408_,
        v_i_409_,
        v_a_410_,
    );
    crate::leanh::lean_dec(v_i_409_);
    return v_res_411_;
}
pub unsafe fn l_Nat_forM___redArg(
    mut v_inst_412_: *mut crate::leanh::LeanObject,
    mut v_n_413_: *mut crate::leanh::LeanObject,
    mut v_f_414_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_n_413_);
    v___x_415_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___redArg(
        v_inst_412_,
        v_n_413_,
        v_f_414_,
        v_n_413_,
    );
    crate::leanh::lean_dec(v_n_413_);
    return v___x_415_;
}
pub unsafe fn l_Nat_forM(
    mut v_m_416_: *mut crate::leanh::LeanObject,
    mut v_inst_417_: *mut crate::leanh::LeanObject,
    mut v_n_418_: *mut crate::leanh::LeanObject,
    mut v_f_419_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_n_418_);
    v___x_420_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___redArg(
        v_inst_417_,
        v_n_418_,
        v_f_419_,
        v_n_418_,
    );
    crate::leanh::lean_dec(v_n_418_);
    return v___x_420_;
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_forRevM_loop___redArg___lam__0___boxed(
    mut v_inst_421_: *mut crate::leanh::LeanObject,
    mut v_f_422_: *mut crate::leanh::LeanObject,
    mut v_n_423_: *mut crate::leanh::LeanObject,
    mut v_____r_424_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_425_ = l___private_Init_Data_Nat_Control_0__Nat_forRevM_loop___redArg___lam__0(
        v_inst_421_,
        v_f_422_,
        v_n_423_,
        v_____r_424_,
    );
    crate::leanh::lean_dec(v_n_423_);
    return v_res_425_;
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_forRevM_loop___redArg(
    mut v_inst_426_: *mut crate::leanh::LeanObject,
    mut v_f_427_: *mut crate::leanh::LeanObject,
    mut v_i_428_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zero_432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_433_: u8 = 0;
    v_toApplicative_429_ = crate::leanh::lean_ctor_get(v_inst_426_, 0);
    v_toBind_430_ = crate::leanh::lean_ctor_get(v_inst_426_, 1);
    crate::leanh::lean_inc(v_toBind_430_);
    v_toPure_431_ = crate::leanh::lean_ctor_get(v_toApplicative_429_, 1);
    v_zero_432_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_433_ = lean_nat_dec_eq(v_i_428_, v_zero_432_);
    if v_isZero_433_ == 1 {
        let mut v___x_434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc(v_toPure_431_);
        crate::leanh::lean_dec(v_toBind_430_);
        crate::leanh::lean_dec(v_f_427_);
        crate::leanh::lean_dec_ref(v_inst_426_);
        v___x_434_ = crate::leanh::lean_box(0);
        v___x_435_ =
            crate::leanh::lean_apply_2(v_toPure_431_, crate::leanh::lean_box(0), v___x_434_);
        return v___x_435_;
    } else {
        let mut v_one_436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_one_436_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_437_ = lean_nat_sub(v_i_428_, v_one_436_);
        crate::leanh::lean_inc(v_n_437_);
        crate::leanh::lean_inc(v_f_427_);
        v___f_438_ = crate::leanh::lean_alloc_closure(
            l___private_Init_Data_Nat_Control_0__Nat_forRevM_loop___redArg___lam__0___boxed
                as *mut core::ffi::c_void,
            4,
            3,
        );
        crate::leanh::lean_closure_set(v___f_438_, 0, v_inst_426_);
        crate::leanh::lean_closure_set(v___f_438_, 1, v_f_427_);
        crate::leanh::lean_closure_set(v___f_438_, 2, v_n_437_);
        v___x_439_ = crate::leanh::lean_apply_2(v_f_427_, v_n_437_, crate::leanh::lean_box(0));
        v___x_440_ = crate::leanh::lean_apply_4(
            v_toBind_430_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_439_,
            v___f_438_,
        );
        return v___x_440_;
    }
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_forRevM_loop___redArg___lam__0(
    mut v_inst_441_: *mut crate::leanh::LeanObject,
    mut v_f_442_: *mut crate::leanh::LeanObject,
    mut v_n_443_: *mut crate::leanh::LeanObject,
    mut v_____r_444_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_445_ = l___private_Init_Data_Nat_Control_0__Nat_forRevM_loop___redArg(
        v_inst_441_,
        v_f_442_,
        v_n_443_,
    );
    return v___x_445_;
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_forRevM_loop___redArg___boxed(
    mut v_inst_446_: *mut crate::leanh::LeanObject,
    mut v_f_447_: *mut crate::leanh::LeanObject,
    mut v_i_448_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_449_ = l___private_Init_Data_Nat_Control_0__Nat_forRevM_loop___redArg(
        v_inst_446_,
        v_f_447_,
        v_i_448_,
    );
    crate::leanh::lean_dec(v_i_448_);
    return v_res_449_;
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_forRevM_loop(
    mut v_m_450_: *mut crate::leanh::LeanObject,
    mut v_inst_451_: *mut crate::leanh::LeanObject,
    mut v_n_452_: *mut crate::leanh::LeanObject,
    mut v_f_453_: *mut crate::leanh::LeanObject,
    mut v_i_454_: *mut crate::leanh::LeanObject,
    mut v_a_455_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_456_ = l___private_Init_Data_Nat_Control_0__Nat_forRevM_loop___redArg(
        v_inst_451_,
        v_f_453_,
        v_i_454_,
    );
    return v___x_456_;
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_forRevM_loop___boxed(
    mut v_m_457_: *mut crate::leanh::LeanObject,
    mut v_inst_458_: *mut crate::leanh::LeanObject,
    mut v_n_459_: *mut crate::leanh::LeanObject,
    mut v_f_460_: *mut crate::leanh::LeanObject,
    mut v_i_461_: *mut crate::leanh::LeanObject,
    mut v_a_462_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_463_ = l___private_Init_Data_Nat_Control_0__Nat_forRevM_loop(
        v_m_457_,
        v_inst_458_,
        v_n_459_,
        v_f_460_,
        v_i_461_,
        v_a_462_,
    );
    crate::leanh::lean_dec(v_i_461_);
    crate::leanh::lean_dec(v_n_459_);
    return v_res_463_;
}
pub unsafe fn l_Nat_forRevM___redArg(
    mut v_inst_464_: *mut crate::leanh::LeanObject,
    mut v_n_465_: *mut crate::leanh::LeanObject,
    mut v_f_466_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_467_ = l___private_Init_Data_Nat_Control_0__Nat_forRevM_loop___redArg(
        v_inst_464_,
        v_f_466_,
        v_n_465_,
    );
    return v___x_467_;
}
pub unsafe fn l_Nat_forRevM___redArg___boxed(
    mut v_inst_468_: *mut crate::leanh::LeanObject,
    mut v_n_469_: *mut crate::leanh::LeanObject,
    mut v_f_470_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_471_ = l_Nat_forRevM___redArg(v_inst_468_, v_n_469_, v_f_470_);
    crate::leanh::lean_dec(v_n_469_);
    return v_res_471_;
}
pub unsafe fn l_Nat_forRevM(
    mut v_m_472_: *mut crate::leanh::LeanObject,
    mut v_inst_473_: *mut crate::leanh::LeanObject,
    mut v_n_474_: *mut crate::leanh::LeanObject,
    mut v_f_475_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_476_ = l___private_Init_Data_Nat_Control_0__Nat_forRevM_loop___redArg(
        v_inst_473_,
        v_f_475_,
        v_n_474_,
    );
    return v___x_476_;
}
pub unsafe fn l_Nat_forRevM___boxed(
    mut v_m_477_: *mut crate::leanh::LeanObject,
    mut v_inst_478_: *mut crate::leanh::LeanObject,
    mut v_n_479_: *mut crate::leanh::LeanObject,
    mut v_f_480_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_481_ = l_Nat_forRevM(v_m_477_, v_inst_478_, v_n_479_, v_f_480_);
    crate::leanh::lean_dec(v_n_479_);
    return v_res_481_;
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___redArg___boxed(
    mut v_inst_482_: *mut crate::leanh::LeanObject,
    mut v_n_483_: *mut crate::leanh::LeanObject,
    mut v_f_484_: *mut crate::leanh::LeanObject,
    mut v_i_485_: *mut crate::leanh::LeanObject,
    mut v_a_486_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_487_ = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___redArg(
        v_inst_482_,
        v_n_483_,
        v_f_484_,
        v_i_485_,
        v_a_486_,
    );
    crate::leanh::lean_dec(v_i_485_);
    return v_res_487_;
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___redArg(
    mut v_inst_488_: *mut crate::leanh::LeanObject,
    mut v_n_489_: *mut crate::leanh::LeanObject,
    mut v_f_490_: *mut crate::leanh::LeanObject,
    mut v_i_491_: *mut crate::leanh::LeanObject,
    mut v_a_492_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zero_496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_497_: u8 = 0;
    v_toApplicative_493_ = crate::leanh::lean_ctor_get(v_inst_488_, 0);
    v_toBind_494_ = crate::leanh::lean_ctor_get(v_inst_488_, 1);
    crate::leanh::lean_inc(v_toBind_494_);
    v_toPure_495_ = crate::leanh::lean_ctor_get(v_toApplicative_493_, 1);
    v_zero_496_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_497_ = lean_nat_dec_eq(v_i_491_, v_zero_496_);
    if v_isZero_497_ == 1 {
        let mut v___x_498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc(v_toPure_495_);
        crate::leanh::lean_dec(v_toBind_494_);
        crate::leanh::lean_dec(v_f_490_);
        crate::leanh::lean_dec(v_n_489_);
        crate::leanh::lean_dec_ref(v_inst_488_);
        v___x_498_ = crate::leanh::lean_apply_2(v_toPure_495_, crate::leanh::lean_box(0), v_a_492_);
        return v___x_498_;
    } else {
        let mut v_one_499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_one_499_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_500_ = lean_nat_sub(v_i_491_, v_one_499_);
        v___x_501_ = lean_nat_sub(v_n_489_, v_n_500_);
        v___x_502_ = lean_nat_sub(v___x_501_, v_one_499_);
        crate::leanh::lean_dec(v___x_501_);
        crate::leanh::lean_inc(v_f_490_);
        v___x_503_ =
            crate::leanh::lean_apply_3(v_f_490_, v___x_502_, crate::leanh::lean_box(0), v_a_492_);
        v___x_504_ = crate::leanh::lean_alloc_closure(
            l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___redArg___boxed
                as *mut core::ffi::c_void,
            5,
            4,
        );
        crate::leanh::lean_closure_set(v___x_504_, 0, v_inst_488_);
        crate::leanh::lean_closure_set(v___x_504_, 1, v_n_489_);
        crate::leanh::lean_closure_set(v___x_504_, 2, v_f_490_);
        crate::leanh::lean_closure_set(v___x_504_, 3, v_n_500_);
        v___x_505_ = crate::leanh::lean_apply_4(
            v_toBind_494_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_503_,
            v___x_504_,
        );
        return v___x_505_;
    }
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_foldM_loop(
    mut v_00_u03b1_506_: *mut crate::leanh::LeanObject,
    mut v_m_507_: *mut crate::leanh::LeanObject,
    mut v_inst_508_: *mut crate::leanh::LeanObject,
    mut v_n_509_: *mut crate::leanh::LeanObject,
    mut v_f_510_: *mut crate::leanh::LeanObject,
    mut v_i_511_: *mut crate::leanh::LeanObject,
    mut v_a_512_: *mut crate::leanh::LeanObject,
    mut v_a_513_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_514_ = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___redArg(
        v_inst_508_,
        v_n_509_,
        v_f_510_,
        v_i_511_,
        v_a_513_,
    );
    return v___x_514_;
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___boxed(
    mut v_00_u03b1_515_: *mut crate::leanh::LeanObject,
    mut v_m_516_: *mut crate::leanh::LeanObject,
    mut v_inst_517_: *mut crate::leanh::LeanObject,
    mut v_n_518_: *mut crate::leanh::LeanObject,
    mut v_f_519_: *mut crate::leanh::LeanObject,
    mut v_i_520_: *mut crate::leanh::LeanObject,
    mut v_a_521_: *mut crate::leanh::LeanObject,
    mut v_a_522_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_523_ = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop(
        v_00_u03b1_515_,
        v_m_516_,
        v_inst_517_,
        v_n_518_,
        v_f_519_,
        v_i_520_,
        v_a_521_,
        v_a_522_,
    );
    crate::leanh::lean_dec(v_i_520_);
    return v_res_523_;
}
pub unsafe fn l_Nat_foldM___redArg(
    mut v_inst_524_: *mut crate::leanh::LeanObject,
    mut v_n_525_: *mut crate::leanh::LeanObject,
    mut v_f_526_: *mut crate::leanh::LeanObject,
    mut v_init_527_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_n_525_);
    v___x_528_ = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___redArg(
        v_inst_524_,
        v_n_525_,
        v_f_526_,
        v_n_525_,
        v_init_527_,
    );
    crate::leanh::lean_dec(v_n_525_);
    return v___x_528_;
}
pub unsafe fn l_Nat_foldM(
    mut v_00_u03b1_529_: *mut crate::leanh::LeanObject,
    mut v_m_530_: *mut crate::leanh::LeanObject,
    mut v_inst_531_: *mut crate::leanh::LeanObject,
    mut v_n_532_: *mut crate::leanh::LeanObject,
    mut v_f_533_: *mut crate::leanh::LeanObject,
    mut v_init_534_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_n_532_);
    v___x_535_ = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___redArg(
        v_inst_531_,
        v_n_532_,
        v_f_533_,
        v_n_532_,
        v_init_534_,
    );
    crate::leanh::lean_dec(v_n_532_);
    return v___x_535_;
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___redArg___boxed(
    mut v_inst_536_: *mut crate::leanh::LeanObject,
    mut v_f_537_: *mut crate::leanh::LeanObject,
    mut v_i_538_: *mut crate::leanh::LeanObject,
    mut v_a_539_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_540_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___redArg(
        v_inst_536_,
        v_f_537_,
        v_i_538_,
        v_a_539_,
    );
    crate::leanh::lean_dec(v_i_538_);
    return v_res_540_;
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___redArg(
    mut v_inst_541_: *mut crate::leanh::LeanObject,
    mut v_f_542_: *mut crate::leanh::LeanObject,
    mut v_i_543_: *mut crate::leanh::LeanObject,
    mut v_a_544_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zero_548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_549_: u8 = 0;
    v_toApplicative_545_ = crate::leanh::lean_ctor_get(v_inst_541_, 0);
    v_toBind_546_ = crate::leanh::lean_ctor_get(v_inst_541_, 1);
    crate::leanh::lean_inc(v_toBind_546_);
    v_toPure_547_ = crate::leanh::lean_ctor_get(v_toApplicative_545_, 1);
    v_zero_548_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_549_ = lean_nat_dec_eq(v_i_543_, v_zero_548_);
    if v_isZero_549_ == 1 {
        let mut v___x_550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc(v_toPure_547_);
        crate::leanh::lean_dec(v_toBind_546_);
        crate::leanh::lean_dec(v_f_542_);
        crate::leanh::lean_dec_ref(v_inst_541_);
        v___x_550_ = crate::leanh::lean_apply_2(v_toPure_547_, crate::leanh::lean_box(0), v_a_544_);
        return v___x_550_;
    } else {
        let mut v_one_551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_one_551_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_552_ = lean_nat_sub(v_i_543_, v_one_551_);
        crate::leanh::lean_inc(v_f_542_);
        crate::leanh::lean_inc(v_n_552_);
        v___x_553_ =
            crate::leanh::lean_apply_3(v_f_542_, v_n_552_, crate::leanh::lean_box(0), v_a_544_);
        v___x_554_ = crate::leanh::lean_alloc_closure(
            l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___redArg___boxed
                as *mut core::ffi::c_void,
            4,
            3,
        );
        crate::leanh::lean_closure_set(v___x_554_, 0, v_inst_541_);
        crate::leanh::lean_closure_set(v___x_554_, 1, v_f_542_);
        crate::leanh::lean_closure_set(v___x_554_, 2, v_n_552_);
        v___x_555_ = crate::leanh::lean_apply_4(
            v_toBind_546_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_553_,
            v___x_554_,
        );
        return v___x_555_;
    }
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop(
    mut v_00_u03b1_556_: *mut crate::leanh::LeanObject,
    mut v_m_557_: *mut crate::leanh::LeanObject,
    mut v_inst_558_: *mut crate::leanh::LeanObject,
    mut v_n_559_: *mut crate::leanh::LeanObject,
    mut v_f_560_: *mut crate::leanh::LeanObject,
    mut v_i_561_: *mut crate::leanh::LeanObject,
    mut v_a_562_: *mut crate::leanh::LeanObject,
    mut v_a_563_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_564_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___redArg(
        v_inst_558_,
        v_f_560_,
        v_i_561_,
        v_a_563_,
    );
    return v___x_564_;
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___boxed(
    mut v_00_u03b1_565_: *mut crate::leanh::LeanObject,
    mut v_m_566_: *mut crate::leanh::LeanObject,
    mut v_inst_567_: *mut crate::leanh::LeanObject,
    mut v_n_568_: *mut crate::leanh::LeanObject,
    mut v_f_569_: *mut crate::leanh::LeanObject,
    mut v_i_570_: *mut crate::leanh::LeanObject,
    mut v_a_571_: *mut crate::leanh::LeanObject,
    mut v_a_572_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_573_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop(
        v_00_u03b1_565_,
        v_m_566_,
        v_inst_567_,
        v_n_568_,
        v_f_569_,
        v_i_570_,
        v_a_571_,
        v_a_572_,
    );
    crate::leanh::lean_dec(v_i_570_);
    crate::leanh::lean_dec(v_n_568_);
    return v_res_573_;
}
pub unsafe fn l_Nat_foldRevM___redArg(
    mut v_inst_574_: *mut crate::leanh::LeanObject,
    mut v_n_575_: *mut crate::leanh::LeanObject,
    mut v_f_576_: *mut crate::leanh::LeanObject,
    mut v_init_577_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_578_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___redArg(
        v_inst_574_,
        v_f_576_,
        v_n_575_,
        v_init_577_,
    );
    return v___x_578_;
}
pub unsafe fn l_Nat_foldRevM___redArg___boxed(
    mut v_inst_579_: *mut crate::leanh::LeanObject,
    mut v_n_580_: *mut crate::leanh::LeanObject,
    mut v_f_581_: *mut crate::leanh::LeanObject,
    mut v_init_582_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_583_ = l_Nat_foldRevM___redArg(v_inst_579_, v_n_580_, v_f_581_, v_init_582_);
    crate::leanh::lean_dec(v_n_580_);
    return v_res_583_;
}
pub unsafe fn l_Nat_foldRevM(
    mut v_00_u03b1_584_: *mut crate::leanh::LeanObject,
    mut v_m_585_: *mut crate::leanh::LeanObject,
    mut v_inst_586_: *mut crate::leanh::LeanObject,
    mut v_n_587_: *mut crate::leanh::LeanObject,
    mut v_f_588_: *mut crate::leanh::LeanObject,
    mut v_init_589_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_590_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___redArg(
        v_inst_586_,
        v_f_588_,
        v_n_587_,
        v_init_589_,
    );
    return v___x_590_;
}
pub unsafe fn l_Nat_foldRevM___boxed(
    mut v_00_u03b1_591_: *mut crate::leanh::LeanObject,
    mut v_m_592_: *mut crate::leanh::LeanObject,
    mut v_inst_593_: *mut crate::leanh::LeanObject,
    mut v_n_594_: *mut crate::leanh::LeanObject,
    mut v_f_595_: *mut crate::leanh::LeanObject,
    mut v_init_596_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_597_ = l_Nat_foldRevM(
        v_00_u03b1_591_,
        v_m_592_,
        v_inst_593_,
        v_n_594_,
        v_f_595_,
        v_init_596_,
    );
    crate::leanh::lean_dec(v_n_594_);
    return v_res_597_;
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_allM_loop___redArg___lam__0___boxed(
    mut v_toPure_598_: *mut crate::leanh::LeanObject,
    mut v_inst_599_: *mut crate::leanh::LeanObject,
    mut v_n_600_: *mut crate::leanh::LeanObject,
    mut v_p_601_: *mut crate::leanh::LeanObject,
    mut v_n_602_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_603_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_____do__lift_114__boxed_604_: u8 = 0;
    let mut v_res_605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_114__boxed_604_ = (crate::leanh::lean_unbox(v_____do__lift_603_) as u8);
    v_res_605_ = l___private_Init_Data_Nat_Control_0__Nat_allM_loop___redArg___lam__0(
        v_toPure_598_,
        v_inst_599_,
        v_n_600_,
        v_p_601_,
        v_n_602_,
        v_____do__lift_114__boxed_604_,
    );
    crate::leanh::lean_dec(v_n_602_);
    return v_res_605_;
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_allM_loop___redArg(
    mut v_inst_606_: *mut crate::leanh::LeanObject,
    mut v_n_607_: *mut crate::leanh::LeanObject,
    mut v_p_608_: *mut crate::leanh::LeanObject,
    mut v_i_609_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zero_613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_614_: u8 = 0;
    v_toApplicative_610_ = crate::leanh::lean_ctor_get(v_inst_606_, 0);
    v_toBind_611_ = crate::leanh::lean_ctor_get(v_inst_606_, 1);
    crate::leanh::lean_inc(v_toBind_611_);
    v_toPure_612_ = crate::leanh::lean_ctor_get(v_toApplicative_610_, 1);
    crate::leanh::lean_inc(v_toPure_612_);
    v_zero_613_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_614_ = lean_nat_dec_eq(v_i_609_, v_zero_613_);
    if v_isZero_614_ == 1 {
        let mut v___x_615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toBind_611_);
        crate::leanh::lean_dec(v_p_608_);
        crate::leanh::lean_dec(v_n_607_);
        crate::leanh::lean_dec_ref(v_inst_606_);
        v___x_615_ = crate::leanh::lean_box((v_isZero_614_) as usize);
        v___x_616_ =
            crate::leanh::lean_apply_2(v_toPure_612_, crate::leanh::lean_box(0), v___x_615_);
        return v___x_616_;
    } else {
        let mut v_one_617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_one_617_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_618_ = lean_nat_sub(v_i_609_, v_one_617_);
        crate::leanh::lean_inc(v_n_618_);
        crate::leanh::lean_inc(v_p_608_);
        crate::leanh::lean_inc(v_n_607_);
        v___f_619_ = crate::leanh::lean_alloc_closure(
            l___private_Init_Data_Nat_Control_0__Nat_allM_loop___redArg___lam__0___boxed
                as *mut core::ffi::c_void,
            6,
            5,
        );
        crate::leanh::lean_closure_set(v___f_619_, 0, v_toPure_612_);
        crate::leanh::lean_closure_set(v___f_619_, 1, v_inst_606_);
        crate::leanh::lean_closure_set(v___f_619_, 2, v_n_607_);
        crate::leanh::lean_closure_set(v___f_619_, 3, v_p_608_);
        crate::leanh::lean_closure_set(v___f_619_, 4, v_n_618_);
        v___x_620_ = lean_nat_sub(v_n_607_, v_n_618_);
        crate::leanh::lean_dec(v_n_618_);
        crate::leanh::lean_dec(v_n_607_);
        v___x_621_ = lean_nat_sub(v___x_620_, v_one_617_);
        crate::leanh::lean_dec(v___x_620_);
        v___x_622_ = crate::leanh::lean_apply_2(v_p_608_, v___x_621_, crate::leanh::lean_box(0));
        v___x_623_ = crate::leanh::lean_apply_4(
            v_toBind_611_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_622_,
            v___f_619_,
        );
        return v___x_623_;
    }
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_allM_loop___redArg___lam__0(
    mut v_toPure_624_: *mut crate::leanh::LeanObject,
    mut v_inst_625_: *mut crate::leanh::LeanObject,
    mut v_n_626_: *mut crate::leanh::LeanObject,
    mut v_p_627_: *mut crate::leanh::LeanObject,
    mut v_n_628_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_629_: u8,
) -> *mut crate::leanh::LeanObject {
    if v_____do__lift_629_ == 0 {
        let mut v___x_630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_p_627_);
        crate::leanh::lean_dec(v_n_626_);
        crate::leanh::lean_dec_ref(v_inst_625_);
        v___x_630_ = crate::leanh::lean_box((v_____do__lift_629_) as usize);
        v___x_631_ =
            crate::leanh::lean_apply_2(v_toPure_624_, crate::leanh::lean_box(0), v___x_630_);
        return v___x_631_;
    } else {
        let mut v___x_632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_624_);
        v___x_632_ = l___private_Init_Data_Nat_Control_0__Nat_allM_loop___redArg(
            v_inst_625_,
            v_n_626_,
            v_p_627_,
            v_n_628_,
        );
        return v___x_632_;
    }
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_allM_loop___redArg___boxed(
    mut v_inst_633_: *mut crate::leanh::LeanObject,
    mut v_n_634_: *mut crate::leanh::LeanObject,
    mut v_p_635_: *mut crate::leanh::LeanObject,
    mut v_i_636_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_637_ = l___private_Init_Data_Nat_Control_0__Nat_allM_loop___redArg(
        v_inst_633_,
        v_n_634_,
        v_p_635_,
        v_i_636_,
    );
    crate::leanh::lean_dec(v_i_636_);
    return v_res_637_;
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_allM_loop(
    mut v_m_638_: *mut crate::leanh::LeanObject,
    mut v_inst_639_: *mut crate::leanh::LeanObject,
    mut v_n_640_: *mut crate::leanh::LeanObject,
    mut v_p_641_: *mut crate::leanh::LeanObject,
    mut v_i_642_: *mut crate::leanh::LeanObject,
    mut v_a_643_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_644_ = l___private_Init_Data_Nat_Control_0__Nat_allM_loop___redArg(
        v_inst_639_,
        v_n_640_,
        v_p_641_,
        v_i_642_,
    );
    return v___x_644_;
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_allM_loop___boxed(
    mut v_m_645_: *mut crate::leanh::LeanObject,
    mut v_inst_646_: *mut crate::leanh::LeanObject,
    mut v_n_647_: *mut crate::leanh::LeanObject,
    mut v_p_648_: *mut crate::leanh::LeanObject,
    mut v_i_649_: *mut crate::leanh::LeanObject,
    mut v_a_650_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_651_ = l___private_Init_Data_Nat_Control_0__Nat_allM_loop(
        v_m_645_,
        v_inst_646_,
        v_n_647_,
        v_p_648_,
        v_i_649_,
        v_a_650_,
    );
    crate::leanh::lean_dec(v_i_649_);
    return v_res_651_;
}
pub unsafe fn l_Nat_allM___redArg(
    mut v_inst_652_: *mut crate::leanh::LeanObject,
    mut v_n_653_: *mut crate::leanh::LeanObject,
    mut v_p_654_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_n_653_);
    v___x_655_ = l___private_Init_Data_Nat_Control_0__Nat_allM_loop___redArg(
        v_inst_652_,
        v_n_653_,
        v_p_654_,
        v_n_653_,
    );
    crate::leanh::lean_dec(v_n_653_);
    return v___x_655_;
}
pub unsafe fn l_Nat_allM(
    mut v_m_656_: *mut crate::leanh::LeanObject,
    mut v_inst_657_: *mut crate::leanh::LeanObject,
    mut v_n_658_: *mut crate::leanh::LeanObject,
    mut v_p_659_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_n_658_);
    v___x_660_ = l___private_Init_Data_Nat_Control_0__Nat_allM_loop___redArg(
        v_inst_657_,
        v_n_658_,
        v_p_659_,
        v_n_658_,
    );
    crate::leanh::lean_dec(v_n_658_);
    return v___x_660_;
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_anyM_loop___redArg___lam__0___boxed(
    mut v_inst_661_: *mut crate::leanh::LeanObject,
    mut v_n_662_: *mut crate::leanh::LeanObject,
    mut v_p_663_: *mut crate::leanh::LeanObject,
    mut v_n_664_: *mut crate::leanh::LeanObject,
    mut v_toPure_665_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_666_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_____do__lift_114__boxed_667_: u8 = 0;
    let mut v_res_668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_114__boxed_667_ = (crate::leanh::lean_unbox(v_____do__lift_666_) as u8);
    v_res_668_ = l___private_Init_Data_Nat_Control_0__Nat_anyM_loop___redArg___lam__0(
        v_inst_661_,
        v_n_662_,
        v_p_663_,
        v_n_664_,
        v_toPure_665_,
        v_____do__lift_114__boxed_667_,
    );
    crate::leanh::lean_dec(v_n_664_);
    return v_res_668_;
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_anyM_loop___redArg(
    mut v_inst_669_: *mut crate::leanh::LeanObject,
    mut v_n_670_: *mut crate::leanh::LeanObject,
    mut v_p_671_: *mut crate::leanh::LeanObject,
    mut v_i_672_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zero_676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_677_: u8 = 0;
    v_toApplicative_673_ = crate::leanh::lean_ctor_get(v_inst_669_, 0);
    v_toBind_674_ = crate::leanh::lean_ctor_get(v_inst_669_, 1);
    crate::leanh::lean_inc(v_toBind_674_);
    v_toPure_675_ = crate::leanh::lean_ctor_get(v_toApplicative_673_, 1);
    crate::leanh::lean_inc(v_toPure_675_);
    v_zero_676_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_677_ = lean_nat_dec_eq(v_i_672_, v_zero_676_);
    if v_isZero_677_ == 1 {
        let mut v___x_678_: u8 = 0;
        let mut v___x_679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toBind_674_);
        crate::leanh::lean_dec(v_p_671_);
        crate::leanh::lean_dec(v_n_670_);
        crate::leanh::lean_dec_ref(v_inst_669_);
        v___x_678_ = 0;
        v___x_679_ = crate::leanh::lean_box((v___x_678_) as usize);
        v___x_680_ =
            crate::leanh::lean_apply_2(v_toPure_675_, crate::leanh::lean_box(0), v___x_679_);
        return v___x_680_;
    } else {
        let mut v_one_681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_one_681_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_682_ = lean_nat_sub(v_i_672_, v_one_681_);
        crate::leanh::lean_inc(v_n_682_);
        crate::leanh::lean_inc(v_p_671_);
        crate::leanh::lean_inc(v_n_670_);
        v___f_683_ = crate::leanh::lean_alloc_closure(
            l___private_Init_Data_Nat_Control_0__Nat_anyM_loop___redArg___lam__0___boxed
                as *mut core::ffi::c_void,
            6,
            5,
        );
        crate::leanh::lean_closure_set(v___f_683_, 0, v_inst_669_);
        crate::leanh::lean_closure_set(v___f_683_, 1, v_n_670_);
        crate::leanh::lean_closure_set(v___f_683_, 2, v_p_671_);
        crate::leanh::lean_closure_set(v___f_683_, 3, v_n_682_);
        crate::leanh::lean_closure_set(v___f_683_, 4, v_toPure_675_);
        v___x_684_ = lean_nat_sub(v_n_670_, v_n_682_);
        crate::leanh::lean_dec(v_n_682_);
        crate::leanh::lean_dec(v_n_670_);
        v___x_685_ = lean_nat_sub(v___x_684_, v_one_681_);
        crate::leanh::lean_dec(v___x_684_);
        v___x_686_ = crate::leanh::lean_apply_2(v_p_671_, v___x_685_, crate::leanh::lean_box(0));
        v___x_687_ = crate::leanh::lean_apply_4(
            v_toBind_674_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_686_,
            v___f_683_,
        );
        return v___x_687_;
    }
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_anyM_loop___redArg___lam__0(
    mut v_inst_688_: *mut crate::leanh::LeanObject,
    mut v_n_689_: *mut crate::leanh::LeanObject,
    mut v_p_690_: *mut crate::leanh::LeanObject,
    mut v_n_691_: *mut crate::leanh::LeanObject,
    mut v_toPure_692_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_693_: u8,
) -> *mut crate::leanh::LeanObject {
    if v_____do__lift_693_ == 0 {
        let mut v___x_694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_692_);
        v___x_694_ = l___private_Init_Data_Nat_Control_0__Nat_anyM_loop___redArg(
            v_inst_688_,
            v_n_689_,
            v_p_690_,
            v_n_691_,
        );
        return v___x_694_;
    } else {
        let mut v___x_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_p_690_);
        crate::leanh::lean_dec(v_n_689_);
        crate::leanh::lean_dec_ref(v_inst_688_);
        v___x_695_ = crate::leanh::lean_box((v_____do__lift_693_) as usize);
        v___x_696_ =
            crate::leanh::lean_apply_2(v_toPure_692_, crate::leanh::lean_box(0), v___x_695_);
        return v___x_696_;
    }
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_anyM_loop___redArg___boxed(
    mut v_inst_697_: *mut crate::leanh::LeanObject,
    mut v_n_698_: *mut crate::leanh::LeanObject,
    mut v_p_699_: *mut crate::leanh::LeanObject,
    mut v_i_700_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_701_ = l___private_Init_Data_Nat_Control_0__Nat_anyM_loop___redArg(
        v_inst_697_,
        v_n_698_,
        v_p_699_,
        v_i_700_,
    );
    crate::leanh::lean_dec(v_i_700_);
    return v_res_701_;
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_anyM_loop(
    mut v_m_702_: *mut crate::leanh::LeanObject,
    mut v_inst_703_: *mut crate::leanh::LeanObject,
    mut v_n_704_: *mut crate::leanh::LeanObject,
    mut v_p_705_: *mut crate::leanh::LeanObject,
    mut v_i_706_: *mut crate::leanh::LeanObject,
    mut v_a_707_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_708_ = l___private_Init_Data_Nat_Control_0__Nat_anyM_loop___redArg(
        v_inst_703_,
        v_n_704_,
        v_p_705_,
        v_i_706_,
    );
    return v___x_708_;
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_anyM_loop___boxed(
    mut v_m_709_: *mut crate::leanh::LeanObject,
    mut v_inst_710_: *mut crate::leanh::LeanObject,
    mut v_n_711_: *mut crate::leanh::LeanObject,
    mut v_p_712_: *mut crate::leanh::LeanObject,
    mut v_i_713_: *mut crate::leanh::LeanObject,
    mut v_a_714_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_715_ = l___private_Init_Data_Nat_Control_0__Nat_anyM_loop(
        v_m_709_,
        v_inst_710_,
        v_n_711_,
        v_p_712_,
        v_i_713_,
        v_a_714_,
    );
    crate::leanh::lean_dec(v_i_713_);
    return v_res_715_;
}
pub unsafe fn l_Nat_anyM___redArg(
    mut v_inst_716_: *mut crate::leanh::LeanObject,
    mut v_n_717_: *mut crate::leanh::LeanObject,
    mut v_p_718_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_n_717_);
    v___x_719_ = l___private_Init_Data_Nat_Control_0__Nat_anyM_loop___redArg(
        v_inst_716_,
        v_n_717_,
        v_p_718_,
        v_n_717_,
    );
    crate::leanh::lean_dec(v_n_717_);
    return v___x_719_;
}
pub unsafe fn l_Nat_anyM(
    mut v_m_720_: *mut crate::leanh::LeanObject,
    mut v_inst_721_: *mut crate::leanh::LeanObject,
    mut v_n_722_: *mut crate::leanh::LeanObject,
    mut v_p_723_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_n_722_);
    v___x_724_ = l___private_Init_Data_Nat_Control_0__Nat_anyM_loop___redArg(
        v_inst_721_,
        v_n_722_,
        v_p_723_,
        v_n_722_,
    );
    crate::leanh::lean_dec(v_n_722_);
    return v___x_724_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Nat_Control(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Notation(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Nat_Control(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Nat_Control(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Notation(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Control(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Nat_Control(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Nat_Control(builtin);
}
