// Lean compiler output
// Module: Init.Data.Nat.Control
// Imports: Init.Notation Init.Omega
use crate::r#gen::Init::Notation::{initialize_Init_Notation, runtime_initialize_Init_Notation};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::lean_imports_rs::Init::Prelude::{lean_nat_dec_eq, lean_nat_sub};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_apply_2, lean_apply_3, lean_apply_4,
    lean_box, lean_closure_set, lean_ctor_get, lean_dec, lean_dec_ref, lean_inc,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_unbox, lean_unsigned_to_nat,
};
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_forM_loop___redArg___lam__0___boxed(
    mut v_inst_363_: *mut LeanObject,
    mut v_n_364_: *mut LeanObject,
    mut v_f_365_: *mut LeanObject,
    mut v_n_366_: *mut LeanObject,
    mut v_____r_367_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_368_: *mut LeanObject = core::ptr::null_mut();
    v_res_368_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___redArg___lam__0(
        v_inst_363_,
        v_n_364_,
        v_f_365_,
        v_n_366_,
        v_____r_367_,
    );
    lean_dec(v_n_366_);
    return v_res_368_;
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_forM_loop___redArg(
    mut v_inst_369_: *mut LeanObject,
    mut v_n_370_: *mut LeanObject,
    mut v_f_371_: *mut LeanObject,
    mut v_i_372_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zero_376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_377_: u8 = 0;
    v_toApplicative_373_ = lean_ctor_get(v_inst_369_, 0);
    v_toBind_374_ = lean_ctor_get(v_inst_369_, 1);
    lean_inc(v_toBind_374_);
    v_toPure_375_ = lean_ctor_get(v_toApplicative_373_, 1);
    v_zero_376_ = lean_unsigned_to_nat(0);
    v_isZero_377_ = lean_nat_dec_eq(v_i_372_, v_zero_376_);
    if v_isZero_377_ == 1 {
        let mut v___x_378_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_379_: *mut LeanObject = core::ptr::null_mut();
        lean_inc(v_toPure_375_);
        lean_dec(v_toBind_374_);
        lean_dec(v_f_371_);
        lean_dec(v_n_370_);
        lean_dec_ref(v_inst_369_);
        v___x_378_ = lean_box(0);
        v___x_379_ = lean_apply_2(v_toPure_375_, lean_box(0), v___x_378_);
        return v___x_379_;
    } else {
        let mut v_one_380_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_381_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_382_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_383_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_384_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_385_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_386_: *mut LeanObject = core::ptr::null_mut();
        v_one_380_ = lean_unsigned_to_nat(1);
        v_n_381_ = lean_nat_sub(v_i_372_, v_one_380_);
        lean_inc(v_n_381_);
        lean_inc(v_f_371_);
        lean_inc(v_n_370_);
        v___f_382_ = lean_alloc_closure(
            l___private_Init_Data_Nat_Control_0__Nat_forM_loop___redArg___lam__0___boxed
                as *mut core::ffi::c_void,
            5,
            4,
        );
        lean_closure_set(v___f_382_, 0, v_inst_369_);
        lean_closure_set(v___f_382_, 1, v_n_370_);
        lean_closure_set(v___f_382_, 2, v_f_371_);
        lean_closure_set(v___f_382_, 3, v_n_381_);
        v___x_383_ = lean_nat_sub(v_n_370_, v_n_381_);
        lean_dec(v_n_381_);
        lean_dec(v_n_370_);
        v___x_384_ = lean_nat_sub(v___x_383_, v_one_380_);
        lean_dec(v___x_383_);
        v___x_385_ = lean_apply_2(v_f_371_, v___x_384_, lean_box(0));
        v___x_386_ = lean_apply_4(
            v_toBind_374_,
            lean_box(0),
            lean_box(0),
            v___x_385_,
            v___f_382_,
        );
        return v___x_386_;
    }
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_forM_loop___redArg___lam__0(
    mut v_inst_387_: *mut LeanObject,
    mut v_n_388_: *mut LeanObject,
    mut v_f_389_: *mut LeanObject,
    mut v_n_390_: *mut LeanObject,
    mut v_____r_391_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_392_: *mut LeanObject = core::ptr::null_mut();
    v___x_392_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___redArg(
        v_inst_387_,
        v_n_388_,
        v_f_389_,
        v_n_390_,
    );
    return v___x_392_;
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_forM_loop___redArg___boxed(
    mut v_inst_393_: *mut LeanObject,
    mut v_n_394_: *mut LeanObject,
    mut v_f_395_: *mut LeanObject,
    mut v_i_396_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_397_: *mut LeanObject = core::ptr::null_mut();
    v_res_397_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___redArg(
        v_inst_393_,
        v_n_394_,
        v_f_395_,
        v_i_396_,
    );
    lean_dec(v_i_396_);
    return v_res_397_;
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_forM_loop(
    mut v_m_398_: *mut LeanObject,
    mut v_inst_399_: *mut LeanObject,
    mut v_n_400_: *mut LeanObject,
    mut v_f_401_: *mut LeanObject,
    mut v_i_402_: *mut LeanObject,
    mut v_a_403_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_404_: *mut LeanObject = core::ptr::null_mut();
    v___x_404_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___redArg(
        v_inst_399_,
        v_n_400_,
        v_f_401_,
        v_i_402_,
    );
    return v___x_404_;
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_forM_loop___boxed(
    mut v_m_405_: *mut LeanObject,
    mut v_inst_406_: *mut LeanObject,
    mut v_n_407_: *mut LeanObject,
    mut v_f_408_: *mut LeanObject,
    mut v_i_409_: *mut LeanObject,
    mut v_a_410_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_411_: *mut LeanObject = core::ptr::null_mut();
    v_res_411_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop(
        v_m_405_,
        v_inst_406_,
        v_n_407_,
        v_f_408_,
        v_i_409_,
        v_a_410_,
    );
    lean_dec(v_i_409_);
    return v_res_411_;
}
pub unsafe fn l_Nat_forM___redArg(
    mut v_inst_412_: *mut LeanObject,
    mut v_n_413_: *mut LeanObject,
    mut v_f_414_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_415_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_n_413_);
    v___x_415_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___redArg(
        v_inst_412_,
        v_n_413_,
        v_f_414_,
        v_n_413_,
    );
    lean_dec(v_n_413_);
    return v___x_415_;
}
pub unsafe fn l_Nat_forM(
    mut v_m_416_: *mut LeanObject,
    mut v_inst_417_: *mut LeanObject,
    mut v_n_418_: *mut LeanObject,
    mut v_f_419_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_420_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_n_418_);
    v___x_420_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___redArg(
        v_inst_417_,
        v_n_418_,
        v_f_419_,
        v_n_418_,
    );
    lean_dec(v_n_418_);
    return v___x_420_;
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_forRevM_loop___redArg___lam__0___boxed(
    mut v_inst_421_: *mut LeanObject,
    mut v_f_422_: *mut LeanObject,
    mut v_n_423_: *mut LeanObject,
    mut v_____r_424_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_425_: *mut LeanObject = core::ptr::null_mut();
    v_res_425_ = l___private_Init_Data_Nat_Control_0__Nat_forRevM_loop___redArg___lam__0(
        v_inst_421_,
        v_f_422_,
        v_n_423_,
        v_____r_424_,
    );
    lean_dec(v_n_423_);
    return v_res_425_;
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_forRevM_loop___redArg(
    mut v_inst_426_: *mut LeanObject,
    mut v_f_427_: *mut LeanObject,
    mut v_i_428_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zero_432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_433_: u8 = 0;
    v_toApplicative_429_ = lean_ctor_get(v_inst_426_, 0);
    v_toBind_430_ = lean_ctor_get(v_inst_426_, 1);
    lean_inc(v_toBind_430_);
    v_toPure_431_ = lean_ctor_get(v_toApplicative_429_, 1);
    v_zero_432_ = lean_unsigned_to_nat(0);
    v_isZero_433_ = lean_nat_dec_eq(v_i_428_, v_zero_432_);
    if v_isZero_433_ == 1 {
        let mut v___x_434_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_435_: *mut LeanObject = core::ptr::null_mut();
        lean_inc(v_toPure_431_);
        lean_dec(v_toBind_430_);
        lean_dec(v_f_427_);
        lean_dec_ref(v_inst_426_);
        v___x_434_ = lean_box(0);
        v___x_435_ = lean_apply_2(v_toPure_431_, lean_box(0), v___x_434_);
        return v___x_435_;
    } else {
        let mut v_one_436_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_437_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_438_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_439_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_440_: *mut LeanObject = core::ptr::null_mut();
        v_one_436_ = lean_unsigned_to_nat(1);
        v_n_437_ = lean_nat_sub(v_i_428_, v_one_436_);
        lean_inc(v_n_437_);
        lean_inc(v_f_427_);
        v___f_438_ = lean_alloc_closure(
            l___private_Init_Data_Nat_Control_0__Nat_forRevM_loop___redArg___lam__0___boxed
                as *mut core::ffi::c_void,
            4,
            3,
        );
        lean_closure_set(v___f_438_, 0, v_inst_426_);
        lean_closure_set(v___f_438_, 1, v_f_427_);
        lean_closure_set(v___f_438_, 2, v_n_437_);
        v___x_439_ = lean_apply_2(v_f_427_, v_n_437_, lean_box(0));
        v___x_440_ = lean_apply_4(
            v_toBind_430_,
            lean_box(0),
            lean_box(0),
            v___x_439_,
            v___f_438_,
        );
        return v___x_440_;
    }
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_forRevM_loop___redArg___lam__0(
    mut v_inst_441_: *mut LeanObject,
    mut v_f_442_: *mut LeanObject,
    mut v_n_443_: *mut LeanObject,
    mut v_____r_444_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_445_: *mut LeanObject = core::ptr::null_mut();
    v___x_445_ = l___private_Init_Data_Nat_Control_0__Nat_forRevM_loop___redArg(
        v_inst_441_,
        v_f_442_,
        v_n_443_,
    );
    return v___x_445_;
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_forRevM_loop___redArg___boxed(
    mut v_inst_446_: *mut LeanObject,
    mut v_f_447_: *mut LeanObject,
    mut v_i_448_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_449_: *mut LeanObject = core::ptr::null_mut();
    v_res_449_ = l___private_Init_Data_Nat_Control_0__Nat_forRevM_loop___redArg(
        v_inst_446_,
        v_f_447_,
        v_i_448_,
    );
    lean_dec(v_i_448_);
    return v_res_449_;
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_forRevM_loop(
    mut v_m_450_: *mut LeanObject,
    mut v_inst_451_: *mut LeanObject,
    mut v_n_452_: *mut LeanObject,
    mut v_f_453_: *mut LeanObject,
    mut v_i_454_: *mut LeanObject,
    mut v_a_455_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_456_: *mut LeanObject = core::ptr::null_mut();
    v___x_456_ = l___private_Init_Data_Nat_Control_0__Nat_forRevM_loop___redArg(
        v_inst_451_,
        v_f_453_,
        v_i_454_,
    );
    return v___x_456_;
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_forRevM_loop___boxed(
    mut v_m_457_: *mut LeanObject,
    mut v_inst_458_: *mut LeanObject,
    mut v_n_459_: *mut LeanObject,
    mut v_f_460_: *mut LeanObject,
    mut v_i_461_: *mut LeanObject,
    mut v_a_462_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_463_: *mut LeanObject = core::ptr::null_mut();
    v_res_463_ = l___private_Init_Data_Nat_Control_0__Nat_forRevM_loop(
        v_m_457_,
        v_inst_458_,
        v_n_459_,
        v_f_460_,
        v_i_461_,
        v_a_462_,
    );
    lean_dec(v_i_461_);
    lean_dec(v_n_459_);
    return v_res_463_;
}
pub unsafe fn l_Nat_forRevM___redArg(
    mut v_inst_464_: *mut LeanObject,
    mut v_n_465_: *mut LeanObject,
    mut v_f_466_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_467_: *mut LeanObject = core::ptr::null_mut();
    v___x_467_ = l___private_Init_Data_Nat_Control_0__Nat_forRevM_loop___redArg(
        v_inst_464_,
        v_f_466_,
        v_n_465_,
    );
    return v___x_467_;
}
pub unsafe fn l_Nat_forRevM___redArg___boxed(
    mut v_inst_468_: *mut LeanObject,
    mut v_n_469_: *mut LeanObject,
    mut v_f_470_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_471_: *mut LeanObject = core::ptr::null_mut();
    v_res_471_ = l_Nat_forRevM___redArg(v_inst_468_, v_n_469_, v_f_470_);
    lean_dec(v_n_469_);
    return v_res_471_;
}
pub unsafe fn l_Nat_forRevM(
    mut v_m_472_: *mut LeanObject,
    mut v_inst_473_: *mut LeanObject,
    mut v_n_474_: *mut LeanObject,
    mut v_f_475_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_476_: *mut LeanObject = core::ptr::null_mut();
    v___x_476_ = l___private_Init_Data_Nat_Control_0__Nat_forRevM_loop___redArg(
        v_inst_473_,
        v_f_475_,
        v_n_474_,
    );
    return v___x_476_;
}
pub unsafe fn l_Nat_forRevM___boxed(
    mut v_m_477_: *mut LeanObject,
    mut v_inst_478_: *mut LeanObject,
    mut v_n_479_: *mut LeanObject,
    mut v_f_480_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_481_: *mut LeanObject = core::ptr::null_mut();
    v_res_481_ = l_Nat_forRevM(v_m_477_, v_inst_478_, v_n_479_, v_f_480_);
    lean_dec(v_n_479_);
    return v_res_481_;
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___redArg___boxed(
    mut v_inst_482_: *mut LeanObject,
    mut v_n_483_: *mut LeanObject,
    mut v_f_484_: *mut LeanObject,
    mut v_i_485_: *mut LeanObject,
    mut v_a_486_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_487_: *mut LeanObject = core::ptr::null_mut();
    v_res_487_ = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___redArg(
        v_inst_482_,
        v_n_483_,
        v_f_484_,
        v_i_485_,
        v_a_486_,
    );
    lean_dec(v_i_485_);
    return v_res_487_;
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___redArg(
    mut v_inst_488_: *mut LeanObject,
    mut v_n_489_: *mut LeanObject,
    mut v_f_490_: *mut LeanObject,
    mut v_i_491_: *mut LeanObject,
    mut v_a_492_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zero_496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_497_: u8 = 0;
    v_toApplicative_493_ = lean_ctor_get(v_inst_488_, 0);
    v_toBind_494_ = lean_ctor_get(v_inst_488_, 1);
    lean_inc(v_toBind_494_);
    v_toPure_495_ = lean_ctor_get(v_toApplicative_493_, 1);
    v_zero_496_ = lean_unsigned_to_nat(0);
    v_isZero_497_ = lean_nat_dec_eq(v_i_491_, v_zero_496_);
    if v_isZero_497_ == 1 {
        let mut v___x_498_: *mut LeanObject = core::ptr::null_mut();
        lean_inc(v_toPure_495_);
        lean_dec(v_toBind_494_);
        lean_dec(v_f_490_);
        lean_dec(v_n_489_);
        lean_dec_ref(v_inst_488_);
        v___x_498_ = lean_apply_2(v_toPure_495_, lean_box(0), v_a_492_);
        return v___x_498_;
    } else {
        let mut v_one_499_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_500_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_501_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_502_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_503_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_504_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_505_: *mut LeanObject = core::ptr::null_mut();
        v_one_499_ = lean_unsigned_to_nat(1);
        v_n_500_ = lean_nat_sub(v_i_491_, v_one_499_);
        v___x_501_ = lean_nat_sub(v_n_489_, v_n_500_);
        v___x_502_ = lean_nat_sub(v___x_501_, v_one_499_);
        lean_dec(v___x_501_);
        lean_inc(v_f_490_);
        v___x_503_ = lean_apply_3(v_f_490_, v___x_502_, lean_box(0), v_a_492_);
        v___x_504_ = lean_alloc_closure(
            l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___redArg___boxed
                as *mut core::ffi::c_void,
            5,
            4,
        );
        lean_closure_set(v___x_504_, 0, v_inst_488_);
        lean_closure_set(v___x_504_, 1, v_n_489_);
        lean_closure_set(v___x_504_, 2, v_f_490_);
        lean_closure_set(v___x_504_, 3, v_n_500_);
        v___x_505_ = lean_apply_4(
            v_toBind_494_,
            lean_box(0),
            lean_box(0),
            v___x_503_,
            v___x_504_,
        );
        return v___x_505_;
    }
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_foldM_loop(
    mut v_00_u03b1_506_: *mut LeanObject,
    mut v_m_507_: *mut LeanObject,
    mut v_inst_508_: *mut LeanObject,
    mut v_n_509_: *mut LeanObject,
    mut v_f_510_: *mut LeanObject,
    mut v_i_511_: *mut LeanObject,
    mut v_a_512_: *mut LeanObject,
    mut v_a_513_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_514_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_515_: *mut LeanObject,
    mut v_m_516_: *mut LeanObject,
    mut v_inst_517_: *mut LeanObject,
    mut v_n_518_: *mut LeanObject,
    mut v_f_519_: *mut LeanObject,
    mut v_i_520_: *mut LeanObject,
    mut v_a_521_: *mut LeanObject,
    mut v_a_522_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_523_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_i_520_);
    return v_res_523_;
}
pub unsafe fn l_Nat_foldM___redArg(
    mut v_inst_524_: *mut LeanObject,
    mut v_n_525_: *mut LeanObject,
    mut v_f_526_: *mut LeanObject,
    mut v_init_527_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_528_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_n_525_);
    v___x_528_ = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___redArg(
        v_inst_524_,
        v_n_525_,
        v_f_526_,
        v_n_525_,
        v_init_527_,
    );
    lean_dec(v_n_525_);
    return v___x_528_;
}
pub unsafe fn l_Nat_foldM(
    mut v_00_u03b1_529_: *mut LeanObject,
    mut v_m_530_: *mut LeanObject,
    mut v_inst_531_: *mut LeanObject,
    mut v_n_532_: *mut LeanObject,
    mut v_f_533_: *mut LeanObject,
    mut v_init_534_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_535_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_n_532_);
    v___x_535_ = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___redArg(
        v_inst_531_,
        v_n_532_,
        v_f_533_,
        v_n_532_,
        v_init_534_,
    );
    lean_dec(v_n_532_);
    return v___x_535_;
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___redArg___boxed(
    mut v_inst_536_: *mut LeanObject,
    mut v_f_537_: *mut LeanObject,
    mut v_i_538_: *mut LeanObject,
    mut v_a_539_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_540_: *mut LeanObject = core::ptr::null_mut();
    v_res_540_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___redArg(
        v_inst_536_,
        v_f_537_,
        v_i_538_,
        v_a_539_,
    );
    lean_dec(v_i_538_);
    return v_res_540_;
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___redArg(
    mut v_inst_541_: *mut LeanObject,
    mut v_f_542_: *mut LeanObject,
    mut v_i_543_: *mut LeanObject,
    mut v_a_544_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zero_548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_549_: u8 = 0;
    v_toApplicative_545_ = lean_ctor_get(v_inst_541_, 0);
    v_toBind_546_ = lean_ctor_get(v_inst_541_, 1);
    lean_inc(v_toBind_546_);
    v_toPure_547_ = lean_ctor_get(v_toApplicative_545_, 1);
    v_zero_548_ = lean_unsigned_to_nat(0);
    v_isZero_549_ = lean_nat_dec_eq(v_i_543_, v_zero_548_);
    if v_isZero_549_ == 1 {
        let mut v___x_550_: *mut LeanObject = core::ptr::null_mut();
        lean_inc(v_toPure_547_);
        lean_dec(v_toBind_546_);
        lean_dec(v_f_542_);
        lean_dec_ref(v_inst_541_);
        v___x_550_ = lean_apply_2(v_toPure_547_, lean_box(0), v_a_544_);
        return v___x_550_;
    } else {
        let mut v_one_551_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_552_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_553_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_554_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_555_: *mut LeanObject = core::ptr::null_mut();
        v_one_551_ = lean_unsigned_to_nat(1);
        v_n_552_ = lean_nat_sub(v_i_543_, v_one_551_);
        lean_inc(v_f_542_);
        lean_inc(v_n_552_);
        v___x_553_ = lean_apply_3(v_f_542_, v_n_552_, lean_box(0), v_a_544_);
        v___x_554_ = lean_alloc_closure(
            l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___redArg___boxed
                as *mut core::ffi::c_void,
            4,
            3,
        );
        lean_closure_set(v___x_554_, 0, v_inst_541_);
        lean_closure_set(v___x_554_, 1, v_f_542_);
        lean_closure_set(v___x_554_, 2, v_n_552_);
        v___x_555_ = lean_apply_4(
            v_toBind_546_,
            lean_box(0),
            lean_box(0),
            v___x_553_,
            v___x_554_,
        );
        return v___x_555_;
    }
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop(
    mut v_00_u03b1_556_: *mut LeanObject,
    mut v_m_557_: *mut LeanObject,
    mut v_inst_558_: *mut LeanObject,
    mut v_n_559_: *mut LeanObject,
    mut v_f_560_: *mut LeanObject,
    mut v_i_561_: *mut LeanObject,
    mut v_a_562_: *mut LeanObject,
    mut v_a_563_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_564_: *mut LeanObject = core::ptr::null_mut();
    v___x_564_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___redArg(
        v_inst_558_,
        v_f_560_,
        v_i_561_,
        v_a_563_,
    );
    return v___x_564_;
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___boxed(
    mut v_00_u03b1_565_: *mut LeanObject,
    mut v_m_566_: *mut LeanObject,
    mut v_inst_567_: *mut LeanObject,
    mut v_n_568_: *mut LeanObject,
    mut v_f_569_: *mut LeanObject,
    mut v_i_570_: *mut LeanObject,
    mut v_a_571_: *mut LeanObject,
    mut v_a_572_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_573_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_i_570_);
    lean_dec(v_n_568_);
    return v_res_573_;
}
pub unsafe fn l_Nat_foldRevM___redArg(
    mut v_inst_574_: *mut LeanObject,
    mut v_n_575_: *mut LeanObject,
    mut v_f_576_: *mut LeanObject,
    mut v_init_577_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_578_: *mut LeanObject = core::ptr::null_mut();
    v___x_578_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___redArg(
        v_inst_574_,
        v_f_576_,
        v_n_575_,
        v_init_577_,
    );
    return v___x_578_;
}
pub unsafe fn l_Nat_foldRevM___redArg___boxed(
    mut v_inst_579_: *mut LeanObject,
    mut v_n_580_: *mut LeanObject,
    mut v_f_581_: *mut LeanObject,
    mut v_init_582_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_583_: *mut LeanObject = core::ptr::null_mut();
    v_res_583_ = l_Nat_foldRevM___redArg(v_inst_579_, v_n_580_, v_f_581_, v_init_582_);
    lean_dec(v_n_580_);
    return v_res_583_;
}
pub unsafe fn l_Nat_foldRevM(
    mut v_00_u03b1_584_: *mut LeanObject,
    mut v_m_585_: *mut LeanObject,
    mut v_inst_586_: *mut LeanObject,
    mut v_n_587_: *mut LeanObject,
    mut v_f_588_: *mut LeanObject,
    mut v_init_589_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_590_: *mut LeanObject = core::ptr::null_mut();
    v___x_590_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___redArg(
        v_inst_586_,
        v_f_588_,
        v_n_587_,
        v_init_589_,
    );
    return v___x_590_;
}
pub unsafe fn l_Nat_foldRevM___boxed(
    mut v_00_u03b1_591_: *mut LeanObject,
    mut v_m_592_: *mut LeanObject,
    mut v_inst_593_: *mut LeanObject,
    mut v_n_594_: *mut LeanObject,
    mut v_f_595_: *mut LeanObject,
    mut v_init_596_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_597_: *mut LeanObject = core::ptr::null_mut();
    v_res_597_ = l_Nat_foldRevM(
        v_00_u03b1_591_,
        v_m_592_,
        v_inst_593_,
        v_n_594_,
        v_f_595_,
        v_init_596_,
    );
    lean_dec(v_n_594_);
    return v_res_597_;
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_allM_loop___redArg___lam__0___boxed(
    mut v_toPure_598_: *mut LeanObject,
    mut v_inst_599_: *mut LeanObject,
    mut v_n_600_: *mut LeanObject,
    mut v_p_601_: *mut LeanObject,
    mut v_n_602_: *mut LeanObject,
    mut v_____do__lift_603_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____do__lift_114__boxed_604_: u8 = 0;
    let mut v_res_605_: *mut LeanObject = core::ptr::null_mut();
    v_____do__lift_114__boxed_604_ = (lean_unbox(v_____do__lift_603_) as u8);
    v_res_605_ = l___private_Init_Data_Nat_Control_0__Nat_allM_loop___redArg___lam__0(
        v_toPure_598_,
        v_inst_599_,
        v_n_600_,
        v_p_601_,
        v_n_602_,
        v_____do__lift_114__boxed_604_,
    );
    lean_dec(v_n_602_);
    return v_res_605_;
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_allM_loop___redArg(
    mut v_inst_606_: *mut LeanObject,
    mut v_n_607_: *mut LeanObject,
    mut v_p_608_: *mut LeanObject,
    mut v_i_609_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zero_613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_614_: u8 = 0;
    v_toApplicative_610_ = lean_ctor_get(v_inst_606_, 0);
    v_toBind_611_ = lean_ctor_get(v_inst_606_, 1);
    lean_inc(v_toBind_611_);
    v_toPure_612_ = lean_ctor_get(v_toApplicative_610_, 1);
    lean_inc(v_toPure_612_);
    v_zero_613_ = lean_unsigned_to_nat(0);
    v_isZero_614_ = lean_nat_dec_eq(v_i_609_, v_zero_613_);
    if v_isZero_614_ == 1 {
        let mut v___x_615_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_616_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toBind_611_);
        lean_dec(v_p_608_);
        lean_dec(v_n_607_);
        lean_dec_ref(v_inst_606_);
        v___x_615_ = lean_box((v_isZero_614_) as usize);
        v___x_616_ = lean_apply_2(v_toPure_612_, lean_box(0), v___x_615_);
        return v___x_616_;
    } else {
        let mut v_one_617_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_618_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_619_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_620_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_621_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_622_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_623_: *mut LeanObject = core::ptr::null_mut();
        v_one_617_ = lean_unsigned_to_nat(1);
        v_n_618_ = lean_nat_sub(v_i_609_, v_one_617_);
        lean_inc(v_n_618_);
        lean_inc(v_p_608_);
        lean_inc(v_n_607_);
        v___f_619_ = lean_alloc_closure(
            l___private_Init_Data_Nat_Control_0__Nat_allM_loop___redArg___lam__0___boxed
                as *mut core::ffi::c_void,
            6,
            5,
        );
        lean_closure_set(v___f_619_, 0, v_toPure_612_);
        lean_closure_set(v___f_619_, 1, v_inst_606_);
        lean_closure_set(v___f_619_, 2, v_n_607_);
        lean_closure_set(v___f_619_, 3, v_p_608_);
        lean_closure_set(v___f_619_, 4, v_n_618_);
        v___x_620_ = lean_nat_sub(v_n_607_, v_n_618_);
        lean_dec(v_n_618_);
        lean_dec(v_n_607_);
        v___x_621_ = lean_nat_sub(v___x_620_, v_one_617_);
        lean_dec(v___x_620_);
        v___x_622_ = lean_apply_2(v_p_608_, v___x_621_, lean_box(0));
        v___x_623_ = lean_apply_4(
            v_toBind_611_,
            lean_box(0),
            lean_box(0),
            v___x_622_,
            v___f_619_,
        );
        return v___x_623_;
    }
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_allM_loop___redArg___lam__0(
    mut v_toPure_624_: *mut LeanObject,
    mut v_inst_625_: *mut LeanObject,
    mut v_n_626_: *mut LeanObject,
    mut v_p_627_: *mut LeanObject,
    mut v_n_628_: *mut LeanObject,
    mut v_____do__lift_629_: u8,
) -> *mut LeanObject {
    if v_____do__lift_629_ == 0 {
        let mut v___x_630_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_631_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_p_627_);
        lean_dec(v_n_626_);
        lean_dec_ref(v_inst_625_);
        v___x_630_ = lean_box((v_____do__lift_629_) as usize);
        v___x_631_ = lean_apply_2(v_toPure_624_, lean_box(0), v___x_630_);
        return v___x_631_;
    } else {
        let mut v___x_632_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_624_);
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
    mut v_inst_633_: *mut LeanObject,
    mut v_n_634_: *mut LeanObject,
    mut v_p_635_: *mut LeanObject,
    mut v_i_636_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_637_: *mut LeanObject = core::ptr::null_mut();
    v_res_637_ = l___private_Init_Data_Nat_Control_0__Nat_allM_loop___redArg(
        v_inst_633_,
        v_n_634_,
        v_p_635_,
        v_i_636_,
    );
    lean_dec(v_i_636_);
    return v_res_637_;
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_allM_loop(
    mut v_m_638_: *mut LeanObject,
    mut v_inst_639_: *mut LeanObject,
    mut v_n_640_: *mut LeanObject,
    mut v_p_641_: *mut LeanObject,
    mut v_i_642_: *mut LeanObject,
    mut v_a_643_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_644_: *mut LeanObject = core::ptr::null_mut();
    v___x_644_ = l___private_Init_Data_Nat_Control_0__Nat_allM_loop___redArg(
        v_inst_639_,
        v_n_640_,
        v_p_641_,
        v_i_642_,
    );
    return v___x_644_;
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_allM_loop___boxed(
    mut v_m_645_: *mut LeanObject,
    mut v_inst_646_: *mut LeanObject,
    mut v_n_647_: *mut LeanObject,
    mut v_p_648_: *mut LeanObject,
    mut v_i_649_: *mut LeanObject,
    mut v_a_650_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_651_: *mut LeanObject = core::ptr::null_mut();
    v_res_651_ = l___private_Init_Data_Nat_Control_0__Nat_allM_loop(
        v_m_645_,
        v_inst_646_,
        v_n_647_,
        v_p_648_,
        v_i_649_,
        v_a_650_,
    );
    lean_dec(v_i_649_);
    return v_res_651_;
}
pub unsafe fn l_Nat_allM___redArg(
    mut v_inst_652_: *mut LeanObject,
    mut v_n_653_: *mut LeanObject,
    mut v_p_654_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_655_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_n_653_);
    v___x_655_ = l___private_Init_Data_Nat_Control_0__Nat_allM_loop___redArg(
        v_inst_652_,
        v_n_653_,
        v_p_654_,
        v_n_653_,
    );
    lean_dec(v_n_653_);
    return v___x_655_;
}
pub unsafe fn l_Nat_allM(
    mut v_m_656_: *mut LeanObject,
    mut v_inst_657_: *mut LeanObject,
    mut v_n_658_: *mut LeanObject,
    mut v_p_659_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_660_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_n_658_);
    v___x_660_ = l___private_Init_Data_Nat_Control_0__Nat_allM_loop___redArg(
        v_inst_657_,
        v_n_658_,
        v_p_659_,
        v_n_658_,
    );
    lean_dec(v_n_658_);
    return v___x_660_;
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_anyM_loop___redArg___lam__0___boxed(
    mut v_inst_661_: *mut LeanObject,
    mut v_n_662_: *mut LeanObject,
    mut v_p_663_: *mut LeanObject,
    mut v_n_664_: *mut LeanObject,
    mut v_toPure_665_: *mut LeanObject,
    mut v_____do__lift_666_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____do__lift_114__boxed_667_: u8 = 0;
    let mut v_res_668_: *mut LeanObject = core::ptr::null_mut();
    v_____do__lift_114__boxed_667_ = (lean_unbox(v_____do__lift_666_) as u8);
    v_res_668_ = l___private_Init_Data_Nat_Control_0__Nat_anyM_loop___redArg___lam__0(
        v_inst_661_,
        v_n_662_,
        v_p_663_,
        v_n_664_,
        v_toPure_665_,
        v_____do__lift_114__boxed_667_,
    );
    lean_dec(v_n_664_);
    return v_res_668_;
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_anyM_loop___redArg(
    mut v_inst_669_: *mut LeanObject,
    mut v_n_670_: *mut LeanObject,
    mut v_p_671_: *mut LeanObject,
    mut v_i_672_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zero_676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_677_: u8 = 0;
    v_toApplicative_673_ = lean_ctor_get(v_inst_669_, 0);
    v_toBind_674_ = lean_ctor_get(v_inst_669_, 1);
    lean_inc(v_toBind_674_);
    v_toPure_675_ = lean_ctor_get(v_toApplicative_673_, 1);
    lean_inc(v_toPure_675_);
    v_zero_676_ = lean_unsigned_to_nat(0);
    v_isZero_677_ = lean_nat_dec_eq(v_i_672_, v_zero_676_);
    if v_isZero_677_ == 1 {
        let mut v___x_678_: u8 = 0;
        let mut v___x_679_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_680_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toBind_674_);
        lean_dec(v_p_671_);
        lean_dec(v_n_670_);
        lean_dec_ref(v_inst_669_);
        v___x_678_ = 0;
        v___x_679_ = lean_box((v___x_678_) as usize);
        v___x_680_ = lean_apply_2(v_toPure_675_, lean_box(0), v___x_679_);
        return v___x_680_;
    } else {
        let mut v_one_681_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_682_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_683_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_684_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_685_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_686_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_687_: *mut LeanObject = core::ptr::null_mut();
        v_one_681_ = lean_unsigned_to_nat(1);
        v_n_682_ = lean_nat_sub(v_i_672_, v_one_681_);
        lean_inc(v_n_682_);
        lean_inc(v_p_671_);
        lean_inc(v_n_670_);
        v___f_683_ = lean_alloc_closure(
            l___private_Init_Data_Nat_Control_0__Nat_anyM_loop___redArg___lam__0___boxed
                as *mut core::ffi::c_void,
            6,
            5,
        );
        lean_closure_set(v___f_683_, 0, v_inst_669_);
        lean_closure_set(v___f_683_, 1, v_n_670_);
        lean_closure_set(v___f_683_, 2, v_p_671_);
        lean_closure_set(v___f_683_, 3, v_n_682_);
        lean_closure_set(v___f_683_, 4, v_toPure_675_);
        v___x_684_ = lean_nat_sub(v_n_670_, v_n_682_);
        lean_dec(v_n_682_);
        lean_dec(v_n_670_);
        v___x_685_ = lean_nat_sub(v___x_684_, v_one_681_);
        lean_dec(v___x_684_);
        v___x_686_ = lean_apply_2(v_p_671_, v___x_685_, lean_box(0));
        v___x_687_ = lean_apply_4(
            v_toBind_674_,
            lean_box(0),
            lean_box(0),
            v___x_686_,
            v___f_683_,
        );
        return v___x_687_;
    }
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_anyM_loop___redArg___lam__0(
    mut v_inst_688_: *mut LeanObject,
    mut v_n_689_: *mut LeanObject,
    mut v_p_690_: *mut LeanObject,
    mut v_n_691_: *mut LeanObject,
    mut v_toPure_692_: *mut LeanObject,
    mut v_____do__lift_693_: u8,
) -> *mut LeanObject {
    if v_____do__lift_693_ == 0 {
        let mut v___x_694_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_692_);
        v___x_694_ = l___private_Init_Data_Nat_Control_0__Nat_anyM_loop___redArg(
            v_inst_688_,
            v_n_689_,
            v_p_690_,
            v_n_691_,
        );
        return v___x_694_;
    } else {
        let mut v___x_695_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_696_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_p_690_);
        lean_dec(v_n_689_);
        lean_dec_ref(v_inst_688_);
        v___x_695_ = lean_box((v_____do__lift_693_) as usize);
        v___x_696_ = lean_apply_2(v_toPure_692_, lean_box(0), v___x_695_);
        return v___x_696_;
    }
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_anyM_loop___redArg___boxed(
    mut v_inst_697_: *mut LeanObject,
    mut v_n_698_: *mut LeanObject,
    mut v_p_699_: *mut LeanObject,
    mut v_i_700_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_701_: *mut LeanObject = core::ptr::null_mut();
    v_res_701_ = l___private_Init_Data_Nat_Control_0__Nat_anyM_loop___redArg(
        v_inst_697_,
        v_n_698_,
        v_p_699_,
        v_i_700_,
    );
    lean_dec(v_i_700_);
    return v_res_701_;
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_anyM_loop(
    mut v_m_702_: *mut LeanObject,
    mut v_inst_703_: *mut LeanObject,
    mut v_n_704_: *mut LeanObject,
    mut v_p_705_: *mut LeanObject,
    mut v_i_706_: *mut LeanObject,
    mut v_a_707_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_708_: *mut LeanObject = core::ptr::null_mut();
    v___x_708_ = l___private_Init_Data_Nat_Control_0__Nat_anyM_loop___redArg(
        v_inst_703_,
        v_n_704_,
        v_p_705_,
        v_i_706_,
    );
    return v___x_708_;
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_anyM_loop___boxed(
    mut v_m_709_: *mut LeanObject,
    mut v_inst_710_: *mut LeanObject,
    mut v_n_711_: *mut LeanObject,
    mut v_p_712_: *mut LeanObject,
    mut v_i_713_: *mut LeanObject,
    mut v_a_714_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_715_: *mut LeanObject = core::ptr::null_mut();
    v_res_715_ = l___private_Init_Data_Nat_Control_0__Nat_anyM_loop(
        v_m_709_,
        v_inst_710_,
        v_n_711_,
        v_p_712_,
        v_i_713_,
        v_a_714_,
    );
    lean_dec(v_i_713_);
    return v_res_715_;
}
pub unsafe fn l_Nat_anyM___redArg(
    mut v_inst_716_: *mut LeanObject,
    mut v_n_717_: *mut LeanObject,
    mut v_p_718_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_719_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_n_717_);
    v___x_719_ = l___private_Init_Data_Nat_Control_0__Nat_anyM_loop___redArg(
        v_inst_716_,
        v_n_717_,
        v_p_718_,
        v_n_717_,
    );
    lean_dec(v_n_717_);
    return v___x_719_;
}
pub unsafe fn l_Nat_anyM(
    mut v_m_720_: *mut LeanObject,
    mut v_inst_721_: *mut LeanObject,
    mut v_n_722_: *mut LeanObject,
    mut v_p_723_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_724_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_n_722_);
    v___x_724_ = l___private_Init_Data_Nat_Control_0__Nat_anyM_loop___redArg(
        v_inst_721_,
        v_n_722_,
        v_p_723_,
        v_n_722_,
    );
    lean_dec(v_n_722_);
    return v___x_724_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Nat_Control(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Notation(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Nat_Control(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Nat_Control(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Notation(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Control(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Nat_Control(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Nat_Control(builtin);
}
