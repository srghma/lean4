// Lean compiler output
// Module: Init.Data.Fin.Lemmas
// Imports: Init.Ext Init.Data.Nat.Div.Basic Init.Data.Order.Classes Init.NotationExtra Init.ByCases Init.Data.Nat.Lemmas Init.Data.Nat.Linear Init.Omega Init.TacticsExtra Init.Hints
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Data::Nat::Div::Basic::{
    initialize_Init_Data_Nat_Div_Basic, runtime_initialize_Init_Data_Nat_Div_Basic,
};
use crate::r#gen::Init::Data::Nat::Lemmas::{
    initialize_Init_Data_Nat_Lemmas, runtime_initialize_Init_Data_Nat_Lemmas,
};
use crate::r#gen::Init::Data::Nat::Linear::{
    initialize_Init_Data_Nat_Linear, runtime_initialize_Init_Data_Nat_Linear,
};
use crate::r#gen::Init::Data::Order::Classes::{
    initialize_Init_Data_Order_Classes, runtime_initialize_Init_Data_Order_Classes,
};
use crate::r#gen::Init::Ext::{initialize_Init_Ext, runtime_initialize_Init_Ext};
use crate::r#gen::Init::Hints::{initialize_Init_Hints, runtime_initialize_Init_Hints};
use crate::r#gen::Init::NotationExtra::{
    initialize_Init_NotationExtra, runtime_initialize_Init_NotationExtra,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::TacticsExtra::{
    initialize_Init_TacticsExtra, runtime_initialize_Init_TacticsExtra,
};
use crate::lean_imports_rs::Init::Data::Int::Basic::{
    lean_int_dec_le, lean_nat_abs, lean_nat_to_int,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_mod, lean_nat_sub,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_apply_1, lean_apply_2, lean_apply_3,
    lean_apply_4, lean_apply_5, lean_box, lean_closure_set, lean_dec, lean_dec_ref, lean_inc,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_once, lean_unsigned_to_nat,
};
static mut l_Fin_intCast___redArg___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Fin_intCast___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Fin_NatCast_instNatCast___redArg___lam__0(
    mut v_n_346_: *mut LeanObject,
    mut v_a_347_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_348_: *mut LeanObject = core::ptr::null_mut();
    v___x_348_ = lean_nat_mod(v_a_347_, v_n_346_);
    return v___x_348_;
}
pub unsafe fn l_Fin_NatCast_instNatCast___redArg___lam__0___boxed(
    mut v_n_349_: *mut LeanObject,
    mut v_a_350_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_351_: *mut LeanObject = core::ptr::null_mut();
    v_res_351_ = l_Fin_NatCast_instNatCast___redArg___lam__0(v_n_349_, v_a_350_);
    lean_dec(v_a_350_);
    lean_dec(v_n_349_);
    return v_res_351_;
}
pub unsafe fn l_Fin_NatCast_instNatCast___redArg(mut v_n_352_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_353_: *mut LeanObject = core::ptr::null_mut();
    v___f_353_ = lean_alloc_closure(
        l_Fin_NatCast_instNatCast___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_353_, 0, v_n_352_);
    return v___f_353_;
}
pub unsafe fn l_Fin_NatCast_instNatCast(
    mut v_n_354_: *mut LeanObject,
    mut v_inst_355_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_356_: *mut LeanObject = core::ptr::null_mut();
    v___f_356_ = lean_alloc_closure(
        l_Fin_NatCast_instNatCast___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_356_, 0, v_n_354_);
    return v___f_356_;
}
pub unsafe fn _init_l_Fin_intCast___redArg___closed__0() -> *mut LeanObject {
    let mut v___x_357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_358_: *mut LeanObject = core::ptr::null_mut();
    v___x_357_ = lean_unsigned_to_nat(0);
    v___x_358_ = lean_nat_to_int(v___x_357_);
    return v___x_358_;
}
pub unsafe fn l_Fin_intCast___redArg(
    mut v_n_359_: *mut LeanObject,
    mut v_a_360_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_362_: u8 = 0;
    v___x_361_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Fin_intCast___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Fin_intCast___redArg___closed__0_once),
        _init_l_Fin_intCast___redArg___closed__0,
    );
    v___x_362_ = lean_int_dec_le(v___x_361_, v_a_360_);
    if v___x_362_ == 0 {
        let mut v___x_363_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_364_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_365_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_366_: *mut LeanObject = core::ptr::null_mut();
        v___x_363_ = lean_nat_abs(v_a_360_);
        v___x_364_ = lean_nat_mod(v___x_363_, v_n_359_);
        lean_dec(v___x_363_);
        v___x_365_ = lean_nat_sub(v_n_359_, v___x_364_);
        lean_dec(v___x_364_);
        v___x_366_ = lean_nat_mod(v___x_365_, v_n_359_);
        lean_dec(v___x_365_);
        return v___x_366_;
    } else {
        let mut v___x_367_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_368_: *mut LeanObject = core::ptr::null_mut();
        v___x_367_ = lean_nat_abs(v_a_360_);
        v___x_368_ = lean_nat_mod(v___x_367_, v_n_359_);
        lean_dec(v___x_367_);
        return v___x_368_;
    }
}
pub unsafe fn l_Fin_intCast___redArg___boxed(
    mut v_n_369_: *mut LeanObject,
    mut v_a_370_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_371_: *mut LeanObject = core::ptr::null_mut();
    v_res_371_ = l_Fin_intCast___redArg(v_n_369_, v_a_370_);
    lean_dec(v_a_370_);
    lean_dec(v_n_369_);
    return v_res_371_;
}
pub unsafe fn l_Fin_intCast(
    mut v_n_372_: *mut LeanObject,
    mut v_inst_373_: *mut LeanObject,
    mut v_a_374_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_375_: *mut LeanObject = core::ptr::null_mut();
    v___x_375_ = l_Fin_intCast___redArg(v_n_372_, v_a_374_);
    return v___x_375_;
}
pub unsafe fn l_Fin_intCast___boxed(
    mut v_n_376_: *mut LeanObject,
    mut v_inst_377_: *mut LeanObject,
    mut v_a_378_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_379_: *mut LeanObject = core::ptr::null_mut();
    v_res_379_ = l_Fin_intCast(v_n_376_, v_inst_377_, v_a_378_);
    lean_dec(v_a_378_);
    lean_dec(v_n_376_);
    return v_res_379_;
}
pub unsafe fn l_Fin_IntCast_instIntCast___redArg(mut v_n_380_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_381_: *mut LeanObject = core::ptr::null_mut();
    v___x_381_ = lean_alloc_closure(l_Fin_intCast___boxed as *mut core::ffi::c_void, 3, 2);
    lean_closure_set(v___x_381_, 0, v_n_380_);
    lean_closure_set(v___x_381_, 1, lean_box(0));
    return v___x_381_;
}
pub unsafe fn l_Fin_IntCast_instIntCast(
    mut v_n_382_: *mut LeanObject,
    mut v_inst_383_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_384_: *mut LeanObject = core::ptr::null_mut();
    v___x_384_ = lean_alloc_closure(l_Fin_intCast___boxed as *mut core::ffi::c_void, 3, 2);
    lean_closure_set(v___x_384_, 0, v_n_382_);
    lean_closure_set(v___x_384_, 1, lean_box(0));
    return v___x_384_;
}
pub unsafe fn l_Fin_succRec___redArg(
    mut v_zero_385_: *mut LeanObject,
    mut v_succ_386_: *mut LeanObject,
    mut v_x_387_: *mut LeanObject,
    mut v_x_388_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_390_: u8 = 0;
    let mut v_one_391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_393_: u8 = 0;
    v_zero_389_ = lean_unsigned_to_nat(0);
    v_isZero_390_ = lean_nat_dec_eq(v_x_387_, v_zero_389_);
    v_one_391_ = lean_unsigned_to_nat(1);
    v_n_392_ = lean_nat_sub(v_x_387_, v_one_391_);
    v_isZero_393_ = lean_nat_dec_eq(v_x_388_, v_zero_389_);
    if v_isZero_393_ == 1 {
        let mut v___x_394_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_succ_386_);
        v___x_394_ = lean_apply_1(v_zero_385_, v_n_392_);
        return v___x_394_;
    } else {
        let mut v_n_395_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_396_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_397_: *mut LeanObject = core::ptr::null_mut();
        v_n_395_ = lean_nat_sub(v_x_388_, v_one_391_);
        lean_inc(v_succ_386_);
        v___x_396_ = l_Fin_succRec___redArg(v_zero_385_, v_succ_386_, v_n_392_, v_n_395_);
        v___x_397_ = lean_apply_3(v_succ_386_, v_n_392_, v_n_395_, v___x_396_);
        return v___x_397_;
    }
}
pub unsafe fn l_Fin_succRec___redArg___boxed(
    mut v_zero_398_: *mut LeanObject,
    mut v_succ_399_: *mut LeanObject,
    mut v_x_400_: *mut LeanObject,
    mut v_x_401_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_402_: *mut LeanObject = core::ptr::null_mut();
    v_res_402_ = l_Fin_succRec___redArg(v_zero_398_, v_succ_399_, v_x_400_, v_x_401_);
    lean_dec(v_x_401_);
    lean_dec(v_x_400_);
    return v_res_402_;
}
pub unsafe fn l_Fin_succRec(
    mut v_motive_403_: *mut LeanObject,
    mut v_zero_404_: *mut LeanObject,
    mut v_succ_405_: *mut LeanObject,
    mut v_x_406_: *mut LeanObject,
    mut v_x_407_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_408_: *mut LeanObject = core::ptr::null_mut();
    v___x_408_ = l_Fin_succRec___redArg(v_zero_404_, v_succ_405_, v_x_406_, v_x_407_);
    return v___x_408_;
}
pub unsafe fn l_Fin_succRec___boxed(
    mut v_motive_409_: *mut LeanObject,
    mut v_zero_410_: *mut LeanObject,
    mut v_succ_411_: *mut LeanObject,
    mut v_x_412_: *mut LeanObject,
    mut v_x_413_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_414_: *mut LeanObject = core::ptr::null_mut();
    v_res_414_ = l_Fin_succRec(v_motive_409_, v_zero_410_, v_succ_411_, v_x_412_, v_x_413_);
    lean_dec(v_x_413_);
    lean_dec(v_x_412_);
    return v_res_414_;
}
pub unsafe fn l_Fin_succRecOn___redArg(
    mut v_n_415_: *mut LeanObject,
    mut v_i_416_: *mut LeanObject,
    mut v_zero_417_: *mut LeanObject,
    mut v_succ_418_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_419_: *mut LeanObject = core::ptr::null_mut();
    v___x_419_ = l_Fin_succRec___redArg(v_zero_417_, v_succ_418_, v_n_415_, v_i_416_);
    return v___x_419_;
}
pub unsafe fn l_Fin_succRecOn___redArg___boxed(
    mut v_n_420_: *mut LeanObject,
    mut v_i_421_: *mut LeanObject,
    mut v_zero_422_: *mut LeanObject,
    mut v_succ_423_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_424_: *mut LeanObject = core::ptr::null_mut();
    v_res_424_ = l_Fin_succRecOn___redArg(v_n_420_, v_i_421_, v_zero_422_, v_succ_423_);
    lean_dec(v_i_421_);
    lean_dec(v_n_420_);
    return v_res_424_;
}
pub unsafe fn l_Fin_succRecOn(
    mut v_n_425_: *mut LeanObject,
    mut v_i_426_: *mut LeanObject,
    mut v_motive_427_: *mut LeanObject,
    mut v_zero_428_: *mut LeanObject,
    mut v_succ_429_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_430_: *mut LeanObject = core::ptr::null_mut();
    v___x_430_ = l_Fin_succRec___redArg(v_zero_428_, v_succ_429_, v_n_425_, v_i_426_);
    return v___x_430_;
}
pub unsafe fn l_Fin_succRecOn___boxed(
    mut v_n_431_: *mut LeanObject,
    mut v_i_432_: *mut LeanObject,
    mut v_motive_433_: *mut LeanObject,
    mut v_zero_434_: *mut LeanObject,
    mut v_succ_435_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_436_: *mut LeanObject = core::ptr::null_mut();
    v_res_436_ = l_Fin_succRecOn(v_n_431_, v_i_432_, v_motive_433_, v_zero_434_, v_succ_435_);
    lean_dec(v_i_432_);
    lean_dec(v_n_431_);
    return v_res_436_;
}
pub unsafe fn l_Fin_induction_go___redArg(
    mut v_zero_437_: *mut LeanObject,
    mut v_succ_438_: *mut LeanObject,
    mut v_i_439_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_441_: u8 = 0;
    v_zero_440_ = lean_unsigned_to_nat(0);
    v_isZero_441_ = lean_nat_dec_eq(v_i_439_, v_zero_440_);
    if v_isZero_441_ == 1 {
        lean_dec(v_succ_438_);
        lean_inc(v_zero_437_);
        return v_zero_437_;
    } else {
        let mut v_one_442_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_443_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_444_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_445_: *mut LeanObject = core::ptr::null_mut();
        v_one_442_ = lean_unsigned_to_nat(1);
        v_n_443_ = lean_nat_sub(v_i_439_, v_one_442_);
        lean_inc(v_succ_438_);
        v___x_444_ = l_Fin_induction_go___redArg(v_zero_437_, v_succ_438_, v_n_443_);
        v___x_445_ = lean_apply_2(v_succ_438_, v_n_443_, v___x_444_);
        return v___x_445_;
    }
}
pub unsafe fn l_Fin_induction_go___redArg___boxed(
    mut v_zero_446_: *mut LeanObject,
    mut v_succ_447_: *mut LeanObject,
    mut v_i_448_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_449_: *mut LeanObject = core::ptr::null_mut();
    v_res_449_ = l_Fin_induction_go___redArg(v_zero_446_, v_succ_447_, v_i_448_);
    lean_dec(v_i_448_);
    lean_dec(v_zero_446_);
    return v_res_449_;
}
pub unsafe fn l_Fin_induction_go(
    mut v_n_450_: *mut LeanObject,
    mut v_motive_451_: *mut LeanObject,
    mut v_zero_452_: *mut LeanObject,
    mut v_succ_453_: *mut LeanObject,
    mut v_i_454_: *mut LeanObject,
    mut v_hi_455_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_456_: *mut LeanObject = core::ptr::null_mut();
    v___x_456_ = l_Fin_induction_go___redArg(v_zero_452_, v_succ_453_, v_i_454_);
    return v___x_456_;
}
pub unsafe fn l_Fin_induction_go___boxed(
    mut v_n_457_: *mut LeanObject,
    mut v_motive_458_: *mut LeanObject,
    mut v_zero_459_: *mut LeanObject,
    mut v_succ_460_: *mut LeanObject,
    mut v_i_461_: *mut LeanObject,
    mut v_hi_462_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_463_: *mut LeanObject = core::ptr::null_mut();
    v_res_463_ = l_Fin_induction_go(
        v_n_457_,
        v_motive_458_,
        v_zero_459_,
        v_succ_460_,
        v_i_461_,
        v_hi_462_,
    );
    lean_dec(v_i_461_);
    lean_dec(v_zero_459_);
    lean_dec(v_n_457_);
    return v_res_463_;
}
pub unsafe fn l_Fin_induction___redArg(
    mut v_zero_464_: *mut LeanObject,
    mut v_succ_465_: *mut LeanObject,
    mut v_x_466_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_467_: *mut LeanObject = core::ptr::null_mut();
    v___x_467_ = l_Fin_induction_go___redArg(v_zero_464_, v_succ_465_, v_x_466_);
    return v___x_467_;
}
pub unsafe fn l_Fin_induction___redArg___boxed(
    mut v_zero_468_: *mut LeanObject,
    mut v_succ_469_: *mut LeanObject,
    mut v_x_470_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_471_: *mut LeanObject = core::ptr::null_mut();
    v_res_471_ = l_Fin_induction___redArg(v_zero_468_, v_succ_469_, v_x_470_);
    lean_dec(v_x_470_);
    lean_dec(v_zero_468_);
    return v_res_471_;
}
pub unsafe fn l_Fin_induction(
    mut v_n_472_: *mut LeanObject,
    mut v_motive_473_: *mut LeanObject,
    mut v_zero_474_: *mut LeanObject,
    mut v_succ_475_: *mut LeanObject,
    mut v_x_476_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_477_: *mut LeanObject = core::ptr::null_mut();
    v___x_477_ = l_Fin_induction_go___redArg(v_zero_474_, v_succ_475_, v_x_476_);
    return v___x_477_;
}
pub unsafe fn l_Fin_induction___boxed(
    mut v_n_478_: *mut LeanObject,
    mut v_motive_479_: *mut LeanObject,
    mut v_zero_480_: *mut LeanObject,
    mut v_succ_481_: *mut LeanObject,
    mut v_x_482_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_483_: *mut LeanObject = core::ptr::null_mut();
    v_res_483_ = l_Fin_induction(v_n_478_, v_motive_479_, v_zero_480_, v_succ_481_, v_x_482_);
    lean_dec(v_x_482_);
    lean_dec(v_zero_480_);
    lean_dec(v_n_478_);
    return v_res_483_;
}
pub unsafe fn l_Fin_inductionOn___redArg(
    mut v_i_484_: *mut LeanObject,
    mut v_zero_485_: *mut LeanObject,
    mut v_succ_486_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_487_: *mut LeanObject = core::ptr::null_mut();
    v___x_487_ = l_Fin_induction_go___redArg(v_zero_485_, v_succ_486_, v_i_484_);
    return v___x_487_;
}
pub unsafe fn l_Fin_inductionOn___redArg___boxed(
    mut v_i_488_: *mut LeanObject,
    mut v_zero_489_: *mut LeanObject,
    mut v_succ_490_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_491_: *mut LeanObject = core::ptr::null_mut();
    v_res_491_ = l_Fin_inductionOn___redArg(v_i_488_, v_zero_489_, v_succ_490_);
    lean_dec(v_zero_489_);
    lean_dec(v_i_488_);
    return v_res_491_;
}
pub unsafe fn l_Fin_inductionOn(
    mut v_n_492_: *mut LeanObject,
    mut v_i_493_: *mut LeanObject,
    mut v_motive_494_: *mut LeanObject,
    mut v_zero_495_: *mut LeanObject,
    mut v_succ_496_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_497_: *mut LeanObject = core::ptr::null_mut();
    v___x_497_ = l_Fin_induction_go___redArg(v_zero_495_, v_succ_496_, v_i_493_);
    return v___x_497_;
}
pub unsafe fn l_Fin_inductionOn___boxed(
    mut v_n_498_: *mut LeanObject,
    mut v_i_499_: *mut LeanObject,
    mut v_motive_500_: *mut LeanObject,
    mut v_zero_501_: *mut LeanObject,
    mut v_succ_502_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_503_: *mut LeanObject = core::ptr::null_mut();
    v_res_503_ = l_Fin_inductionOn(v_n_498_, v_i_499_, v_motive_500_, v_zero_501_, v_succ_502_);
    lean_dec(v_zero_501_);
    lean_dec(v_i_499_);
    lean_dec(v_n_498_);
    return v_res_503_;
}
pub unsafe fn l_Fin_cases___redArg___lam__0(
    mut v_succ_504_: *mut LeanObject,
    mut v_i_505_: *mut LeanObject,
    mut v_x_506_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_507_: *mut LeanObject = core::ptr::null_mut();
    v___x_507_ = lean_apply_1(v_succ_504_, v_i_505_);
    return v___x_507_;
}
pub unsafe fn l_Fin_cases___redArg___lam__0___boxed(
    mut v_succ_508_: *mut LeanObject,
    mut v_i_509_: *mut LeanObject,
    mut v_x_510_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_511_: *mut LeanObject = core::ptr::null_mut();
    v_res_511_ = l_Fin_cases___redArg___lam__0(v_succ_508_, v_i_509_, v_x_510_);
    lean_dec(v_x_510_);
    return v_res_511_;
}
pub unsafe fn l_Fin_cases___redArg(
    mut v_zero_512_: *mut LeanObject,
    mut v_succ_513_: *mut LeanObject,
    mut v_i_514_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_516_: *mut LeanObject = core::ptr::null_mut();
    v___f_515_ = lean_alloc_closure(
        l_Fin_cases___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_515_, 0, v_succ_513_);
    v___x_516_ = l_Fin_induction_go___redArg(v_zero_512_, v___f_515_, v_i_514_);
    return v___x_516_;
}
pub unsafe fn l_Fin_cases___redArg___boxed(
    mut v_zero_517_: *mut LeanObject,
    mut v_succ_518_: *mut LeanObject,
    mut v_i_519_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_520_: *mut LeanObject = core::ptr::null_mut();
    v_res_520_ = l_Fin_cases___redArg(v_zero_517_, v_succ_518_, v_i_519_);
    lean_dec(v_i_519_);
    lean_dec(v_zero_517_);
    return v_res_520_;
}
pub unsafe fn l_Fin_cases(
    mut v_n_521_: *mut LeanObject,
    mut v_motive_522_: *mut LeanObject,
    mut v_zero_523_: *mut LeanObject,
    mut v_succ_524_: *mut LeanObject,
    mut v_i_525_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_526_: *mut LeanObject = core::ptr::null_mut();
    v___x_526_ = l_Fin_cases___redArg(v_zero_523_, v_succ_524_, v_i_525_);
    return v___x_526_;
}
pub unsafe fn l_Fin_cases___boxed(
    mut v_n_527_: *mut LeanObject,
    mut v_motive_528_: *mut LeanObject,
    mut v_zero_529_: *mut LeanObject,
    mut v_succ_530_: *mut LeanObject,
    mut v_i_531_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_532_: *mut LeanObject = core::ptr::null_mut();
    v_res_532_ = l_Fin_cases(v_n_527_, v_motive_528_, v_zero_529_, v_succ_530_, v_i_531_);
    lean_dec(v_i_531_);
    lean_dec(v_zero_529_);
    lean_dec(v_n_527_);
    return v_res_532_;
}
pub unsafe fn l_Fin_reverseInduction_go___redArg(
    mut v_cast_533_: *mut LeanObject,
    mut v_i_534_: *mut LeanObject,
    mut v_j_535_: *mut LeanObject,
    mut v_x_536_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_537_: u8 = 0;
    let mut v_zero_538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_539_: u8 = 0;
    let mut v_one_540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_542_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_537_ = lean_nat_dec_eq(v_i_534_, v_j_535_);
                if v___x_537_ == 0 {
                    v_zero_538_ = lean_unsigned_to_nat(0);
                    v_isZero_539_ = lean_nat_dec_eq(v_j_535_, v_zero_538_);
                    v_one_540_ = lean_unsigned_to_nat(1);
                    v_n_541_ = lean_nat_sub(v_j_535_, v_one_540_);
                    lean_dec(v_j_535_);
                    lean_inc(v_cast_533_);
                    lean_inc(v_n_541_);
                    v___x_542_ = lean_apply_2(v_cast_533_, v_n_541_, v_x_536_);
                    v_j_535_ = v_n_541_;
                    v_x_536_ = v___x_542_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_j_535_);
                    lean_dec(v_cast_533_);
                    return v_x_536_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Fin_reverseInduction_go___redArg___boxed(
    mut v_cast_544_: *mut LeanObject,
    mut v_i_545_: *mut LeanObject,
    mut v_j_546_: *mut LeanObject,
    mut v_x_547_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_548_: *mut LeanObject = core::ptr::null_mut();
    v_res_548_ = l_Fin_reverseInduction_go___redArg(v_cast_544_, v_i_545_, v_j_546_, v_x_547_);
    lean_dec(v_i_545_);
    return v_res_548_;
}
pub unsafe fn l_Fin_reverseInduction_go(
    mut v_n_549_: *mut LeanObject,
    mut v_motive_550_: *mut LeanObject,
    mut v_cast_551_: *mut LeanObject,
    mut v_i_552_: *mut LeanObject,
    mut v_j_553_: *mut LeanObject,
    mut v_h_554_: *mut LeanObject,
    mut v_h2_555_: *mut LeanObject,
    mut v_x_556_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_557_: *mut LeanObject = core::ptr::null_mut();
    v___x_557_ = l_Fin_reverseInduction_go___redArg(v_cast_551_, v_i_552_, v_j_553_, v_x_556_);
    return v___x_557_;
}
pub unsafe fn l_Fin_reverseInduction_go___boxed(
    mut v_n_558_: *mut LeanObject,
    mut v_motive_559_: *mut LeanObject,
    mut v_cast_560_: *mut LeanObject,
    mut v_i_561_: *mut LeanObject,
    mut v_j_562_: *mut LeanObject,
    mut v_h_563_: *mut LeanObject,
    mut v_h2_564_: *mut LeanObject,
    mut v_x_565_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_566_: *mut LeanObject = core::ptr::null_mut();
    v_res_566_ = l_Fin_reverseInduction_go(
        v_n_558_,
        v_motive_559_,
        v_cast_560_,
        v_i_561_,
        v_j_562_,
        v_h_563_,
        v_h2_564_,
        v_x_565_,
    );
    lean_dec(v_i_561_);
    lean_dec(v_n_558_);
    return v_res_566_;
}
pub unsafe fn l_Fin_reverseInduction___redArg(
    mut v_n_567_: *mut LeanObject,
    mut v_last_568_: *mut LeanObject,
    mut v_cast_569_: *mut LeanObject,
    mut v_i_570_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_571_: *mut LeanObject = core::ptr::null_mut();
    v___x_571_ = l_Fin_reverseInduction_go___redArg(v_cast_569_, v_i_570_, v_n_567_, v_last_568_);
    return v___x_571_;
}
pub unsafe fn l_Fin_reverseInduction___redArg___boxed(
    mut v_n_572_: *mut LeanObject,
    mut v_last_573_: *mut LeanObject,
    mut v_cast_574_: *mut LeanObject,
    mut v_i_575_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_576_: *mut LeanObject = core::ptr::null_mut();
    v_res_576_ = l_Fin_reverseInduction___redArg(v_n_572_, v_last_573_, v_cast_574_, v_i_575_);
    lean_dec(v_i_575_);
    return v_res_576_;
}
pub unsafe fn l_Fin_reverseInduction(
    mut v_n_577_: *mut LeanObject,
    mut v_motive_578_: *mut LeanObject,
    mut v_last_579_: *mut LeanObject,
    mut v_cast_580_: *mut LeanObject,
    mut v_i_581_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_582_: *mut LeanObject = core::ptr::null_mut();
    v___x_582_ = l_Fin_reverseInduction_go___redArg(v_cast_580_, v_i_581_, v_n_577_, v_last_579_);
    return v___x_582_;
}
pub unsafe fn l_Fin_reverseInduction___boxed(
    mut v_n_583_: *mut LeanObject,
    mut v_motive_584_: *mut LeanObject,
    mut v_last_585_: *mut LeanObject,
    mut v_cast_586_: *mut LeanObject,
    mut v_i_587_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_588_: *mut LeanObject = core::ptr::null_mut();
    v_res_588_ =
        l_Fin_reverseInduction(v_n_583_, v_motive_584_, v_last_585_, v_cast_586_, v_i_587_);
    lean_dec(v_i_587_);
    return v_res_588_;
}
pub unsafe fn l___private_Init_Data_Fin_Lemmas_0__Fin_reverseInduction_go_match__1_splitter___redArg(
    mut v_j_589_: *mut LeanObject,
    mut v_x_590_: *mut LeanObject,
    mut v_h__1_591_: *mut LeanObject,
    mut v_h__2_592_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_594_: u8 = 0;
    v_zero_593_ = lean_unsigned_to_nat(0);
    v_isZero_594_ = lean_nat_dec_eq(v_j_589_, v_zero_593_);
    if v_isZero_594_ == 1 {
        let mut v___x_595_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_592_);
        v___x_595_ = lean_apply_4(v_h__1_591_, lean_box(0), lean_box(0), v_x_590_, lean_box(0));
        return v___x_595_;
    } else {
        let mut v_one_596_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_597_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_598_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_591_);
        v_one_596_ = lean_unsigned_to_nat(1);
        v_n_597_ = lean_nat_sub(v_j_589_, v_one_596_);
        v___x_598_ = lean_apply_5(
            v_h__2_592_,
            v_n_597_,
            lean_box(0),
            lean_box(0),
            v_x_590_,
            lean_box(0),
        );
        return v___x_598_;
    }
}
pub unsafe fn l___private_Init_Data_Fin_Lemmas_0__Fin_reverseInduction_go_match__1_splitter___redArg___boxed(
    mut v_j_599_: *mut LeanObject,
    mut v_x_600_: *mut LeanObject,
    mut v_h__1_601_: *mut LeanObject,
    mut v_h__2_602_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_603_: *mut LeanObject = core::ptr::null_mut();
    v_res_603_ =
        l___private_Init_Data_Fin_Lemmas_0__Fin_reverseInduction_go_match__1_splitter___redArg(
            v_j_599_,
            v_x_600_,
            v_h__1_601_,
            v_h__2_602_,
        );
    lean_dec(v_j_599_);
    return v_res_603_;
}
pub unsafe fn l___private_Init_Data_Fin_Lemmas_0__Fin_reverseInduction_go_match__1_splitter(
    mut v_n_604_: *mut LeanObject,
    mut v_motive_605_: *mut LeanObject,
    mut v_i_606_: *mut LeanObject,
    mut v_motive_607_: *mut LeanObject,
    mut v_j_608_: *mut LeanObject,
    mut v_h_609_: *mut LeanObject,
    mut v_h2_610_: *mut LeanObject,
    mut v_x_611_: *mut LeanObject,
    mut v_hi_612_: *mut LeanObject,
    mut v_h__1_613_: *mut LeanObject,
    mut v_h__2_614_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_616_: u8 = 0;
    v_zero_615_ = lean_unsigned_to_nat(0);
    v_isZero_616_ = lean_nat_dec_eq(v_j_608_, v_zero_615_);
    if v_isZero_616_ == 1 {
        let mut v___x_617_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_614_);
        v___x_617_ = lean_apply_4(v_h__1_613_, lean_box(0), lean_box(0), v_x_611_, lean_box(0));
        return v___x_617_;
    } else {
        let mut v_one_618_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_619_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_620_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_613_);
        v_one_618_ = lean_unsigned_to_nat(1);
        v_n_619_ = lean_nat_sub(v_j_608_, v_one_618_);
        v___x_620_ = lean_apply_5(
            v_h__2_614_,
            v_n_619_,
            lean_box(0),
            lean_box(0),
            v_x_611_,
            lean_box(0),
        );
        return v___x_620_;
    }
}
pub unsafe fn l___private_Init_Data_Fin_Lemmas_0__Fin_reverseInduction_go_match__1_splitter___boxed(
    mut v_n_621_: *mut LeanObject,
    mut v_motive_622_: *mut LeanObject,
    mut v_i_623_: *mut LeanObject,
    mut v_motive_624_: *mut LeanObject,
    mut v_j_625_: *mut LeanObject,
    mut v_h_626_: *mut LeanObject,
    mut v_h2_627_: *mut LeanObject,
    mut v_x_628_: *mut LeanObject,
    mut v_hi_629_: *mut LeanObject,
    mut v_h__1_630_: *mut LeanObject,
    mut v_h__2_631_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_632_: *mut LeanObject = core::ptr::null_mut();
    v_res_632_ = l___private_Init_Data_Fin_Lemmas_0__Fin_reverseInduction_go_match__1_splitter(
        v_n_621_,
        v_motive_622_,
        v_i_623_,
        v_motive_624_,
        v_j_625_,
        v_h_626_,
        v_h2_627_,
        v_x_628_,
        v_hi_629_,
        v_h__1_630_,
        v_h__2_631_,
    );
    lean_dec(v_j_625_);
    lean_dec(v_i_623_);
    lean_dec(v_n_621_);
    return v_res_632_;
}
pub unsafe fn l_Fin_lastCases___redArg___lam__0(
    mut v_cast_633_: *mut LeanObject,
    mut v_i_634_: *mut LeanObject,
    mut v_x_635_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_636_: *mut LeanObject = core::ptr::null_mut();
    v___x_636_ = lean_apply_1(v_cast_633_, v_i_634_);
    return v___x_636_;
}
pub unsafe fn l_Fin_lastCases___redArg___lam__0___boxed(
    mut v_cast_637_: *mut LeanObject,
    mut v_i_638_: *mut LeanObject,
    mut v_x_639_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_640_: *mut LeanObject = core::ptr::null_mut();
    v_res_640_ = l_Fin_lastCases___redArg___lam__0(v_cast_637_, v_i_638_, v_x_639_);
    lean_dec(v_x_639_);
    return v_res_640_;
}
pub unsafe fn l_Fin_lastCases___redArg(
    mut v_n_641_: *mut LeanObject,
    mut v_last_642_: *mut LeanObject,
    mut v_cast_643_: *mut LeanObject,
    mut v_i_644_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_646_: *mut LeanObject = core::ptr::null_mut();
    v___f_645_ = lean_alloc_closure(
        l_Fin_lastCases___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_645_, 0, v_cast_643_);
    v___x_646_ = l_Fin_reverseInduction_go___redArg(v___f_645_, v_i_644_, v_n_641_, v_last_642_);
    return v___x_646_;
}
pub unsafe fn l_Fin_lastCases___redArg___boxed(
    mut v_n_647_: *mut LeanObject,
    mut v_last_648_: *mut LeanObject,
    mut v_cast_649_: *mut LeanObject,
    mut v_i_650_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_651_: *mut LeanObject = core::ptr::null_mut();
    v_res_651_ = l_Fin_lastCases___redArg(v_n_647_, v_last_648_, v_cast_649_, v_i_650_);
    lean_dec(v_i_650_);
    return v_res_651_;
}
pub unsafe fn l_Fin_lastCases(
    mut v_n_652_: *mut LeanObject,
    mut v_motive_653_: *mut LeanObject,
    mut v_last_654_: *mut LeanObject,
    mut v_cast_655_: *mut LeanObject,
    mut v_i_656_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_657_: *mut LeanObject = core::ptr::null_mut();
    v___x_657_ = l_Fin_lastCases___redArg(v_n_652_, v_last_654_, v_cast_655_, v_i_656_);
    return v___x_657_;
}
pub unsafe fn l_Fin_lastCases___boxed(
    mut v_n_658_: *mut LeanObject,
    mut v_motive_659_: *mut LeanObject,
    mut v_last_660_: *mut LeanObject,
    mut v_cast_661_: *mut LeanObject,
    mut v_i_662_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_663_: *mut LeanObject = core::ptr::null_mut();
    v_res_663_ = l_Fin_lastCases(v_n_658_, v_motive_659_, v_last_660_, v_cast_661_, v_i_662_);
    lean_dec(v_i_662_);
    return v_res_663_;
}
pub unsafe fn l_Fin_addCases___redArg(
    mut v_m_664_: *mut LeanObject,
    mut v_left_665_: *mut LeanObject,
    mut v_right_666_: *mut LeanObject,
    mut v_i_667_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_668_: u8 = 0;
    v___x_668_ = lean_nat_dec_lt(v_i_667_, v_m_664_);
    if v___x_668_ == 0 {
        let mut v___x_669_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_670_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_left_665_);
        v___x_669_ = lean_nat_sub(v_i_667_, v_m_664_);
        lean_dec(v_i_667_);
        v___x_670_ = lean_apply_1(v_right_666_, v___x_669_);
        return v___x_670_;
    } else {
        let mut v___x_671_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_right_666_);
        v___x_671_ = lean_apply_1(v_left_665_, v_i_667_);
        return v___x_671_;
    }
}
pub unsafe fn l_Fin_addCases___redArg___boxed(
    mut v_m_672_: *mut LeanObject,
    mut v_left_673_: *mut LeanObject,
    mut v_right_674_: *mut LeanObject,
    mut v_i_675_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_676_: *mut LeanObject = core::ptr::null_mut();
    v_res_676_ = l_Fin_addCases___redArg(v_m_672_, v_left_673_, v_right_674_, v_i_675_);
    lean_dec(v_m_672_);
    return v_res_676_;
}
pub unsafe fn l_Fin_addCases(
    mut v_m_677_: *mut LeanObject,
    mut v_n_678_: *mut LeanObject,
    mut v_motive_679_: *mut LeanObject,
    mut v_left_680_: *mut LeanObject,
    mut v_right_681_: *mut LeanObject,
    mut v_i_682_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_683_: *mut LeanObject = core::ptr::null_mut();
    v___x_683_ = l_Fin_addCases___redArg(v_m_677_, v_left_680_, v_right_681_, v_i_682_);
    return v___x_683_;
}
pub unsafe fn l_Fin_addCases___boxed(
    mut v_m_684_: *mut LeanObject,
    mut v_n_685_: *mut LeanObject,
    mut v_motive_686_: *mut LeanObject,
    mut v_left_687_: *mut LeanObject,
    mut v_right_688_: *mut LeanObject,
    mut v_i_689_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_690_: *mut LeanObject = core::ptr::null_mut();
    v_res_690_ = l_Fin_addCases(
        v_m_684_,
        v_n_685_,
        v_motive_686_,
        v_left_687_,
        v_right_688_,
        v_i_689_,
    );
    lean_dec(v_n_685_);
    lean_dec(v_m_684_);
    return v_res_690_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Fin_Lemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Ext(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Div_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Order_Classes(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_NotationExtra(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Linear(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_TacticsExtra(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Hints(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Fin_Lemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Fin_Lemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Ext(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Div_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Order_Classes(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_NotationExtra(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Linear(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_TacticsExtra(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Hints(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Fin_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Fin_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Fin_Lemmas(builtin);
}
