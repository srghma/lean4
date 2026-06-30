// Lean compiler output
// Module: Init.Data.Fin.Basic
// Imports: Init.Data.Nat.Bitwise.Basic Init.Data.Nat.Basic Init.Data.Nat.Div.Basic
use crate::ffi::{
    lean_nat_add, lean_nat_div, lean_nat_land, lean_nat_lor, lean_nat_lxor, lean_nat_mod,
    lean_nat_mul, lean_nat_shiftl, lean_nat_shiftr, lean_nat_sub,
};
use crate::r#gen::Init::Data::Nat::Basic::{
    initialize_Init_Data_Nat_Basic, runtime_initialize_Init_Data_Nat_Basic,
};
use crate::r#gen::Init::Data::Nat::Bitwise::Basic::{
    initialize_Init_Data_Nat_Bitwise_Basic, runtime_initialize_Init_Data_Nat_Bitwise_Basic,
};
use crate::r#gen::Init::Data::Nat::Div::Basic::{
    initialize_Init_Data_Nat_Div_Basic, runtime_initialize_Init_Data_Nat_Div_Basic,
};
pub static l_Fin_coeToNat___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Fin_coeToNat___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Fin_coeToNat___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Fin_coeToNat___closed__0_value) as *mut leanh::LeanObject;
pub unsafe fn l_Fin_coeToNat___lam__0(
    mut v_v_355_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_v_355_);
    return v_v_355_;
}
pub unsafe fn l_Fin_coeToNat___lam__0___boxed(
    mut v_v_356_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_357_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_357_ = l_Fin_coeToNat___lam__0(v_v_356_);
    leanh::lean_dec(v_v_356_);
    return v_res_357_;
}
pub unsafe fn l_Fin_coeToNat(
    mut v_n_359_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_360_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_360_ = l_Fin_coeToNat___closed__0;
    return v___f_360_;
}
pub unsafe fn l_Fin_coeToNat___boxed(
    mut v_n_361_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_362_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_362_ = l_Fin_coeToNat(v_n_361_);
    leanh::lean_dec(v_n_361_);
    return v_res_362_;
}
pub unsafe fn l_Fin_elim0(
    mut v_00_u03b1_363_: *mut leanh::LeanObject,
    mut v_x_364_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    core::hint::unreachable_unchecked();
}
pub unsafe fn l_Fin_elim0___boxed(
    mut v_00_u03b1_365_: *mut leanh::LeanObject,
    mut v_x_366_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_367_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_367_ = l_Fin_elim0(v_00_u03b1_365_, v_x_366_);
    leanh::lean_dec(v_x_366_);
    return v_res_367_;
}
pub unsafe fn l_Fin_succ___redArg(
    mut v_x_368_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_370_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_369_ = leanh::lean_unsigned_to_nat(1);
    v___x_370_ = lean_nat_add(v_x_368_, v___x_369_);
    return v___x_370_;
}
pub unsafe fn l_Fin_succ___redArg___boxed(
    mut v_x_371_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_372_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_372_ = l_Fin_succ___redArg(v_x_371_);
    leanh::lean_dec(v_x_371_);
    return v_res_372_;
}
pub unsafe fn l_Fin_succ(
    mut v_n_373_: *mut leanh::LeanObject,
    mut v_x_374_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_375_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_375_ = l_Fin_succ___redArg(v_x_374_);
    return v___x_375_;
}
pub unsafe fn l_Fin_succ___boxed(
    mut v_n_376_: *mut leanh::LeanObject,
    mut v_x_377_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_378_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_378_ = l_Fin_succ(v_n_376_, v_x_377_);
    leanh::lean_dec(v_x_377_);
    leanh::lean_dec(v_n_376_);
    return v_res_378_;
}
pub unsafe fn l_Fin_ofNat___redArg(
    mut v_n_379_: *mut leanh::LeanObject,
    mut v_a_380_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_381_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_381_ = lean_nat_mod(v_a_380_, v_n_379_);
    return v___x_381_;
}
pub unsafe fn l_Fin_ofNat___redArg___boxed(
    mut v_n_382_: *mut leanh::LeanObject,
    mut v_a_383_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_384_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_384_ = l_Fin_ofNat___redArg(v_n_382_, v_a_383_);
    leanh::lean_dec(v_a_383_);
    leanh::lean_dec(v_n_382_);
    return v_res_384_;
}
pub unsafe fn l_Fin_ofNat(
    mut v_n_385_: *mut leanh::LeanObject,
    mut v_inst_386_: *mut leanh::LeanObject,
    mut v_a_387_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_388_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_388_ = lean_nat_mod(v_a_387_, v_n_385_);
    return v___x_388_;
}
pub unsafe fn l_Fin_ofNat___boxed(
    mut v_n_389_: *mut leanh::LeanObject,
    mut v_inst_390_: *mut leanh::LeanObject,
    mut v_a_391_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_392_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_392_ = l_Fin_ofNat(v_n_389_, v_inst_390_, v_a_391_);
    leanh::lean_dec(v_a_391_);
    leanh::lean_dec(v_n_389_);
    return v_res_392_;
}
pub unsafe fn l_Fin_toNat___redArg(
    mut v_i_393_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_i_393_);
    return v_i_393_;
}
pub unsafe fn l_Fin_toNat___redArg___boxed(
    mut v_i_394_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_395_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_395_ = l_Fin_toNat___redArg(v_i_394_);
    leanh::lean_dec(v_i_394_);
    return v_res_395_;
}
pub unsafe fn l_Fin_toNat(
    mut v_n_396_: *mut leanh::LeanObject,
    mut v_i_397_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_i_397_);
    return v_i_397_;
}
pub unsafe fn l_Fin_toNat___boxed(
    mut v_n_398_: *mut leanh::LeanObject,
    mut v_i_399_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_400_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_400_ = l_Fin_toNat(v_n_398_, v_i_399_);
    leanh::lean_dec(v_i_399_);
    leanh::lean_dec(v_n_398_);
    return v_res_400_;
}
pub unsafe fn l_Fin_add(
    mut v_n_401_: *mut leanh::LeanObject,
    mut v_x_402_: *mut leanh::LeanObject,
    mut v_x_403_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_405_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_404_ = lean_nat_add(v_x_402_, v_x_403_);
    v___x_405_ = lean_nat_mod(v___x_404_, v_n_401_);
    leanh::lean_dec(v___x_404_);
    return v___x_405_;
}
pub unsafe fn l_Fin_add___boxed(
    mut v_n_406_: *mut leanh::LeanObject,
    mut v_x_407_: *mut leanh::LeanObject,
    mut v_x_408_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_409_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_409_ = l_Fin_add(v_n_406_, v_x_407_, v_x_408_);
    leanh::lean_dec(v_x_408_);
    leanh::lean_dec(v_x_407_);
    leanh::lean_dec(v_n_406_);
    return v_res_409_;
}
pub unsafe fn l_Fin_mul(
    mut v_n_410_: *mut leanh::LeanObject,
    mut v_x_411_: *mut leanh::LeanObject,
    mut v_x_412_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_414_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_413_ = lean_nat_mul(v_x_411_, v_x_412_);
    v___x_414_ = lean_nat_mod(v___x_413_, v_n_410_);
    leanh::lean_dec(v___x_413_);
    return v___x_414_;
}
pub unsafe fn l_Fin_mul___boxed(
    mut v_n_415_: *mut leanh::LeanObject,
    mut v_x_416_: *mut leanh::LeanObject,
    mut v_x_417_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_418_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_418_ = l_Fin_mul(v_n_415_, v_x_416_, v_x_417_);
    leanh::lean_dec(v_x_417_);
    leanh::lean_dec(v_x_416_);
    leanh::lean_dec(v_n_415_);
    return v_res_418_;
}
pub unsafe fn l_Fin_sub(
    mut v_n_419_: *mut leanh::LeanObject,
    mut v_x_420_: *mut leanh::LeanObject,
    mut v_x_421_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_424_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_422_ = lean_nat_sub(v_n_419_, v_x_421_);
    v___x_423_ = lean_nat_add(v___x_422_, v_x_420_);
    leanh::lean_dec(v___x_422_);
    v___x_424_ = lean_nat_mod(v___x_423_, v_n_419_);
    leanh::lean_dec(v___x_423_);
    return v___x_424_;
}
pub unsafe fn l_Fin_sub___boxed(
    mut v_n_425_: *mut leanh::LeanObject,
    mut v_x_426_: *mut leanh::LeanObject,
    mut v_x_427_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_428_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_428_ = l_Fin_sub(v_n_425_, v_x_426_, v_x_427_);
    leanh::lean_dec(v_x_427_);
    leanh::lean_dec(v_x_426_);
    leanh::lean_dec(v_n_425_);
    return v_res_428_;
}
pub unsafe fn l_Fin_mod___redArg(
    mut v_x_429_: *mut leanh::LeanObject,
    mut v_x_430_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_431_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_431_ = lean_nat_mod(v_x_429_, v_x_430_);
    return v___x_431_;
}
pub unsafe fn l_Fin_mod___redArg___boxed(
    mut v_x_432_: *mut leanh::LeanObject,
    mut v_x_433_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_434_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_434_ = l_Fin_mod___redArg(v_x_432_, v_x_433_);
    leanh::lean_dec(v_x_433_);
    leanh::lean_dec(v_x_432_);
    return v_res_434_;
}
pub unsafe fn l_Fin_mod(
    mut v_n_435_: *mut leanh::LeanObject,
    mut v_x_436_: *mut leanh::LeanObject,
    mut v_x_437_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_438_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_438_ = lean_nat_mod(v_x_436_, v_x_437_);
    return v___x_438_;
}
pub unsafe fn l_Fin_mod___boxed(
    mut v_n_439_: *mut leanh::LeanObject,
    mut v_x_440_: *mut leanh::LeanObject,
    mut v_x_441_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_442_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_442_ = l_Fin_mod(v_n_439_, v_x_440_, v_x_441_);
    leanh::lean_dec(v_x_441_);
    leanh::lean_dec(v_x_440_);
    leanh::lean_dec(v_n_439_);
    return v_res_442_;
}
pub unsafe fn l_Fin_div___redArg(
    mut v_x_443_: *mut leanh::LeanObject,
    mut v_x_444_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_445_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_445_ = lean_nat_div(v_x_443_, v_x_444_);
    return v___x_445_;
}
pub unsafe fn l_Fin_div___redArg___boxed(
    mut v_x_446_: *mut leanh::LeanObject,
    mut v_x_447_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_448_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_448_ = l_Fin_div___redArg(v_x_446_, v_x_447_);
    leanh::lean_dec(v_x_447_);
    leanh::lean_dec(v_x_446_);
    return v_res_448_;
}
pub unsafe fn l_Fin_div(
    mut v_n_449_: *mut leanh::LeanObject,
    mut v_x_450_: *mut leanh::LeanObject,
    mut v_x_451_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_452_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_452_ = lean_nat_div(v_x_450_, v_x_451_);
    return v___x_452_;
}
pub unsafe fn l_Fin_div___boxed(
    mut v_n_453_: *mut leanh::LeanObject,
    mut v_x_454_: *mut leanh::LeanObject,
    mut v_x_455_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_456_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_456_ = l_Fin_div(v_n_453_, v_x_454_, v_x_455_);
    leanh::lean_dec(v_x_455_);
    leanh::lean_dec(v_x_454_);
    leanh::lean_dec(v_n_453_);
    return v_res_456_;
}
pub unsafe fn l_Fin_modn___redArg(
    mut v_x_457_: *mut leanh::LeanObject,
    mut v_x_458_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_459_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_459_ = lean_nat_mod(v_x_457_, v_x_458_);
    return v___x_459_;
}
pub unsafe fn l_Fin_modn___redArg___boxed(
    mut v_x_460_: *mut leanh::LeanObject,
    mut v_x_461_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_462_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_462_ = l_Fin_modn___redArg(v_x_460_, v_x_461_);
    leanh::lean_dec(v_x_461_);
    leanh::lean_dec(v_x_460_);
    return v_res_462_;
}
pub unsafe fn l_Fin_modn(
    mut v_n_463_: *mut leanh::LeanObject,
    mut v_x_464_: *mut leanh::LeanObject,
    mut v_x_465_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_466_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_466_ = lean_nat_mod(v_x_464_, v_x_465_);
    return v___x_466_;
}
pub unsafe fn l_Fin_modn___boxed(
    mut v_n_467_: *mut leanh::LeanObject,
    mut v_x_468_: *mut leanh::LeanObject,
    mut v_x_469_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_470_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_470_ = l_Fin_modn(v_n_467_, v_x_468_, v_x_469_);
    leanh::lean_dec(v_x_469_);
    leanh::lean_dec(v_x_468_);
    leanh::lean_dec(v_n_467_);
    return v_res_470_;
}
pub unsafe fn l_Fin_land(
    mut v_n_471_: *mut leanh::LeanObject,
    mut v_x_472_: *mut leanh::LeanObject,
    mut v_x_473_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_475_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_474_ = lean_nat_land(v_x_472_, v_x_473_);
    v___x_475_ = lean_nat_mod(v___x_474_, v_n_471_);
    leanh::lean_dec(v___x_474_);
    return v___x_475_;
}
pub unsafe fn l_Fin_land___boxed(
    mut v_n_476_: *mut leanh::LeanObject,
    mut v_x_477_: *mut leanh::LeanObject,
    mut v_x_478_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_479_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_479_ = l_Fin_land(v_n_476_, v_x_477_, v_x_478_);
    leanh::lean_dec(v_x_478_);
    leanh::lean_dec(v_x_477_);
    leanh::lean_dec(v_n_476_);
    return v_res_479_;
}
pub unsafe fn l_Fin_lor(
    mut v_n_480_: *mut leanh::LeanObject,
    mut v_x_481_: *mut leanh::LeanObject,
    mut v_x_482_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_484_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_483_ = lean_nat_lor(v_x_481_, v_x_482_);
    v___x_484_ = lean_nat_mod(v___x_483_, v_n_480_);
    leanh::lean_dec(v___x_483_);
    return v___x_484_;
}
pub unsafe fn l_Fin_lor___boxed(
    mut v_n_485_: *mut leanh::LeanObject,
    mut v_x_486_: *mut leanh::LeanObject,
    mut v_x_487_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_488_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_488_ = l_Fin_lor(v_n_485_, v_x_486_, v_x_487_);
    leanh::lean_dec(v_x_487_);
    leanh::lean_dec(v_x_486_);
    leanh::lean_dec(v_n_485_);
    return v_res_488_;
}
pub unsafe fn l_Fin_xor(
    mut v_n_489_: *mut leanh::LeanObject,
    mut v_x_490_: *mut leanh::LeanObject,
    mut v_x_491_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_493_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_492_ = lean_nat_lxor(v_x_490_, v_x_491_);
    v___x_493_ = lean_nat_mod(v___x_492_, v_n_489_);
    leanh::lean_dec(v___x_492_);
    return v___x_493_;
}
pub unsafe fn l_Fin_xor___boxed(
    mut v_n_494_: *mut leanh::LeanObject,
    mut v_x_495_: *mut leanh::LeanObject,
    mut v_x_496_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_497_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_497_ = l_Fin_xor(v_n_494_, v_x_495_, v_x_496_);
    leanh::lean_dec(v_x_496_);
    leanh::lean_dec(v_x_495_);
    leanh::lean_dec(v_n_494_);
    return v_res_497_;
}
pub unsafe fn l_Fin_shiftLeft(
    mut v_n_498_: *mut leanh::LeanObject,
    mut v_x_499_: *mut leanh::LeanObject,
    mut v_x_500_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_502_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_501_ = lean_nat_shiftl(v_x_499_, v_x_500_);
    v___x_502_ = lean_nat_mod(v___x_501_, v_n_498_);
    leanh::lean_dec(v___x_501_);
    return v___x_502_;
}
pub unsafe fn l_Fin_shiftLeft___boxed(
    mut v_n_503_: *mut leanh::LeanObject,
    mut v_x_504_: *mut leanh::LeanObject,
    mut v_x_505_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_506_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_506_ = l_Fin_shiftLeft(v_n_503_, v_x_504_, v_x_505_);
    leanh::lean_dec(v_x_505_);
    leanh::lean_dec(v_x_504_);
    leanh::lean_dec(v_n_503_);
    return v_res_506_;
}
pub unsafe fn l_Fin_shiftRight(
    mut v_n_507_: *mut leanh::LeanObject,
    mut v_x_508_: *mut leanh::LeanObject,
    mut v_x_509_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_511_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_510_ = lean_nat_shiftr(v_x_508_, v_x_509_);
    v___x_511_ = lean_nat_mod(v___x_510_, v_n_507_);
    leanh::lean_dec(v___x_510_);
    return v___x_511_;
}
pub unsafe fn l_Fin_shiftRight___boxed(
    mut v_n_512_: *mut leanh::LeanObject,
    mut v_x_513_: *mut leanh::LeanObject,
    mut v_x_514_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_515_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_515_ = l_Fin_shiftRight(v_n_512_, v_x_513_, v_x_514_);
    leanh::lean_dec(v_x_514_);
    leanh::lean_dec(v_x_513_);
    leanh::lean_dec(v_n_512_);
    return v_res_515_;
}
pub unsafe fn l_Fin_instAdd(
    mut v_n_516_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_517_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_517_ =
        leanh::lean_alloc_closure(l_Fin_add___boxed as *mut core::ffi::c_void, 3, 1);
    leanh::lean_closure_set(v___x_517_, 0, v_n_516_);
    return v___x_517_;
}
pub unsafe fn l_Fin_instSub(
    mut v_n_518_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_519_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_519_ =
        leanh::lean_alloc_closure(l_Fin_sub___boxed as *mut core::ffi::c_void, 3, 1);
    leanh::lean_closure_set(v___x_519_, 0, v_n_518_);
    return v___x_519_;
}
pub unsafe fn l_Fin_instMul(
    mut v_n_520_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_521_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_521_ =
        leanh::lean_alloc_closure(l_Fin_mul___boxed as *mut core::ffi::c_void, 3, 1);
    leanh::lean_closure_set(v___x_521_, 0, v_n_520_);
    return v___x_521_;
}
pub unsafe fn l_Fin_instMod(
    mut v_n_522_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_523_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_523_ =
        leanh::lean_alloc_closure(l_Fin_mod___boxed as *mut core::ffi::c_void, 3, 1);
    leanh::lean_closure_set(v___x_523_, 0, v_n_522_);
    return v___x_523_;
}
pub unsafe fn l_Fin_instDiv(
    mut v_n_524_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_525_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_525_ =
        leanh::lean_alloc_closure(l_Fin_div___boxed as *mut core::ffi::c_void, 3, 1);
    leanh::lean_closure_set(v___x_525_, 0, v_n_524_);
    return v___x_525_;
}
pub unsafe fn l_Fin_instAndOp(
    mut v_n_526_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_527_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_527_ =
        leanh::lean_alloc_closure(l_Fin_land___boxed as *mut core::ffi::c_void, 3, 1);
    leanh::lean_closure_set(v___x_527_, 0, v_n_526_);
    return v___x_527_;
}
pub unsafe fn l_Fin_instOrOp(
    mut v_n_528_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_529_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_529_ =
        leanh::lean_alloc_closure(l_Fin_lor___boxed as *mut core::ffi::c_void, 3, 1);
    leanh::lean_closure_set(v___x_529_, 0, v_n_528_);
    return v___x_529_;
}
pub unsafe fn l_Fin_instXorOp(
    mut v_n_530_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_531_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_531_ =
        leanh::lean_alloc_closure(l_Fin_xor___boxed as *mut core::ffi::c_void, 3, 1);
    leanh::lean_closure_set(v___x_531_, 0, v_n_530_);
    return v___x_531_;
}
pub unsafe fn l_Fin_instShiftLeft(
    mut v_n_532_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_533_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_533_ =
        leanh::lean_alloc_closure(l_Fin_shiftLeft___boxed as *mut core::ffi::c_void, 3, 1);
    leanh::lean_closure_set(v___x_533_, 0, v_n_532_);
    return v___x_533_;
}
pub unsafe fn l_Fin_instShiftRight(
    mut v_n_534_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_535_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_535_ =
        leanh::lean_alloc_closure(l_Fin_shiftRight___boxed as *mut core::ffi::c_void, 3, 1);
    leanh::lean_closure_set(v___x_535_, 0, v_n_534_);
    return v___x_535_;
}
pub unsafe fn l_Fin_instOfNat___redArg(
    mut v_n_536_: *mut leanh::LeanObject,
    mut v_i_537_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_538_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_538_ = lean_nat_mod(v_i_537_, v_n_536_);
    return v___x_538_;
}
pub unsafe fn l_Fin_instOfNat___redArg___boxed(
    mut v_n_539_: *mut leanh::LeanObject,
    mut v_i_540_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_541_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_541_ = l_Fin_instOfNat___redArg(v_n_539_, v_i_540_);
    leanh::lean_dec(v_i_540_);
    leanh::lean_dec(v_n_539_);
    return v_res_541_;
}
pub unsafe fn l_Fin_instOfNat(
    mut v_n_542_: *mut leanh::LeanObject,
    mut v_inst_543_: *mut leanh::LeanObject,
    mut v_i_544_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_545_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_545_ = lean_nat_mod(v_i_544_, v_n_542_);
    return v___x_545_;
}
pub unsafe fn l_Fin_instOfNat___boxed(
    mut v_n_546_: *mut leanh::LeanObject,
    mut v_inst_547_: *mut leanh::LeanObject,
    mut v_i_548_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_549_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_549_ = l_Fin_instOfNat(v_n_546_, v_inst_547_, v_i_548_);
    leanh::lean_dec(v_i_548_);
    leanh::lean_dec(v_n_546_);
    return v_res_549_;
}
pub unsafe fn l_Fin_neg___lam__0(
    mut v_n_550_: *mut leanh::LeanObject,
    mut v_a_551_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_553_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_552_ = lean_nat_sub(v_n_550_, v_a_551_);
    v___x_553_ = lean_nat_mod(v___x_552_, v_n_550_);
    leanh::lean_dec(v___x_552_);
    return v___x_553_;
}
pub unsafe fn l_Fin_neg___lam__0___boxed(
    mut v_n_554_: *mut leanh::LeanObject,
    mut v_a_555_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_556_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_556_ = l_Fin_neg___lam__0(v_n_554_, v_a_555_);
    leanh::lean_dec(v_a_555_);
    leanh::lean_dec(v_n_554_);
    return v_res_556_;
}
pub unsafe fn l_Fin_neg(
    mut v_n_557_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_558_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_558_ = leanh::lean_alloc_closure(
        l_Fin_neg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_558_, 0, v_n_557_);
    return v___f_558_;
}
pub unsafe fn l_Fin_instInhabited___redArg(
    mut v_n_559_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_561_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_560_ = leanh::lean_unsigned_to_nat(0);
    v___x_561_ = lean_nat_mod(v___x_560_, v_n_559_);
    return v___x_561_;
}
pub unsafe fn l_Fin_instInhabited___redArg___boxed(
    mut v_n_562_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_563_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_563_ = l_Fin_instInhabited___redArg(v_n_562_);
    leanh::lean_dec(v_n_562_);
    return v_res_563_;
}
pub unsafe fn l_Fin_instInhabited(
    mut v_n_564_: *mut leanh::LeanObject,
    mut v_inst_565_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_566_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_566_ = l_Fin_instInhabited___redArg(v_n_564_);
    return v___x_566_;
}
pub unsafe fn l_Fin_instInhabited___boxed(
    mut v_n_567_: *mut leanh::LeanObject,
    mut v_inst_568_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_569_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_569_ = l_Fin_instInhabited(v_n_567_, v_inst_568_);
    leanh::lean_dec(v_n_567_);
    return v_res_569_;
}
pub unsafe fn l___private_Init_Data_Fin_Basic_0__Fin_modn_match__1_splitter___redArg(
    mut v_x_570_: *mut leanh::LeanObject,
    mut v_x_571_: *mut leanh::LeanObject,
    mut v_h__1_572_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_573_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_573_ =
        leanh::lean_apply_3(v_h__1_572_, v_x_570_, leanh::lean_box(0), v_x_571_);
    return v___x_573_;
}
pub unsafe fn l___private_Init_Data_Fin_Basic_0__Fin_modn_match__1_splitter(
    mut v_n_574_: *mut leanh::LeanObject,
    mut v_motive_575_: *mut leanh::LeanObject,
    mut v_x_576_: *mut leanh::LeanObject,
    mut v_x_577_: *mut leanh::LeanObject,
    mut v_h__1_578_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_579_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_579_ =
        leanh::lean_apply_3(v_h__1_578_, v_x_576_, leanh::lean_box(0), v_x_577_);
    return v___x_579_;
}
pub unsafe fn l___private_Init_Data_Fin_Basic_0__Fin_modn_match__1_splitter___boxed(
    mut v_n_580_: *mut leanh::LeanObject,
    mut v_motive_581_: *mut leanh::LeanObject,
    mut v_x_582_: *mut leanh::LeanObject,
    mut v_x_583_: *mut leanh::LeanObject,
    mut v_h__1_584_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_585_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_585_ = l___private_Init_Data_Fin_Basic_0__Fin_modn_match__1_splitter(
        v_n_580_,
        v_motive_581_,
        v_x_582_,
        v_x_583_,
        v_h__1_584_,
    );
    leanh::lean_dec(v_n_580_);
    return v_res_585_;
}
pub unsafe fn l_Fin_last(
    mut v_n_586_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_n_586_);
    return v_n_586_;
}
pub unsafe fn l_Fin_last___boxed(
    mut v_n_587_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_588_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_588_ = l_Fin_last(v_n_587_);
    leanh::lean_dec(v_n_587_);
    return v_res_588_;
}
pub unsafe fn l_Fin_castLT___redArg(
    mut v_i_589_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_i_589_);
    return v_i_589_;
}
pub unsafe fn l_Fin_castLT___redArg___boxed(
    mut v_i_590_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_591_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_591_ = l_Fin_castLT___redArg(v_i_590_);
    leanh::lean_dec(v_i_590_);
    return v_res_591_;
}
pub unsafe fn l_Fin_castLT(
    mut v_n_592_: *mut leanh::LeanObject,
    mut v_m_593_: *mut leanh::LeanObject,
    mut v_i_594_: *mut leanh::LeanObject,
    mut v_h_595_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_i_594_);
    return v_i_594_;
}
pub unsafe fn l_Fin_castLT___boxed(
    mut v_n_596_: *mut leanh::LeanObject,
    mut v_m_597_: *mut leanh::LeanObject,
    mut v_i_598_: *mut leanh::LeanObject,
    mut v_h_599_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_600_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_600_ = l_Fin_castLT(v_n_596_, v_m_597_, v_i_598_, v_h_599_);
    leanh::lean_dec(v_i_598_);
    leanh::lean_dec(v_m_597_);
    leanh::lean_dec(v_n_596_);
    return v_res_600_;
}
pub unsafe fn l_Fin_castLE___redArg(
    mut v_i_601_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_i_601_);
    return v_i_601_;
}
pub unsafe fn l_Fin_castLE___redArg___boxed(
    mut v_i_602_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_603_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_603_ = l_Fin_castLE___redArg(v_i_602_);
    leanh::lean_dec(v_i_602_);
    return v_res_603_;
}
pub unsafe fn l_Fin_castLE(
    mut v_n_604_: *mut leanh::LeanObject,
    mut v_m_605_: *mut leanh::LeanObject,
    mut v_h_606_: *mut leanh::LeanObject,
    mut v_i_607_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_i_607_);
    return v_i_607_;
}
pub unsafe fn l_Fin_castLE___boxed(
    mut v_n_608_: *mut leanh::LeanObject,
    mut v_m_609_: *mut leanh::LeanObject,
    mut v_h_610_: *mut leanh::LeanObject,
    mut v_i_611_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_612_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_612_ = l_Fin_castLE(v_n_608_, v_m_609_, v_h_610_, v_i_611_);
    leanh::lean_dec(v_i_611_);
    leanh::lean_dec(v_m_609_);
    leanh::lean_dec(v_n_608_);
    return v_res_612_;
}
pub unsafe fn l_Fin_cast___redArg(
    mut v_i_613_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_i_613_);
    return v_i_613_;
}
pub unsafe fn l_Fin_cast___redArg___boxed(
    mut v_i_614_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_615_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_615_ = l_Fin_cast___redArg(v_i_614_);
    leanh::lean_dec(v_i_614_);
    return v_res_615_;
}
pub unsafe fn l_Fin_cast(
    mut v_n_616_: *mut leanh::LeanObject,
    mut v_m_617_: *mut leanh::LeanObject,
    mut v_eq_618_: *mut leanh::LeanObject,
    mut v_i_619_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_i_619_);
    return v_i_619_;
}
pub unsafe fn l_Fin_cast___boxed(
    mut v_n_620_: *mut leanh::LeanObject,
    mut v_m_621_: *mut leanh::LeanObject,
    mut v_eq_622_: *mut leanh::LeanObject,
    mut v_i_623_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_624_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_624_ = l_Fin_cast(v_n_620_, v_m_621_, v_eq_622_, v_i_623_);
    leanh::lean_dec(v_i_623_);
    leanh::lean_dec(v_m_621_);
    leanh::lean_dec(v_n_620_);
    return v_res_624_;
}
pub unsafe fn l_Fin_castAdd___redArg(
    mut v_i_625_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_i_625_);
    return v_i_625_;
}
pub unsafe fn l_Fin_castAdd___redArg___boxed(
    mut v_i_626_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_627_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_627_ = l_Fin_castAdd___redArg(v_i_626_);
    leanh::lean_dec(v_i_626_);
    return v_res_627_;
}
pub unsafe fn l_Fin_castAdd(
    mut v_n_628_: *mut leanh::LeanObject,
    mut v_m_629_: *mut leanh::LeanObject,
    mut v_i_630_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_i_630_);
    return v_i_630_;
}
pub unsafe fn l_Fin_castAdd___boxed(
    mut v_n_631_: *mut leanh::LeanObject,
    mut v_m_632_: *mut leanh::LeanObject,
    mut v_i_633_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_634_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_634_ = l_Fin_castAdd(v_n_631_, v_m_632_, v_i_633_);
    leanh::lean_dec(v_i_633_);
    leanh::lean_dec(v_m_632_);
    leanh::lean_dec(v_n_631_);
    return v_res_634_;
}
pub unsafe fn l_Fin_castSucc___redArg(
    mut v_a_635_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_a_635_);
    return v_a_635_;
}
pub unsafe fn l_Fin_castSucc___redArg___boxed(
    mut v_a_636_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_637_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_637_ = l_Fin_castSucc___redArg(v_a_636_);
    leanh::lean_dec(v_a_636_);
    return v_res_637_;
}
pub unsafe fn l_Fin_castSucc(
    mut v_n_638_: *mut leanh::LeanObject,
    mut v_a_639_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_a_639_);
    return v_a_639_;
}
pub unsafe fn l_Fin_castSucc___boxed(
    mut v_n_640_: *mut leanh::LeanObject,
    mut v_a_641_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_642_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_642_ = l_Fin_castSucc(v_n_640_, v_a_641_);
    leanh::lean_dec(v_a_641_);
    leanh::lean_dec(v_n_640_);
    return v_res_642_;
}
pub unsafe fn l_Fin_addNat___redArg(
    mut v_i_643_: *mut leanh::LeanObject,
    mut v_m_644_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_645_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_645_ = lean_nat_add(v_i_643_, v_m_644_);
    return v___x_645_;
}
pub unsafe fn l_Fin_addNat___redArg___boxed(
    mut v_i_646_: *mut leanh::LeanObject,
    mut v_m_647_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_648_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_648_ = l_Fin_addNat___redArg(v_i_646_, v_m_647_);
    leanh::lean_dec(v_m_647_);
    leanh::lean_dec(v_i_646_);
    return v_res_648_;
}
pub unsafe fn l_Fin_addNat(
    mut v_n_649_: *mut leanh::LeanObject,
    mut v_i_650_: *mut leanh::LeanObject,
    mut v_m_651_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_652_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_652_ = lean_nat_add(v_i_650_, v_m_651_);
    return v___x_652_;
}
pub unsafe fn l_Fin_addNat___boxed(
    mut v_n_653_: *mut leanh::LeanObject,
    mut v_i_654_: *mut leanh::LeanObject,
    mut v_m_655_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_656_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_656_ = l_Fin_addNat(v_n_653_, v_i_654_, v_m_655_);
    leanh::lean_dec(v_m_655_);
    leanh::lean_dec(v_i_654_);
    leanh::lean_dec(v_n_653_);
    return v_res_656_;
}
pub unsafe fn l_Fin_natAdd___redArg(
    mut v_n_657_: *mut leanh::LeanObject,
    mut v_i_658_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_659_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_659_ = lean_nat_add(v_n_657_, v_i_658_);
    return v___x_659_;
}
pub unsafe fn l_Fin_natAdd___redArg___boxed(
    mut v_n_660_: *mut leanh::LeanObject,
    mut v_i_661_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_662_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_662_ = l_Fin_natAdd___redArg(v_n_660_, v_i_661_);
    leanh::lean_dec(v_i_661_);
    leanh::lean_dec(v_n_660_);
    return v_res_662_;
}
pub unsafe fn l_Fin_natAdd(
    mut v_m_663_: *mut leanh::LeanObject,
    mut v_n_664_: *mut leanh::LeanObject,
    mut v_i_665_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_666_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_666_ = lean_nat_add(v_n_664_, v_i_665_);
    return v___x_666_;
}
pub unsafe fn l_Fin_natAdd___boxed(
    mut v_m_667_: *mut leanh::LeanObject,
    mut v_n_668_: *mut leanh::LeanObject,
    mut v_i_669_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_670_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_670_ = l_Fin_natAdd(v_m_667_, v_n_668_, v_i_669_);
    leanh::lean_dec(v_i_669_);
    leanh::lean_dec(v_n_668_);
    leanh::lean_dec(v_m_667_);
    return v_res_670_;
}
pub unsafe fn l_Fin_rev(
    mut v_n_671_: *mut leanh::LeanObject,
    mut v_i_672_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_675_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_673_ = leanh::lean_unsigned_to_nat(1);
    v___x_674_ = lean_nat_add(v_i_672_, v___x_673_);
    v___x_675_ = lean_nat_sub(v_n_671_, v___x_674_);
    leanh::lean_dec(v___x_674_);
    return v___x_675_;
}
pub unsafe fn l_Fin_rev___boxed(
    mut v_n_676_: *mut leanh::LeanObject,
    mut v_i_677_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_678_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_678_ = l_Fin_rev(v_n_676_, v_i_677_);
    leanh::lean_dec(v_i_677_);
    leanh::lean_dec(v_n_676_);
    return v_res_678_;
}
pub unsafe fn l_Fin_subNat___redArg(
    mut v_m_679_: *mut leanh::LeanObject,
    mut v_i_680_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_681_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_681_ = lean_nat_sub(v_i_680_, v_m_679_);
    return v___x_681_;
}
pub unsafe fn l_Fin_subNat___redArg___boxed(
    mut v_m_682_: *mut leanh::LeanObject,
    mut v_i_683_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_684_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_684_ = l_Fin_subNat___redArg(v_m_682_, v_i_683_);
    leanh::lean_dec(v_i_683_);
    leanh::lean_dec(v_m_682_);
    return v_res_684_;
}
pub unsafe fn l_Fin_subNat(
    mut v_n_685_: *mut leanh::LeanObject,
    mut v_m_686_: *mut leanh::LeanObject,
    mut v_i_687_: *mut leanh::LeanObject,
    mut v_h_688_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_689_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_689_ = lean_nat_sub(v_i_687_, v_m_686_);
    return v___x_689_;
}
pub unsafe fn l_Fin_subNat___boxed(
    mut v_n_690_: *mut leanh::LeanObject,
    mut v_m_691_: *mut leanh::LeanObject,
    mut v_i_692_: *mut leanh::LeanObject,
    mut v_h_693_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_694_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_694_ = l_Fin_subNat(v_n_690_, v_m_691_, v_i_692_, v_h_693_);
    leanh::lean_dec(v_i_692_);
    leanh::lean_dec(v_m_691_);
    leanh::lean_dec(v_n_690_);
    return v_res_694_;
}
pub unsafe fn l_Fin_pred___redArg(
    mut v_i_695_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_697_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_696_ = leanh::lean_unsigned_to_nat(1);
    v___x_697_ = lean_nat_sub(v_i_695_, v___x_696_);
    return v___x_697_;
}
pub unsafe fn l_Fin_pred___redArg___boxed(
    mut v_i_698_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_699_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_699_ = l_Fin_pred___redArg(v_i_698_);
    leanh::lean_dec(v_i_698_);
    return v_res_699_;
}
pub unsafe fn l_Fin_pred(
    mut v_n_700_: *mut leanh::LeanObject,
    mut v_i_701_: *mut leanh::LeanObject,
    mut v_h_702_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_704_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_703_ = leanh::lean_unsigned_to_nat(1);
    v___x_704_ = lean_nat_sub(v_i_701_, v___x_703_);
    return v___x_704_;
}
pub unsafe fn l_Fin_pred___boxed(
    mut v_n_705_: *mut leanh::LeanObject,
    mut v_i_706_: *mut leanh::LeanObject,
    mut v_h_707_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_708_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_708_ = l_Fin_pred(v_n_705_, v_i_706_, v_h_707_);
    leanh::lean_dec(v_i_706_);
    leanh::lean_dec(v_n_705_);
    return v_res_708_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Fin_Basic(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Nat_Bitwise_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Div_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Fin_Basic(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Fin_Basic(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Nat_Bitwise_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Div_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Fin_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Fin_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Fin_Basic(builtin);
}