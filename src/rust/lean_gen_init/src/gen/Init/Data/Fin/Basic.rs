// Lean compiler output
// Module: Init.Data.Fin.Basic
// Imports: Init.Data.Nat.Bitwise.Basic Init.Data.Nat.Basic Init.Data.Nat.Div.Basic
use crate::r#gen::Init::Data::Nat::Basic::{
    initialize_Init_Data_Nat_Basic, runtime_initialize_Init_Data_Nat_Basic,
};
use crate::r#gen::Init::Data::Nat::Bitwise::Basic::{
    initialize_Init_Data_Nat_Bitwise_Basic, runtime_initialize_Init_Data_Nat_Bitwise_Basic,
};
use crate::r#gen::Init::Data::Nat::Div::Basic::{
    initialize_Init_Data_Nat_Div_Basic, runtime_initialize_Init_Data_Nat_Div_Basic,
};
use crate::lean_imports_rs::Init::Data::Nat::Bitwise::Basic::{
    lean_nat_land, lean_nat_lor, lean_nat_lxor, lean_nat_shiftl, lean_nat_shiftr,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_nat_add, lean_nat_div, lean_nat_mod, lean_nat_mul, lean_nat_sub,
};
pub static l_Fin_coeToNat___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Fin_coeToNat___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Fin_coeToNat___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Fin_coeToNat___closed__0_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Fin_coeToNat___lam__0(
    mut v_v_355_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_v_355_);
    return v_v_355_;
}
pub unsafe fn l_Fin_coeToNat___lam__0___boxed(
    mut v_v_356_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_357_ = l_Fin_coeToNat___lam__0(v_v_356_);
    crate::leanh::lean_dec(v_v_356_);
    return v_res_357_;
}
pub unsafe fn l_Fin_coeToNat(
    mut v_n_359_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_360_ = l_Fin_coeToNat___closed__0;
    return v___f_360_;
}
pub unsafe fn l_Fin_coeToNat___boxed(
    mut v_n_361_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_362_ = l_Fin_coeToNat(v_n_361_);
    crate::leanh::lean_dec(v_n_361_);
    return v_res_362_;
}
pub unsafe fn l_Fin_elim0(
    mut v_00_u03b1_363_: *mut crate::leanh::LeanObject,
    mut v_x_364_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    core::hint::unreachable_unchecked();
}
pub unsafe fn l_Fin_elim0___boxed(
    mut v_00_u03b1_365_: *mut crate::leanh::LeanObject,
    mut v_x_366_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_367_ = l_Fin_elim0(v_00_u03b1_365_, v_x_366_);
    crate::leanh::lean_dec(v_x_366_);
    return v_res_367_;
}
pub unsafe fn l_Fin_succ___redArg(
    mut v_x_368_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_369_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_370_ = lean_nat_add(v_x_368_, v___x_369_);
    return v___x_370_;
}
pub unsafe fn l_Fin_succ___redArg___boxed(
    mut v_x_371_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_372_ = l_Fin_succ___redArg(v_x_371_);
    crate::leanh::lean_dec(v_x_371_);
    return v_res_372_;
}
pub unsafe fn l_Fin_succ(
    mut v_n_373_: *mut crate::leanh::LeanObject,
    mut v_x_374_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_375_ = l_Fin_succ___redArg(v_x_374_);
    return v___x_375_;
}
pub unsafe fn l_Fin_succ___boxed(
    mut v_n_376_: *mut crate::leanh::LeanObject,
    mut v_x_377_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_378_ = l_Fin_succ(v_n_376_, v_x_377_);
    crate::leanh::lean_dec(v_x_377_);
    crate::leanh::lean_dec(v_n_376_);
    return v_res_378_;
}
pub unsafe fn l_Fin_ofNat___redArg(
    mut v_n_379_: *mut crate::leanh::LeanObject,
    mut v_a_380_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_381_ = lean_nat_mod(v_a_380_, v_n_379_);
    return v___x_381_;
}
pub unsafe fn l_Fin_ofNat___redArg___boxed(
    mut v_n_382_: *mut crate::leanh::LeanObject,
    mut v_a_383_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_384_ = l_Fin_ofNat___redArg(v_n_382_, v_a_383_);
    crate::leanh::lean_dec(v_a_383_);
    crate::leanh::lean_dec(v_n_382_);
    return v_res_384_;
}
pub unsafe fn l_Fin_ofNat(
    mut v_n_385_: *mut crate::leanh::LeanObject,
    mut v_inst_386_: *mut crate::leanh::LeanObject,
    mut v_a_387_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_388_ = lean_nat_mod(v_a_387_, v_n_385_);
    return v___x_388_;
}
pub unsafe fn l_Fin_ofNat___boxed(
    mut v_n_389_: *mut crate::leanh::LeanObject,
    mut v_inst_390_: *mut crate::leanh::LeanObject,
    mut v_a_391_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_392_ = l_Fin_ofNat(v_n_389_, v_inst_390_, v_a_391_);
    crate::leanh::lean_dec(v_a_391_);
    crate::leanh::lean_dec(v_n_389_);
    return v_res_392_;
}
pub unsafe fn l_Fin_toNat___redArg(
    mut v_i_393_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_i_393_);
    return v_i_393_;
}
pub unsafe fn l_Fin_toNat___redArg___boxed(
    mut v_i_394_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_395_ = l_Fin_toNat___redArg(v_i_394_);
    crate::leanh::lean_dec(v_i_394_);
    return v_res_395_;
}
pub unsafe fn l_Fin_toNat(
    mut v_n_396_: *mut crate::leanh::LeanObject,
    mut v_i_397_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_i_397_);
    return v_i_397_;
}
pub unsafe fn l_Fin_toNat___boxed(
    mut v_n_398_: *mut crate::leanh::LeanObject,
    mut v_i_399_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_400_ = l_Fin_toNat(v_n_398_, v_i_399_);
    crate::leanh::lean_dec(v_i_399_);
    crate::leanh::lean_dec(v_n_398_);
    return v_res_400_;
}
pub unsafe fn l_Fin_add(
    mut v_n_401_: *mut crate::leanh::LeanObject,
    mut v_x_402_: *mut crate::leanh::LeanObject,
    mut v_x_403_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_404_ = lean_nat_add(v_x_402_, v_x_403_);
    v___x_405_ = lean_nat_mod(v___x_404_, v_n_401_);
    crate::leanh::lean_dec(v___x_404_);
    return v___x_405_;
}
pub unsafe fn l_Fin_add___boxed(
    mut v_n_406_: *mut crate::leanh::LeanObject,
    mut v_x_407_: *mut crate::leanh::LeanObject,
    mut v_x_408_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_409_ = l_Fin_add(v_n_406_, v_x_407_, v_x_408_);
    crate::leanh::lean_dec(v_x_408_);
    crate::leanh::lean_dec(v_x_407_);
    crate::leanh::lean_dec(v_n_406_);
    return v_res_409_;
}
pub unsafe fn l_Fin_mul(
    mut v_n_410_: *mut crate::leanh::LeanObject,
    mut v_x_411_: *mut crate::leanh::LeanObject,
    mut v_x_412_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_413_ = lean_nat_mul(v_x_411_, v_x_412_);
    v___x_414_ = lean_nat_mod(v___x_413_, v_n_410_);
    crate::leanh::lean_dec(v___x_413_);
    return v___x_414_;
}
pub unsafe fn l_Fin_mul___boxed(
    mut v_n_415_: *mut crate::leanh::LeanObject,
    mut v_x_416_: *mut crate::leanh::LeanObject,
    mut v_x_417_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_418_ = l_Fin_mul(v_n_415_, v_x_416_, v_x_417_);
    crate::leanh::lean_dec(v_x_417_);
    crate::leanh::lean_dec(v_x_416_);
    crate::leanh::lean_dec(v_n_415_);
    return v_res_418_;
}
pub unsafe fn l_Fin_sub(
    mut v_n_419_: *mut crate::leanh::LeanObject,
    mut v_x_420_: *mut crate::leanh::LeanObject,
    mut v_x_421_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_422_ = lean_nat_sub(v_n_419_, v_x_421_);
    v___x_423_ = lean_nat_add(v___x_422_, v_x_420_);
    crate::leanh::lean_dec(v___x_422_);
    v___x_424_ = lean_nat_mod(v___x_423_, v_n_419_);
    crate::leanh::lean_dec(v___x_423_);
    return v___x_424_;
}
pub unsafe fn l_Fin_sub___boxed(
    mut v_n_425_: *mut crate::leanh::LeanObject,
    mut v_x_426_: *mut crate::leanh::LeanObject,
    mut v_x_427_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_428_ = l_Fin_sub(v_n_425_, v_x_426_, v_x_427_);
    crate::leanh::lean_dec(v_x_427_);
    crate::leanh::lean_dec(v_x_426_);
    crate::leanh::lean_dec(v_n_425_);
    return v_res_428_;
}
pub unsafe fn l_Fin_mod___redArg(
    mut v_x_429_: *mut crate::leanh::LeanObject,
    mut v_x_430_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_431_ = lean_nat_mod(v_x_429_, v_x_430_);
    return v___x_431_;
}
pub unsafe fn l_Fin_mod___redArg___boxed(
    mut v_x_432_: *mut crate::leanh::LeanObject,
    mut v_x_433_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_434_ = l_Fin_mod___redArg(v_x_432_, v_x_433_);
    crate::leanh::lean_dec(v_x_433_);
    crate::leanh::lean_dec(v_x_432_);
    return v_res_434_;
}
pub unsafe fn l_Fin_mod(
    mut v_n_435_: *mut crate::leanh::LeanObject,
    mut v_x_436_: *mut crate::leanh::LeanObject,
    mut v_x_437_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_438_ = lean_nat_mod(v_x_436_, v_x_437_);
    return v___x_438_;
}
pub unsafe fn l_Fin_mod___boxed(
    mut v_n_439_: *mut crate::leanh::LeanObject,
    mut v_x_440_: *mut crate::leanh::LeanObject,
    mut v_x_441_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_442_ = l_Fin_mod(v_n_439_, v_x_440_, v_x_441_);
    crate::leanh::lean_dec(v_x_441_);
    crate::leanh::lean_dec(v_x_440_);
    crate::leanh::lean_dec(v_n_439_);
    return v_res_442_;
}
pub unsafe fn l_Fin_div___redArg(
    mut v_x_443_: *mut crate::leanh::LeanObject,
    mut v_x_444_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_445_ = lean_nat_div(v_x_443_, v_x_444_);
    return v___x_445_;
}
pub unsafe fn l_Fin_div___redArg___boxed(
    mut v_x_446_: *mut crate::leanh::LeanObject,
    mut v_x_447_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_448_ = l_Fin_div___redArg(v_x_446_, v_x_447_);
    crate::leanh::lean_dec(v_x_447_);
    crate::leanh::lean_dec(v_x_446_);
    return v_res_448_;
}
pub unsafe fn l_Fin_div(
    mut v_n_449_: *mut crate::leanh::LeanObject,
    mut v_x_450_: *mut crate::leanh::LeanObject,
    mut v_x_451_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_452_ = lean_nat_div(v_x_450_, v_x_451_);
    return v___x_452_;
}
pub unsafe fn l_Fin_div___boxed(
    mut v_n_453_: *mut crate::leanh::LeanObject,
    mut v_x_454_: *mut crate::leanh::LeanObject,
    mut v_x_455_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_456_ = l_Fin_div(v_n_453_, v_x_454_, v_x_455_);
    crate::leanh::lean_dec(v_x_455_);
    crate::leanh::lean_dec(v_x_454_);
    crate::leanh::lean_dec(v_n_453_);
    return v_res_456_;
}
pub unsafe fn l_Fin_modn___redArg(
    mut v_x_457_: *mut crate::leanh::LeanObject,
    mut v_x_458_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_459_ = lean_nat_mod(v_x_457_, v_x_458_);
    return v___x_459_;
}
pub unsafe fn l_Fin_modn___redArg___boxed(
    mut v_x_460_: *mut crate::leanh::LeanObject,
    mut v_x_461_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_462_ = l_Fin_modn___redArg(v_x_460_, v_x_461_);
    crate::leanh::lean_dec(v_x_461_);
    crate::leanh::lean_dec(v_x_460_);
    return v_res_462_;
}
pub unsafe fn l_Fin_modn(
    mut v_n_463_: *mut crate::leanh::LeanObject,
    mut v_x_464_: *mut crate::leanh::LeanObject,
    mut v_x_465_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_466_ = lean_nat_mod(v_x_464_, v_x_465_);
    return v___x_466_;
}
pub unsafe fn l_Fin_modn___boxed(
    mut v_n_467_: *mut crate::leanh::LeanObject,
    mut v_x_468_: *mut crate::leanh::LeanObject,
    mut v_x_469_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_470_ = l_Fin_modn(v_n_467_, v_x_468_, v_x_469_);
    crate::leanh::lean_dec(v_x_469_);
    crate::leanh::lean_dec(v_x_468_);
    crate::leanh::lean_dec(v_n_467_);
    return v_res_470_;
}
pub unsafe fn l_Fin_land(
    mut v_n_471_: *mut crate::leanh::LeanObject,
    mut v_x_472_: *mut crate::leanh::LeanObject,
    mut v_x_473_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_474_ = lean_nat_land(v_x_472_, v_x_473_);
    v___x_475_ = lean_nat_mod(v___x_474_, v_n_471_);
    crate::leanh::lean_dec(v___x_474_);
    return v___x_475_;
}
pub unsafe fn l_Fin_land___boxed(
    mut v_n_476_: *mut crate::leanh::LeanObject,
    mut v_x_477_: *mut crate::leanh::LeanObject,
    mut v_x_478_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_479_ = l_Fin_land(v_n_476_, v_x_477_, v_x_478_);
    crate::leanh::lean_dec(v_x_478_);
    crate::leanh::lean_dec(v_x_477_);
    crate::leanh::lean_dec(v_n_476_);
    return v_res_479_;
}
pub unsafe fn l_Fin_lor(
    mut v_n_480_: *mut crate::leanh::LeanObject,
    mut v_x_481_: *mut crate::leanh::LeanObject,
    mut v_x_482_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_483_ = lean_nat_lor(v_x_481_, v_x_482_);
    v___x_484_ = lean_nat_mod(v___x_483_, v_n_480_);
    crate::leanh::lean_dec(v___x_483_);
    return v___x_484_;
}
pub unsafe fn l_Fin_lor___boxed(
    mut v_n_485_: *mut crate::leanh::LeanObject,
    mut v_x_486_: *mut crate::leanh::LeanObject,
    mut v_x_487_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_488_ = l_Fin_lor(v_n_485_, v_x_486_, v_x_487_);
    crate::leanh::lean_dec(v_x_487_);
    crate::leanh::lean_dec(v_x_486_);
    crate::leanh::lean_dec(v_n_485_);
    return v_res_488_;
}
pub unsafe fn l_Fin_xor(
    mut v_n_489_: *mut crate::leanh::LeanObject,
    mut v_x_490_: *mut crate::leanh::LeanObject,
    mut v_x_491_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_492_ = lean_nat_lxor(v_x_490_, v_x_491_);
    v___x_493_ = lean_nat_mod(v___x_492_, v_n_489_);
    crate::leanh::lean_dec(v___x_492_);
    return v___x_493_;
}
pub unsafe fn l_Fin_xor___boxed(
    mut v_n_494_: *mut crate::leanh::LeanObject,
    mut v_x_495_: *mut crate::leanh::LeanObject,
    mut v_x_496_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_497_ = l_Fin_xor(v_n_494_, v_x_495_, v_x_496_);
    crate::leanh::lean_dec(v_x_496_);
    crate::leanh::lean_dec(v_x_495_);
    crate::leanh::lean_dec(v_n_494_);
    return v_res_497_;
}
pub unsafe fn l_Fin_shiftLeft(
    mut v_n_498_: *mut crate::leanh::LeanObject,
    mut v_x_499_: *mut crate::leanh::LeanObject,
    mut v_x_500_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_501_ = lean_nat_shiftl(v_x_499_, v_x_500_);
    v___x_502_ = lean_nat_mod(v___x_501_, v_n_498_);
    crate::leanh::lean_dec(v___x_501_);
    return v___x_502_;
}
pub unsafe fn l_Fin_shiftLeft___boxed(
    mut v_n_503_: *mut crate::leanh::LeanObject,
    mut v_x_504_: *mut crate::leanh::LeanObject,
    mut v_x_505_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_506_ = l_Fin_shiftLeft(v_n_503_, v_x_504_, v_x_505_);
    crate::leanh::lean_dec(v_x_505_);
    crate::leanh::lean_dec(v_x_504_);
    crate::leanh::lean_dec(v_n_503_);
    return v_res_506_;
}
pub unsafe fn l_Fin_shiftRight(
    mut v_n_507_: *mut crate::leanh::LeanObject,
    mut v_x_508_: *mut crate::leanh::LeanObject,
    mut v_x_509_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_510_ = lean_nat_shiftr(v_x_508_, v_x_509_);
    v___x_511_ = lean_nat_mod(v___x_510_, v_n_507_);
    crate::leanh::lean_dec(v___x_510_);
    return v___x_511_;
}
pub unsafe fn l_Fin_shiftRight___boxed(
    mut v_n_512_: *mut crate::leanh::LeanObject,
    mut v_x_513_: *mut crate::leanh::LeanObject,
    mut v_x_514_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_515_ = l_Fin_shiftRight(v_n_512_, v_x_513_, v_x_514_);
    crate::leanh::lean_dec(v_x_514_);
    crate::leanh::lean_dec(v_x_513_);
    crate::leanh::lean_dec(v_n_512_);
    return v_res_515_;
}
pub unsafe fn l_Fin_instAdd(
    mut v_n_516_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_517_ =
        crate::leanh::lean_alloc_closure(l_Fin_add___boxed as *mut core::ffi::c_void, 3, 1);
    crate::leanh::lean_closure_set(v___x_517_, 0, v_n_516_);
    return v___x_517_;
}
pub unsafe fn l_Fin_instSub(
    mut v_n_518_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_519_ =
        crate::leanh::lean_alloc_closure(l_Fin_sub___boxed as *mut core::ffi::c_void, 3, 1);
    crate::leanh::lean_closure_set(v___x_519_, 0, v_n_518_);
    return v___x_519_;
}
pub unsafe fn l_Fin_instMul(
    mut v_n_520_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_521_ =
        crate::leanh::lean_alloc_closure(l_Fin_mul___boxed as *mut core::ffi::c_void, 3, 1);
    crate::leanh::lean_closure_set(v___x_521_, 0, v_n_520_);
    return v___x_521_;
}
pub unsafe fn l_Fin_instMod(
    mut v_n_522_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_523_ =
        crate::leanh::lean_alloc_closure(l_Fin_mod___boxed as *mut core::ffi::c_void, 3, 1);
    crate::leanh::lean_closure_set(v___x_523_, 0, v_n_522_);
    return v___x_523_;
}
pub unsafe fn l_Fin_instDiv(
    mut v_n_524_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_525_ =
        crate::leanh::lean_alloc_closure(l_Fin_div___boxed as *mut core::ffi::c_void, 3, 1);
    crate::leanh::lean_closure_set(v___x_525_, 0, v_n_524_);
    return v___x_525_;
}
pub unsafe fn l_Fin_instAndOp(
    mut v_n_526_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_527_ =
        crate::leanh::lean_alloc_closure(l_Fin_land___boxed as *mut core::ffi::c_void, 3, 1);
    crate::leanh::lean_closure_set(v___x_527_, 0, v_n_526_);
    return v___x_527_;
}
pub unsafe fn l_Fin_instOrOp(
    mut v_n_528_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_529_ =
        crate::leanh::lean_alloc_closure(l_Fin_lor___boxed as *mut core::ffi::c_void, 3, 1);
    crate::leanh::lean_closure_set(v___x_529_, 0, v_n_528_);
    return v___x_529_;
}
pub unsafe fn l_Fin_instXorOp(
    mut v_n_530_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_531_ =
        crate::leanh::lean_alloc_closure(l_Fin_xor___boxed as *mut core::ffi::c_void, 3, 1);
    crate::leanh::lean_closure_set(v___x_531_, 0, v_n_530_);
    return v___x_531_;
}
pub unsafe fn l_Fin_instShiftLeft(
    mut v_n_532_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_533_ =
        crate::leanh::lean_alloc_closure(l_Fin_shiftLeft___boxed as *mut core::ffi::c_void, 3, 1);
    crate::leanh::lean_closure_set(v___x_533_, 0, v_n_532_);
    return v___x_533_;
}
pub unsafe fn l_Fin_instShiftRight(
    mut v_n_534_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_535_ =
        crate::leanh::lean_alloc_closure(l_Fin_shiftRight___boxed as *mut core::ffi::c_void, 3, 1);
    crate::leanh::lean_closure_set(v___x_535_, 0, v_n_534_);
    return v___x_535_;
}
pub unsafe fn l_Fin_instOfNat___redArg(
    mut v_n_536_: *mut crate::leanh::LeanObject,
    mut v_i_537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_538_ = lean_nat_mod(v_i_537_, v_n_536_);
    return v___x_538_;
}
pub unsafe fn l_Fin_instOfNat___redArg___boxed(
    mut v_n_539_: *mut crate::leanh::LeanObject,
    mut v_i_540_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_541_ = l_Fin_instOfNat___redArg(v_n_539_, v_i_540_);
    crate::leanh::lean_dec(v_i_540_);
    crate::leanh::lean_dec(v_n_539_);
    return v_res_541_;
}
pub unsafe fn l_Fin_instOfNat(
    mut v_n_542_: *mut crate::leanh::LeanObject,
    mut v_inst_543_: *mut crate::leanh::LeanObject,
    mut v_i_544_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_545_ = lean_nat_mod(v_i_544_, v_n_542_);
    return v___x_545_;
}
pub unsafe fn l_Fin_instOfNat___boxed(
    mut v_n_546_: *mut crate::leanh::LeanObject,
    mut v_inst_547_: *mut crate::leanh::LeanObject,
    mut v_i_548_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_549_ = l_Fin_instOfNat(v_n_546_, v_inst_547_, v_i_548_);
    crate::leanh::lean_dec(v_i_548_);
    crate::leanh::lean_dec(v_n_546_);
    return v_res_549_;
}
pub unsafe fn l_Fin_neg___lam__0(
    mut v_n_550_: *mut crate::leanh::LeanObject,
    mut v_a_551_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_552_ = lean_nat_sub(v_n_550_, v_a_551_);
    v___x_553_ = lean_nat_mod(v___x_552_, v_n_550_);
    crate::leanh::lean_dec(v___x_552_);
    return v___x_553_;
}
pub unsafe fn l_Fin_neg___lam__0___boxed(
    mut v_n_554_: *mut crate::leanh::LeanObject,
    mut v_a_555_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_556_ = l_Fin_neg___lam__0(v_n_554_, v_a_555_);
    crate::leanh::lean_dec(v_a_555_);
    crate::leanh::lean_dec(v_n_554_);
    return v_res_556_;
}
pub unsafe fn l_Fin_neg(
    mut v_n_557_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_558_ = crate::leanh::lean_alloc_closure(
        l_Fin_neg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_558_, 0, v_n_557_);
    return v___f_558_;
}
pub unsafe fn l_Fin_instInhabited___redArg(
    mut v_n_559_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_560_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_561_ = lean_nat_mod(v___x_560_, v_n_559_);
    return v___x_561_;
}
pub unsafe fn l_Fin_instInhabited___redArg___boxed(
    mut v_n_562_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_563_ = l_Fin_instInhabited___redArg(v_n_562_);
    crate::leanh::lean_dec(v_n_562_);
    return v_res_563_;
}
pub unsafe fn l_Fin_instInhabited(
    mut v_n_564_: *mut crate::leanh::LeanObject,
    mut v_inst_565_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_566_ = l_Fin_instInhabited___redArg(v_n_564_);
    return v___x_566_;
}
pub unsafe fn l_Fin_instInhabited___boxed(
    mut v_n_567_: *mut crate::leanh::LeanObject,
    mut v_inst_568_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_569_ = l_Fin_instInhabited(v_n_567_, v_inst_568_);
    crate::leanh::lean_dec(v_n_567_);
    return v_res_569_;
}
pub unsafe fn l___private_Init_Data_Fin_Basic_0__Fin_modn_match__1_splitter___redArg(
    mut v_x_570_: *mut crate::leanh::LeanObject,
    mut v_x_571_: *mut crate::leanh::LeanObject,
    mut v_h__1_572_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_573_ =
        crate::leanh::lean_apply_3(v_h__1_572_, v_x_570_, crate::leanh::lean_box(0), v_x_571_);
    return v___x_573_;
}
pub unsafe fn l___private_Init_Data_Fin_Basic_0__Fin_modn_match__1_splitter(
    mut v_n_574_: *mut crate::leanh::LeanObject,
    mut v_motive_575_: *mut crate::leanh::LeanObject,
    mut v_x_576_: *mut crate::leanh::LeanObject,
    mut v_x_577_: *mut crate::leanh::LeanObject,
    mut v_h__1_578_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_579_ =
        crate::leanh::lean_apply_3(v_h__1_578_, v_x_576_, crate::leanh::lean_box(0), v_x_577_);
    return v___x_579_;
}
pub unsafe fn l___private_Init_Data_Fin_Basic_0__Fin_modn_match__1_splitter___boxed(
    mut v_n_580_: *mut crate::leanh::LeanObject,
    mut v_motive_581_: *mut crate::leanh::LeanObject,
    mut v_x_582_: *mut crate::leanh::LeanObject,
    mut v_x_583_: *mut crate::leanh::LeanObject,
    mut v_h__1_584_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_585_ = l___private_Init_Data_Fin_Basic_0__Fin_modn_match__1_splitter(
        v_n_580_,
        v_motive_581_,
        v_x_582_,
        v_x_583_,
        v_h__1_584_,
    );
    crate::leanh::lean_dec(v_n_580_);
    return v_res_585_;
}
pub unsafe fn l_Fin_last(
    mut v_n_586_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_n_586_);
    return v_n_586_;
}
pub unsafe fn l_Fin_last___boxed(
    mut v_n_587_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_588_ = l_Fin_last(v_n_587_);
    crate::leanh::lean_dec(v_n_587_);
    return v_res_588_;
}
pub unsafe fn l_Fin_castLT___redArg(
    mut v_i_589_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_i_589_);
    return v_i_589_;
}
pub unsafe fn l_Fin_castLT___redArg___boxed(
    mut v_i_590_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_591_ = l_Fin_castLT___redArg(v_i_590_);
    crate::leanh::lean_dec(v_i_590_);
    return v_res_591_;
}
pub unsafe fn l_Fin_castLT(
    mut v_n_592_: *mut crate::leanh::LeanObject,
    mut v_m_593_: *mut crate::leanh::LeanObject,
    mut v_i_594_: *mut crate::leanh::LeanObject,
    mut v_h_595_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_i_594_);
    return v_i_594_;
}
pub unsafe fn l_Fin_castLT___boxed(
    mut v_n_596_: *mut crate::leanh::LeanObject,
    mut v_m_597_: *mut crate::leanh::LeanObject,
    mut v_i_598_: *mut crate::leanh::LeanObject,
    mut v_h_599_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_600_ = l_Fin_castLT(v_n_596_, v_m_597_, v_i_598_, v_h_599_);
    crate::leanh::lean_dec(v_i_598_);
    crate::leanh::lean_dec(v_m_597_);
    crate::leanh::lean_dec(v_n_596_);
    return v_res_600_;
}
pub unsafe fn l_Fin_castLE___redArg(
    mut v_i_601_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_i_601_);
    return v_i_601_;
}
pub unsafe fn l_Fin_castLE___redArg___boxed(
    mut v_i_602_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_603_ = l_Fin_castLE___redArg(v_i_602_);
    crate::leanh::lean_dec(v_i_602_);
    return v_res_603_;
}
pub unsafe fn l_Fin_castLE(
    mut v_n_604_: *mut crate::leanh::LeanObject,
    mut v_m_605_: *mut crate::leanh::LeanObject,
    mut v_h_606_: *mut crate::leanh::LeanObject,
    mut v_i_607_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_i_607_);
    return v_i_607_;
}
pub unsafe fn l_Fin_castLE___boxed(
    mut v_n_608_: *mut crate::leanh::LeanObject,
    mut v_m_609_: *mut crate::leanh::LeanObject,
    mut v_h_610_: *mut crate::leanh::LeanObject,
    mut v_i_611_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_612_ = l_Fin_castLE(v_n_608_, v_m_609_, v_h_610_, v_i_611_);
    crate::leanh::lean_dec(v_i_611_);
    crate::leanh::lean_dec(v_m_609_);
    crate::leanh::lean_dec(v_n_608_);
    return v_res_612_;
}
pub unsafe fn l_Fin_cast___redArg(
    mut v_i_613_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_i_613_);
    return v_i_613_;
}
pub unsafe fn l_Fin_cast___redArg___boxed(
    mut v_i_614_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_615_ = l_Fin_cast___redArg(v_i_614_);
    crate::leanh::lean_dec(v_i_614_);
    return v_res_615_;
}
pub unsafe fn l_Fin_cast(
    mut v_n_616_: *mut crate::leanh::LeanObject,
    mut v_m_617_: *mut crate::leanh::LeanObject,
    mut v_eq_618_: *mut crate::leanh::LeanObject,
    mut v_i_619_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_i_619_);
    return v_i_619_;
}
pub unsafe fn l_Fin_cast___boxed(
    mut v_n_620_: *mut crate::leanh::LeanObject,
    mut v_m_621_: *mut crate::leanh::LeanObject,
    mut v_eq_622_: *mut crate::leanh::LeanObject,
    mut v_i_623_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_624_ = l_Fin_cast(v_n_620_, v_m_621_, v_eq_622_, v_i_623_);
    crate::leanh::lean_dec(v_i_623_);
    crate::leanh::lean_dec(v_m_621_);
    crate::leanh::lean_dec(v_n_620_);
    return v_res_624_;
}
pub unsafe fn l_Fin_castAdd___redArg(
    mut v_i_625_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_i_625_);
    return v_i_625_;
}
pub unsafe fn l_Fin_castAdd___redArg___boxed(
    mut v_i_626_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_627_ = l_Fin_castAdd___redArg(v_i_626_);
    crate::leanh::lean_dec(v_i_626_);
    return v_res_627_;
}
pub unsafe fn l_Fin_castAdd(
    mut v_n_628_: *mut crate::leanh::LeanObject,
    mut v_m_629_: *mut crate::leanh::LeanObject,
    mut v_i_630_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_i_630_);
    return v_i_630_;
}
pub unsafe fn l_Fin_castAdd___boxed(
    mut v_n_631_: *mut crate::leanh::LeanObject,
    mut v_m_632_: *mut crate::leanh::LeanObject,
    mut v_i_633_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_634_ = l_Fin_castAdd(v_n_631_, v_m_632_, v_i_633_);
    crate::leanh::lean_dec(v_i_633_);
    crate::leanh::lean_dec(v_m_632_);
    crate::leanh::lean_dec(v_n_631_);
    return v_res_634_;
}
pub unsafe fn l_Fin_castSucc___redArg(
    mut v_a_635_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_a_635_);
    return v_a_635_;
}
pub unsafe fn l_Fin_castSucc___redArg___boxed(
    mut v_a_636_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_637_ = l_Fin_castSucc___redArg(v_a_636_);
    crate::leanh::lean_dec(v_a_636_);
    return v_res_637_;
}
pub unsafe fn l_Fin_castSucc(
    mut v_n_638_: *mut crate::leanh::LeanObject,
    mut v_a_639_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_a_639_);
    return v_a_639_;
}
pub unsafe fn l_Fin_castSucc___boxed(
    mut v_n_640_: *mut crate::leanh::LeanObject,
    mut v_a_641_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_642_ = l_Fin_castSucc(v_n_640_, v_a_641_);
    crate::leanh::lean_dec(v_a_641_);
    crate::leanh::lean_dec(v_n_640_);
    return v_res_642_;
}
pub unsafe fn l_Fin_addNat___redArg(
    mut v_i_643_: *mut crate::leanh::LeanObject,
    mut v_m_644_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_645_ = lean_nat_add(v_i_643_, v_m_644_);
    return v___x_645_;
}
pub unsafe fn l_Fin_addNat___redArg___boxed(
    mut v_i_646_: *mut crate::leanh::LeanObject,
    mut v_m_647_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_648_ = l_Fin_addNat___redArg(v_i_646_, v_m_647_);
    crate::leanh::lean_dec(v_m_647_);
    crate::leanh::lean_dec(v_i_646_);
    return v_res_648_;
}
pub unsafe fn l_Fin_addNat(
    mut v_n_649_: *mut crate::leanh::LeanObject,
    mut v_i_650_: *mut crate::leanh::LeanObject,
    mut v_m_651_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_652_ = lean_nat_add(v_i_650_, v_m_651_);
    return v___x_652_;
}
pub unsafe fn l_Fin_addNat___boxed(
    mut v_n_653_: *mut crate::leanh::LeanObject,
    mut v_i_654_: *mut crate::leanh::LeanObject,
    mut v_m_655_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_656_ = l_Fin_addNat(v_n_653_, v_i_654_, v_m_655_);
    crate::leanh::lean_dec(v_m_655_);
    crate::leanh::lean_dec(v_i_654_);
    crate::leanh::lean_dec(v_n_653_);
    return v_res_656_;
}
pub unsafe fn l_Fin_natAdd___redArg(
    mut v_n_657_: *mut crate::leanh::LeanObject,
    mut v_i_658_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_659_ = lean_nat_add(v_n_657_, v_i_658_);
    return v___x_659_;
}
pub unsafe fn l_Fin_natAdd___redArg___boxed(
    mut v_n_660_: *mut crate::leanh::LeanObject,
    mut v_i_661_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_662_ = l_Fin_natAdd___redArg(v_n_660_, v_i_661_);
    crate::leanh::lean_dec(v_i_661_);
    crate::leanh::lean_dec(v_n_660_);
    return v_res_662_;
}
pub unsafe fn l_Fin_natAdd(
    mut v_m_663_: *mut crate::leanh::LeanObject,
    mut v_n_664_: *mut crate::leanh::LeanObject,
    mut v_i_665_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_666_ = lean_nat_add(v_n_664_, v_i_665_);
    return v___x_666_;
}
pub unsafe fn l_Fin_natAdd___boxed(
    mut v_m_667_: *mut crate::leanh::LeanObject,
    mut v_n_668_: *mut crate::leanh::LeanObject,
    mut v_i_669_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_670_ = l_Fin_natAdd(v_m_667_, v_n_668_, v_i_669_);
    crate::leanh::lean_dec(v_i_669_);
    crate::leanh::lean_dec(v_n_668_);
    crate::leanh::lean_dec(v_m_667_);
    return v_res_670_;
}
pub unsafe fn l_Fin_rev(
    mut v_n_671_: *mut crate::leanh::LeanObject,
    mut v_i_672_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_673_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_674_ = lean_nat_add(v_i_672_, v___x_673_);
    v___x_675_ = lean_nat_sub(v_n_671_, v___x_674_);
    crate::leanh::lean_dec(v___x_674_);
    return v___x_675_;
}
pub unsafe fn l_Fin_rev___boxed(
    mut v_n_676_: *mut crate::leanh::LeanObject,
    mut v_i_677_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_678_ = l_Fin_rev(v_n_676_, v_i_677_);
    crate::leanh::lean_dec(v_i_677_);
    crate::leanh::lean_dec(v_n_676_);
    return v_res_678_;
}
pub unsafe fn l_Fin_subNat___redArg(
    mut v_m_679_: *mut crate::leanh::LeanObject,
    mut v_i_680_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_681_ = lean_nat_sub(v_i_680_, v_m_679_);
    return v___x_681_;
}
pub unsafe fn l_Fin_subNat___redArg___boxed(
    mut v_m_682_: *mut crate::leanh::LeanObject,
    mut v_i_683_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_684_ = l_Fin_subNat___redArg(v_m_682_, v_i_683_);
    crate::leanh::lean_dec(v_i_683_);
    crate::leanh::lean_dec(v_m_682_);
    return v_res_684_;
}
pub unsafe fn l_Fin_subNat(
    mut v_n_685_: *mut crate::leanh::LeanObject,
    mut v_m_686_: *mut crate::leanh::LeanObject,
    mut v_i_687_: *mut crate::leanh::LeanObject,
    mut v_h_688_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_689_ = lean_nat_sub(v_i_687_, v_m_686_);
    return v___x_689_;
}
pub unsafe fn l_Fin_subNat___boxed(
    mut v_n_690_: *mut crate::leanh::LeanObject,
    mut v_m_691_: *mut crate::leanh::LeanObject,
    mut v_i_692_: *mut crate::leanh::LeanObject,
    mut v_h_693_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_694_ = l_Fin_subNat(v_n_690_, v_m_691_, v_i_692_, v_h_693_);
    crate::leanh::lean_dec(v_i_692_);
    crate::leanh::lean_dec(v_m_691_);
    crate::leanh::lean_dec(v_n_690_);
    return v_res_694_;
}
pub unsafe fn l_Fin_pred___redArg(
    mut v_i_695_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_696_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_697_ = lean_nat_sub(v_i_695_, v___x_696_);
    return v___x_697_;
}
pub unsafe fn l_Fin_pred___redArg___boxed(
    mut v_i_698_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_699_ = l_Fin_pred___redArg(v_i_698_);
    crate::leanh::lean_dec(v_i_698_);
    return v_res_699_;
}
pub unsafe fn l_Fin_pred(
    mut v_n_700_: *mut crate::leanh::LeanObject,
    mut v_i_701_: *mut crate::leanh::LeanObject,
    mut v_h_702_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_703_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_704_ = lean_nat_sub(v_i_701_, v___x_703_);
    return v___x_704_;
}
pub unsafe fn l_Fin_pred___boxed(
    mut v_n_705_: *mut crate::leanh::LeanObject,
    mut v_i_706_: *mut crate::leanh::LeanObject,
    mut v_h_707_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_708_ = l_Fin_pred(v_n_705_, v_i_706_, v_h_707_);
    crate::leanh::lean_dec(v_i_706_);
    crate::leanh::lean_dec(v_n_705_);
    return v_res_708_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Fin_Basic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Nat_Bitwise_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Div_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Fin_Basic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Fin_Basic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Nat_Bitwise_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Div_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Fin_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Fin_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Fin_Basic(builtin);
}
