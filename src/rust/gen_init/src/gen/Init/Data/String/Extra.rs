// Lean compiler output
// Module: Init.Data.String.Extra
// Imports: Init.Data.ByteArray.Basic Init.Data.String.Basic Init.Data.String.Basic Init.Data.String.Search Init.Data.String.Termination Init.Data.String.Length
use crate::ffi::{
    lean_byte_array_fget, lean_byte_array_size, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_sub, lean_string_append, lean_string_push, lean_string_utf8_at_end,
    lean_string_utf8_byte_size, lean_string_utf8_extract, lean_string_utf8_get,
    lean_string_utf8_get_fast, lean_string_utf8_next_fast, lean_string_validate_utf8,
    lean_uint8_dec_eq, lean_uint8_land, lean_uint8_to_uint32, lean_uint32_dec_eq,
    lean_uint32_dec_le, lean_uint32_dec_lt, lean_uint32_lor, lean_uint32_shift_left,
};
use crate::r#gen::Init::Data::ByteArray::Basic::{
    initialize_Init_Data_ByteArray_Basic, runtime_initialize_Init_Data_ByteArray_Basic,
};
use crate::r#gen::Init::Data::String::Basic::{
    initialize_Init_Data_String_Basic, l_String_Slice_Pos_next_x3f,
    runtime_initialize_Init_Data_String_Basic,
};
use crate::r#gen::Init::Data::String::Length::{
    initialize_Init_Data_String_Length, runtime_initialize_Init_Data_String_Length,
};
use crate::r#gen::Init::Data::String::Search::{
    initialize_Init_Data_String_Search, runtime_initialize_Init_Data_String_Search,
};
use crate::r#gen::Init::Data::String::Termination::{
    initialize_Init_Data_String_Termination, runtime_initialize_Init_Data_String_Termination,
};
pub static l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces___closed__0_value:
    leanh::LeanStringObject<1> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 1,
    m_capacity: 1,
    m_length: 0,
    m_data: [0],
};
static mut l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces___closed__0_value
) as *mut leanh::LeanObject;
pub unsafe fn l_String_utf8DecodeChar_x3f(
    mut v_a_363_: *mut leanh::LeanObject,
    mut v_i_364_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_366_: u8 = 0;
    v___x_365_ = lean_byte_array_size(v_a_363_);
    v___x_366_ = lean_nat_dec_lt(v_i_364_, v___x_365_);
    if v___x_366_ == 0 {
        let mut v___x_367_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_367_ = leanh::lean_box(0);
        return v___x_367_;
    } else {
        let mut v___x_368_: u8 = 0;
        let mut v___x_369_: u8 = 0;
        let mut v___x_370_: u8 = 0;
        let mut v___x_371_: u8 = 0;
        let mut v___x_372_: u8 = 0;
        v___x_368_ = lean_byte_array_fget(v_a_363_, v_i_364_);
        v___x_369_ = 128;
        v___x_370_ = lean_uint8_land(v___x_368_, v___x_369_);
        v___x_371_ = 0;
        v___x_372_ = lean_uint8_dec_eq(v___x_370_, v___x_371_);
        if v___x_372_ == 0 {
            let mut v___x_373_: u8 = 0;
            let mut v___x_374_: u8 = 0;
            let mut v___x_375_: u8 = 0;
            let mut v___x_376_: u8 = 0;
            v___x_373_ = 224;
            v___x_374_ = lean_uint8_land(v___x_368_, v___x_373_);
            v___x_375_ = 192;
            v___x_376_ = lean_uint8_dec_eq(v___x_374_, v___x_375_);
            if v___x_376_ == 0 {
                let mut v___x_377_: u8 = 0;
                let mut v___x_378_: u8 = 0;
                let mut v___x_379_: u8 = 0;
                v___x_377_ = 240;
                v___x_378_ = lean_uint8_land(v___x_368_, v___x_377_);
                v___x_379_ = lean_uint8_dec_eq(v___x_378_, v___x_373_);
                if v___x_379_ == 0 {
                    let mut v___x_380_: u8 = 0;
                    let mut v___x_381_: u8 = 0;
                    let mut v___x_382_: u8 = 0;
                    v___x_380_ = 248;
                    v___x_381_ = lean_uint8_land(v___x_368_, v___x_380_);
                    v___x_382_ = lean_uint8_dec_eq(v___x_381_, v___x_377_);
                    if v___x_382_ == 0 {
                        let mut v___x_383_: *mut leanh::LeanObject = core::ptr::null_mut();
                        v___x_383_ = leanh::lean_box(0);
                        return v___x_383_;
                    } else {
                        let mut v___x_384_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_385_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_386_: u8 = 0;
                        v___x_384_ = leanh::lean_unsigned_to_nat(3);
                        v___x_385_ = lean_nat_add(v_i_364_, v___x_384_);
                        v___x_386_ = lean_nat_dec_lt(v___x_385_, v___x_365_);
                        if v___x_386_ == 0 {
                            let mut v___x_387_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            leanh::lean_dec(v___x_385_);
                            v___x_387_ = leanh::lean_box(0);
                            return v___x_387_;
                        } else {
                            let mut v___x_388_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_389_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_390_: u8 = 0;
                            let mut v___x_391_: u8 = 0;
                            let mut v___x_392_: u8 = 0;
                            v___x_388_ = leanh::lean_unsigned_to_nat(1);
                            v___x_389_ = lean_nat_add(v_i_364_, v___x_388_);
                            v___x_390_ = lean_byte_array_fget(v_a_363_, v___x_389_);
                            leanh::lean_dec(v___x_389_);
                            v___x_391_ = lean_uint8_land(v___x_390_, v___x_375_);
                            v___x_392_ = lean_uint8_dec_eq(v___x_391_, v___x_369_);
                            if v___x_392_ == 0 {
                                let mut v___x_393_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                leanh::lean_dec(v___x_385_);
                                v___x_393_ = leanh::lean_box(0);
                                return v___x_393_;
                            } else {
                                let mut v___x_394_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_395_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_396_: u8 = 0;
                                let mut v___x_397_: u8 = 0;
                                let mut v___x_398_: u8 = 0;
                                v___x_394_ = leanh::lean_unsigned_to_nat(2);
                                v___x_395_ = lean_nat_add(v_i_364_, v___x_394_);
                                v___x_396_ = lean_byte_array_fget(v_a_363_, v___x_395_);
                                leanh::lean_dec(v___x_395_);
                                v___x_397_ = lean_uint8_land(v___x_396_, v___x_375_);
                                v___x_398_ = lean_uint8_dec_eq(v___x_397_, v___x_369_);
                                if v___x_398_ == 0 {
                                    let mut v___x_399_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    leanh::lean_dec(v___x_385_);
                                    v___x_399_ = leanh::lean_box(0);
                                    return v___x_399_;
                                } else {
                                    let mut v___x_400_: u8 = 0;
                                    let mut v___x_401_: u8 = 0;
                                    let mut v___x_402_: u8 = 0;
                                    v___x_400_ = lean_byte_array_fget(v_a_363_, v___x_385_);
                                    leanh::lean_dec(v___x_385_);
                                    v___x_401_ = lean_uint8_land(v___x_400_, v___x_375_);
                                    v___x_402_ = lean_uint8_dec_eq(v___x_401_, v___x_369_);
                                    if v___x_402_ == 0 {
                                        let mut v___x_403_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        v___x_403_ = leanh::lean_box(0);
                                        return v___x_403_;
                                    } else {
                                        let mut v___x_404_: u8 = 0;
                                        let mut v_b_u2080_405_: u8 = 0;
                                        let mut v___x_406_: u8 = 0;
                                        let mut v_b_u2081_407_: u8 = 0;
                                        let mut v_b_u2082_408_: u8 = 0;
                                        let mut v_b_u2083_409_: u8 = 0;
                                        let mut v___x_410_: u32 = 0;
                                        let mut v___x_411_: u32 = 0;
                                        let mut v___x_412_: u32 = 0;
                                        let mut v___x_413_: u32 = 0;
                                        let mut v___x_414_: u32 = 0;
                                        let mut v___x_415_: u32 = 0;
                                        let mut v___x_416_: u32 = 0;
                                        let mut v___x_417_: u32 = 0;
                                        let mut v___x_418_: u32 = 0;
                                        let mut v___x_419_: u32 = 0;
                                        let mut v___x_420_: u32 = 0;
                                        let mut v___x_421_: u32 = 0;
                                        let mut v_r_422_: u32 = 0;
                                        let mut v___x_423_: u32 = 0;
                                        let mut v___x_424_: u8 = 0;
                                        v___x_404_ = 7;
                                        v_b_u2080_405_ = lean_uint8_land(v___x_368_, v___x_404_);
                                        v___x_406_ = 63;
                                        v_b_u2081_407_ = lean_uint8_land(v___x_390_, v___x_406_);
                                        v_b_u2082_408_ = lean_uint8_land(v___x_396_, v___x_406_);
                                        v_b_u2083_409_ = lean_uint8_land(v___x_400_, v___x_406_);
                                        v___x_410_ = lean_uint8_to_uint32(v_b_u2080_405_);
                                        v___x_411_ = 18;
                                        v___x_412_ = lean_uint32_shift_left(v___x_410_, v___x_411_);
                                        v___x_413_ = lean_uint8_to_uint32(v_b_u2081_407_);
                                        v___x_414_ = 12;
                                        v___x_415_ = lean_uint32_shift_left(v___x_413_, v___x_414_);
                                        v___x_416_ = lean_uint32_lor(v___x_412_, v___x_415_);
                                        v___x_417_ = lean_uint8_to_uint32(v_b_u2082_408_);
                                        v___x_418_ = 6;
                                        v___x_419_ = lean_uint32_shift_left(v___x_417_, v___x_418_);
                                        v___x_420_ = lean_uint32_lor(v___x_416_, v___x_419_);
                                        v___x_421_ = lean_uint8_to_uint32(v_b_u2083_409_);
                                        v_r_422_ = lean_uint32_lor(v___x_420_, v___x_421_);
                                        v___x_423_ = 65536;
                                        v___x_424_ = lean_uint32_dec_lt(v_r_422_, v___x_423_);
                                        if v___x_424_ == 0 {
                                            let mut v___x_425_: u32 = 0;
                                            let mut v___x_426_: u8 = 0;
                                            v___x_425_ = 1114111;
                                            v___x_426_ = lean_uint32_dec_lt(v___x_425_, v_r_422_);
                                            if v___x_426_ == 0 {
                                                let mut v___x_427_: *mut leanh::LeanObject =
                                                    core::ptr::null_mut();
                                                let mut v___x_428_: *mut leanh::LeanObject =
                                                    core::ptr::null_mut();
                                                v___x_427_ =
                                                    leanh::lean_box_uint32(v_r_422_);
                                                v___x_428_ =
                                                    leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                                leanh::lean_ctor_set(
                                                    v___x_428_, 0, v___x_427_,
                                                );
                                                return v___x_428_;
                                            } else {
                                                let mut v___x_429_: *mut leanh::LeanObject =
                                                    core::ptr::null_mut();
                                                v___x_429_ = leanh::lean_box(0);
                                                return v___x_429_;
                                            }
                                        } else {
                                            let mut v___x_430_: *mut leanh::LeanObject =
                                                core::ptr::null_mut();
                                            v___x_430_ = leanh::lean_box(0);
                                            return v___x_430_;
                                        }
                                    }
                                }
                            }
                        }
                    }
                } else {
                    let mut v___x_431_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_432_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_433_: u8 = 0;
                    v___x_431_ = leanh::lean_unsigned_to_nat(2);
                    v___x_432_ = lean_nat_add(v_i_364_, v___x_431_);
                    v___x_433_ = lean_nat_dec_lt(v___x_432_, v___x_365_);
                    if v___x_433_ == 0 {
                        let mut v___x_434_: *mut leanh::LeanObject = core::ptr::null_mut();
                        leanh::lean_dec(v___x_432_);
                        v___x_434_ = leanh::lean_box(0);
                        return v___x_434_;
                    } else {
                        let mut v___x_435_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_436_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_437_: u8 = 0;
                        let mut v___x_438_: u8 = 0;
                        let mut v___x_439_: u8 = 0;
                        v___x_435_ = leanh::lean_unsigned_to_nat(1);
                        v___x_436_ = lean_nat_add(v_i_364_, v___x_435_);
                        v___x_437_ = lean_byte_array_fget(v_a_363_, v___x_436_);
                        leanh::lean_dec(v___x_436_);
                        v___x_438_ = lean_uint8_land(v___x_437_, v___x_375_);
                        v___x_439_ = lean_uint8_dec_eq(v___x_438_, v___x_369_);
                        if v___x_439_ == 0 {
                            let mut v___x_440_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            leanh::lean_dec(v___x_432_);
                            v___x_440_ = leanh::lean_box(0);
                            return v___x_440_;
                        } else {
                            let mut v___x_441_: u8 = 0;
                            let mut v___x_442_: u8 = 0;
                            let mut v___x_443_: u8 = 0;
                            v___x_441_ = lean_byte_array_fget(v_a_363_, v___x_432_);
                            leanh::lean_dec(v___x_432_);
                            v___x_442_ = lean_uint8_land(v___x_441_, v___x_375_);
                            v___x_443_ = lean_uint8_dec_eq(v___x_442_, v___x_369_);
                            if v___x_443_ == 0 {
                                let mut v___x_444_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                v___x_444_ = leanh::lean_box(0);
                                return v___x_444_;
                            } else {
                                let mut v___x_445_: u8 = 0;
                                let mut v_b_u2080_446_: u8 = 0;
                                let mut v___x_447_: u8 = 0;
                                let mut v_b_u2081_448_: u8 = 0;
                                let mut v_b_u2082_449_: u8 = 0;
                                let mut v___x_450_: u32 = 0;
                                let mut v___x_451_: u32 = 0;
                                let mut v___x_452_: u32 = 0;
                                let mut v___x_453_: u32 = 0;
                                let mut v___x_454_: u32 = 0;
                                let mut v___x_455_: u32 = 0;
                                let mut v___x_456_: u32 = 0;
                                let mut v___x_457_: u32 = 0;
                                let mut v_r_458_: u32 = 0;
                                let mut v___x_459_: u32 = 0;
                                let mut v___x_460_: u8 = 0;
                                v___x_445_ = 15;
                                v_b_u2080_446_ = lean_uint8_land(v___x_368_, v___x_445_);
                                v___x_447_ = 63;
                                v_b_u2081_448_ = lean_uint8_land(v___x_437_, v___x_447_);
                                v_b_u2082_449_ = lean_uint8_land(v___x_441_, v___x_447_);
                                v___x_450_ = lean_uint8_to_uint32(v_b_u2080_446_);
                                v___x_451_ = 12;
                                v___x_452_ = lean_uint32_shift_left(v___x_450_, v___x_451_);
                                v___x_453_ = lean_uint8_to_uint32(v_b_u2081_448_);
                                v___x_454_ = 6;
                                v___x_455_ = lean_uint32_shift_left(v___x_453_, v___x_454_);
                                v___x_456_ = lean_uint32_lor(v___x_452_, v___x_455_);
                                v___x_457_ = lean_uint8_to_uint32(v_b_u2082_449_);
                                v_r_458_ = lean_uint32_lor(v___x_456_, v___x_457_);
                                v___x_459_ = 2048;
                                v___x_460_ = lean_uint32_dec_lt(v_r_458_, v___x_459_);
                                if v___x_460_ == 0 {
                                    let mut v___x_461_: u32 = 0;
                                    let mut v___x_462_: u8 = 0;
                                    v___x_461_ = 55296;
                                    v___x_462_ = lean_uint32_dec_le(v___x_461_, v_r_458_);
                                    if v___x_462_ == 0 {
                                        let mut v___x_463_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_464_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        v___x_463_ = leanh::lean_box_uint32(v_r_458_);
                                        v___x_464_ =
                                            leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                        leanh::lean_ctor_set(v___x_464_, 0, v___x_463_);
                                        return v___x_464_;
                                    } else {
                                        let mut v___x_465_: u32 = 0;
                                        let mut v___x_466_: u8 = 0;
                                        v___x_465_ = 57343;
                                        v___x_466_ = lean_uint32_dec_le(v_r_458_, v___x_465_);
                                        if v___x_466_ == 0 {
                                            let mut v___x_467_: *mut leanh::LeanObject =
                                                core::ptr::null_mut();
                                            let mut v___x_468_: *mut leanh::LeanObject =
                                                core::ptr::null_mut();
                                            v___x_467_ = leanh::lean_box_uint32(v_r_458_);
                                            v___x_468_ =
                                                leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                            leanh::lean_ctor_set(v___x_468_, 0, v___x_467_);
                                            return v___x_468_;
                                        } else {
                                            let mut v___x_469_: *mut leanh::LeanObject =
                                                core::ptr::null_mut();
                                            v___x_469_ = leanh::lean_box(0);
                                            return v___x_469_;
                                        }
                                    }
                                } else {
                                    let mut v___x_470_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    v___x_470_ = leanh::lean_box(0);
                                    return v___x_470_;
                                }
                            }
                        }
                    }
                }
            } else {
                let mut v___x_471_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_472_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_473_: u8 = 0;
                v___x_471_ = leanh::lean_unsigned_to_nat(1);
                v___x_472_ = lean_nat_add(v_i_364_, v___x_471_);
                v___x_473_ = lean_nat_dec_lt(v___x_472_, v___x_365_);
                if v___x_473_ == 0 {
                    let mut v___x_474_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_dec(v___x_472_);
                    v___x_474_ = leanh::lean_box(0);
                    return v___x_474_;
                } else {
                    let mut v___x_475_: u8 = 0;
                    let mut v___x_476_: u8 = 0;
                    let mut v___x_477_: u8 = 0;
                    v___x_475_ = lean_byte_array_fget(v_a_363_, v___x_472_);
                    leanh::lean_dec(v___x_472_);
                    v___x_476_ = lean_uint8_land(v___x_475_, v___x_375_);
                    v___x_477_ = lean_uint8_dec_eq(v___x_476_, v___x_369_);
                    if v___x_477_ == 0 {
                        let mut v___x_478_: *mut leanh::LeanObject = core::ptr::null_mut();
                        v___x_478_ = leanh::lean_box(0);
                        return v___x_478_;
                    } else {
                        let mut v___x_479_: u8 = 0;
                        let mut v_b_u2080_480_: u8 = 0;
                        let mut v___x_481_: u8 = 0;
                        let mut v_b_u2081_482_: u8 = 0;
                        let mut v___x_483_: u32 = 0;
                        let mut v___x_484_: u32 = 0;
                        let mut v___x_485_: u32 = 0;
                        let mut v___x_486_: u32 = 0;
                        let mut v_r_487_: u32 = 0;
                        let mut v___x_488_: u32 = 0;
                        let mut v___x_489_: u8 = 0;
                        v___x_479_ = 31;
                        v_b_u2080_480_ = lean_uint8_land(v___x_368_, v___x_479_);
                        v___x_481_ = 63;
                        v_b_u2081_482_ = lean_uint8_land(v___x_475_, v___x_481_);
                        v___x_483_ = lean_uint8_to_uint32(v_b_u2080_480_);
                        v___x_484_ = 6;
                        v___x_485_ = lean_uint32_shift_left(v___x_483_, v___x_484_);
                        v___x_486_ = lean_uint8_to_uint32(v_b_u2081_482_);
                        v_r_487_ = lean_uint32_lor(v___x_485_, v___x_486_);
                        v___x_488_ = 128;
                        v___x_489_ = lean_uint32_dec_lt(v_r_487_, v___x_488_);
                        if v___x_489_ == 0 {
                            let mut v___x_490_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_491_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            v___x_490_ = leanh::lean_box_uint32(v_r_487_);
                            v___x_491_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_491_, 0, v___x_490_);
                            return v___x_491_;
                        } else {
                            let mut v___x_492_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            v___x_492_ = leanh::lean_box(0);
                            return v___x_492_;
                        }
                    }
                }
            }
        } else {
            let mut v___x_493_: u32 = 0;
            let mut v___x_494_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_495_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_493_ = lean_uint8_to_uint32(v___x_368_);
            v___x_494_ = leanh::lean_box_uint32(v___x_493_);
            v___x_495_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_495_, 0, v___x_494_);
            return v___x_495_;
        }
    }
}
pub unsafe fn l_String_utf8DecodeChar_x3f___boxed(
    mut v_a_496_: *mut leanh::LeanObject,
    mut v_i_497_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_498_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_498_ = l_String_utf8DecodeChar_x3f(v_a_496_, v_i_497_);
    leanh::lean_dec(v_i_497_);
    leanh::lean_dec_ref(v_a_496_);
    return v_res_498_;
}
pub unsafe fn l_String_validateUTF8(mut v_a_499_: *mut leanh::LeanObject) -> u8 {
    let mut v___x_500_: u8 = 0;
    v___x_500_ = lean_string_validate_utf8(v_a_499_);
    return v___x_500_;
}
pub unsafe fn l_String_validateUTF8___boxed(
    mut v_a_501_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_502_: u8 = 0;
    let mut v_r_503_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_502_ = l_String_validateUTF8(v_a_501_);
    leanh::lean_dec_ref(v_a_501_);
    v_r_503_ = leanh::lean_box((v_res_502_) as usize);
    return v_r_503_;
}
pub unsafe fn l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_consumeSpaces(
    mut v_s_504_: *mut leanh::LeanObject,
    mut v_it_505_: *mut leanh::LeanObject,
    mut v_curr_506_: *mut leanh::LeanObject,
    mut v_min_507_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_509_: u8 = 0;
    let mut v___x_510_: u32 = 0;
    let mut v___y_512_: u8 = 0;
    let mut v___x_513_: u32 = 0;
    let mut v___x_514_: u8 = 0;
    let mut v___x_515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_516_: u8 = 0;
    let mut v___x_517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_525_: u32 = 0;
    let mut v___x_526_: u8 = 0;
    let mut v___x_527_: u32 = 0;
    let mut v___x_528_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_508_ = lean_string_utf8_byte_size(v_s_504_);
                v___x_509_ = lean_nat_dec_eq(v_it_505_, v___x_508_);
                if v___x_509_ == 0 {
                    v___x_510_ = lean_string_utf8_get_fast(v_s_504_, v_it_505_);
                    v___x_525_ = 32;
                    v___x_526_ = lean_uint32_dec_eq(v___x_510_, v___x_525_);
                    if v___x_526_ == 0 {
                        v___x_527_ = 9;
                        v___x_528_ = lean_uint32_dec_eq(v___x_510_, v___x_527_);
                        v___y_512_ = v___x_528_;
                        state = 1;
                        continue;
                    } else {
                        v___y_512_ = v___x_526_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_curr_506_);
                    leanh::lean_dec(v_it_505_);
                    leanh::lean_inc(v_min_507_);
                    return v_min_507_;
                }
            }
            1 => {
                if v___y_512_ == 0 {
                    v___x_513_ = 10;
                    v___x_514_ = lean_uint32_dec_eq(v___x_510_, v___x_513_);
                    if v___x_514_ == 0 {
                        v___x_515_ = lean_string_utf8_next_fast(v_s_504_, v_it_505_);
                        leanh::lean_dec(v_it_505_);
                        v___x_516_ = lean_nat_dec_le(v_curr_506_, v_min_507_);
                        if v___x_516_ == 0 {
                            leanh::lean_dec(v_curr_506_);
                            v___x_517_ = l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_findNextLine(v_s_504_, v___x_515_, v_min_507_);
                            return v___x_517_;
                        } else {
                            v___x_518_ = l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_findNextLine(v_s_504_, v___x_515_, v_curr_506_);
                            leanh::lean_dec(v_curr_506_);
                            return v___x_518_;
                        }
                    } else {
                        leanh::lean_dec(v_curr_506_);
                        v___x_519_ = lean_string_utf8_next_fast(v_s_504_, v_it_505_);
                        leanh::lean_dec(v_it_505_);
                        v___x_520_ = l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_findNextLine(v_s_504_, v___x_519_, v_min_507_);
                        return v___x_520_;
                    }
                } else {
                    v___x_521_ = lean_string_utf8_next_fast(v_s_504_, v_it_505_);
                    leanh::lean_dec(v_it_505_);
                    v___x_522_ = leanh::lean_unsigned_to_nat(1);
                    v___x_523_ = lean_nat_add(v_curr_506_, v___x_522_);
                    leanh::lean_dec(v_curr_506_);
                    v_it_505_ = v___x_521_;
                    v_curr_506_ = v___x_523_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_findNextLine(
    mut v_s_529_: *mut leanh::LeanObject,
    mut v_it_530_: *mut leanh::LeanObject,
    mut v_min_531_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_533_: u8 = 0;
    let mut v___x_534_: u32 = 0;
    let mut v___x_535_: u32 = 0;
    let mut v___x_536_: u8 = 0;
    let mut v___x_537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_532_ = lean_string_utf8_byte_size(v_s_529_);
                v___x_533_ = lean_nat_dec_eq(v_it_530_, v___x_532_);
                if v___x_533_ == 0 {
                    v___x_534_ = lean_string_utf8_get_fast(v_s_529_, v_it_530_);
                    v___x_535_ = 10;
                    v___x_536_ = lean_uint32_dec_eq(v___x_534_, v___x_535_);
                    if v___x_536_ == 0 {
                        v___x_537_ = lean_string_utf8_next_fast(v_s_529_, v_it_530_);
                        leanh::lean_dec(v_it_530_);
                        v_it_530_ = v___x_537_;
                        state = 0;
                        continue;
                    } else {
                        v___x_539_ = lean_string_utf8_next_fast(v_s_529_, v_it_530_);
                        leanh::lean_dec(v_it_530_);
                        v___x_540_ = leanh::lean_unsigned_to_nat(0);
                        v___x_541_ = l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_consumeSpaces(v_s_529_, v___x_539_, v___x_540_, v_min_531_);
                        return v___x_541_;
                    }
                } else {
                    leanh::lean_dec(v_it_530_);
                    leanh::lean_inc(v_min_531_);
                    return v_min_531_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_findNextLine___boxed(
    mut v_s_542_: *mut leanh::LeanObject,
    mut v_it_543_: *mut leanh::LeanObject,
    mut v_min_544_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_545_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_545_ = l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_findNextLine(
        v_s_542_, v_it_543_, v_min_544_,
    );
    leanh::lean_dec(v_min_544_);
    leanh::lean_dec_ref(v_s_542_);
    return v_res_545_;
}
pub unsafe fn l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_consumeSpaces___boxed(
    mut v_s_546_: *mut leanh::LeanObject,
    mut v_it_547_: *mut leanh::LeanObject,
    mut v_curr_548_: *mut leanh::LeanObject,
    mut v_min_549_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_550_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_550_ = l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_consumeSpaces(
        v_s_546_,
        v_it_547_,
        v_curr_548_,
        v_min_549_,
    );
    leanh::lean_dec(v_min_549_);
    leanh::lean_dec_ref(v_s_546_);
    return v_res_550_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_spec__0___redArg(
    mut v___x_551_: *mut leanh::LeanObject,
    mut v_s_552_: *mut leanh::LeanObject,
    mut v_a_553_: *mut leanh::LeanObject,
    mut v_b_554_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_startInclusive_555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_558_: u8 = 0;
    let mut v___x_559_: u32 = 0;
    let mut v___x_560_: u32 = 0;
    let mut v___x_561_: u8 = 0;
    let mut v___x_562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_startInclusive_555_ = leanh::lean_ctor_get(v___x_551_, 1);
                v_endExclusive_556_ = leanh::lean_ctor_get(v___x_551_, 2);
                v___x_557_ = lean_nat_sub(v_endExclusive_556_, v_startInclusive_555_);
                v___x_558_ = lean_nat_dec_eq(v_a_553_, v___x_557_);
                leanh::lean_dec(v___x_557_);
                if v___x_558_ == 0 {
                    v___x_559_ = lean_string_utf8_get_fast(v_s_552_, v_a_553_);
                    v___x_560_ = 10;
                    v___x_561_ = lean_uint32_dec_eq(v___x_559_, v___x_560_);
                    if v___x_561_ == 0 {
                        v___x_562_ = leanh::lean_box(0);
                        v___x_563_ = lean_string_utf8_next_fast(v_s_552_, v_a_553_);
                        leanh::lean_dec(v_a_553_);
                        v_a_553_ = v___x_563_;
                        v_b_554_ = v___x_562_;
                        state = 0;
                        continue;
                    } else {
                        v___x_565_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_565_, 0, v_a_553_);
                        return v___x_565_;
                    }
                } else {
                    leanh::lean_dec(v_a_553_);
                    leanh::lean_inc(v_b_554_);
                    return v_b_554_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_spec__0___redArg___boxed(
    mut v___x_566_: *mut leanh::LeanObject,
    mut v_s_567_: *mut leanh::LeanObject,
    mut v_a_568_: *mut leanh::LeanObject,
    mut v_b_569_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_570_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_570_ = l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_spec__0___redArg(v___x_566_, v_s_567_, v_a_568_, v_b_569_);
    leanh::lean_dec(v_b_569_);
    leanh::lean_dec_ref(v_s_567_);
    leanh::lean_dec_ref(v___x_566_);
    return v_res_570_;
}
pub unsafe fn l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize(
    mut v_s_571_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_searcher_572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_576_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_searcher_572_ = leanh::lean_unsigned_to_nat(0);
    v___x_573_ = lean_string_utf8_byte_size(v_s_571_);
    leanh::lean_inc_ref(v_s_571_);
    v___x_574_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_574_, 0, v_s_571_);
    leanh::lean_ctor_set(v___x_574_, 1, v_searcher_572_);
    leanh::lean_ctor_set(v___x_574_, 2, v___x_573_);
    v___x_575_ = leanh::lean_box(0);
    v___x_576_ = l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_spec__0___redArg(v___x_574_, v_s_571_, v_searcher_572_, v___x_575_);
    if leanh::lean_obj_tag(v___x_576_) == 0 {
        leanh::lean_dec_ref_known(v___x_574_, 3);
        leanh::lean_dec_ref(v_s_571_);
        return v_searcher_572_;
    } else {
        let mut v_val_577_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_578_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_577_ = leanh::lean_ctor_get(v___x_576_, 0);
        leanh::lean_inc(v_val_577_);
        leanh::lean_dec_ref_known(v___x_576_, 1);
        v___x_578_ = l_String_Slice_Pos_next_x3f(v___x_574_, v_val_577_);
        leanh::lean_dec(v_val_577_);
        leanh::lean_dec_ref_known(v___x_574_, 3);
        if leanh::lean_obj_tag(v___x_578_) == 0 {
            leanh::lean_dec_ref(v_s_571_);
            return v_searcher_572_;
        } else {
            let mut v_val_579_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_580_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_val_579_ = leanh::lean_ctor_get(v___x_578_, 0);
            leanh::lean_inc(v_val_579_);
            leanh::lean_dec_ref_known(v___x_578_, 1);
            v___x_580_ =
                l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_consumeSpaces(
                    v_s_571_,
                    v_val_579_,
                    v_searcher_572_,
                    v___x_573_,
                );
            leanh::lean_dec_ref(v_s_571_);
            return v___x_580_;
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_spec__0(
    mut v___x_581_: *mut leanh::LeanObject,
    mut v_s_582_: *mut leanh::LeanObject,
    mut v_inst_583_: *mut leanh::LeanObject,
    mut v_R_584_: *mut leanh::LeanObject,
    mut v_a_585_: *mut leanh::LeanObject,
    mut v_b_586_: *mut leanh::LeanObject,
    mut v_c_587_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_588_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_588_ = l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_spec__0___redArg(v___x_581_, v_s_582_, v_a_585_, v_b_586_);
    return v___x_588_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_spec__0___boxed(
    mut v___x_589_: *mut leanh::LeanObject,
    mut v_s_590_: *mut leanh::LeanObject,
    mut v_inst_591_: *mut leanh::LeanObject,
    mut v_R_592_: *mut leanh::LeanObject,
    mut v_a_593_: *mut leanh::LeanObject,
    mut v_b_594_: *mut leanh::LeanObject,
    mut v_c_595_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_596_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_596_ = l_WellFounded_opaqueFix_u2083___at___00__private_Init_Data_String_Extra_0__String_findLeadingSpacesSize_spec__0(v___x_589_, v_s_590_, v_inst_591_, v_R_592_, v_a_593_, v_b_594_, v_c_595_);
    leanh::lean_dec(v_b_594_);
    leanh::lean_dec_ref(v_s_590_);
    leanh::lean_dec_ref(v___x_589_);
    return v_res_596_;
}
pub unsafe fn l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces(
    mut v_n_597_: *mut leanh::LeanObject,
    mut v_n_598_: *mut leanh::LeanObject,
    mut v_s_599_: *mut leanh::LeanObject,
    mut v_it_600_: *mut leanh::LeanObject,
    mut v_r_601_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_603_: u8 = 0;
    let mut v___x_604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_606_: u8 = 0;
    let mut v_one_607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_610_: u8 = 0;
    let mut v___x_611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_614_: u32 = 0;
    let mut v___x_615_: u32 = 0;
    let mut v___x_616_: u8 = 0;
    let mut v___x_617_: u32 = 0;
    let mut v___x_618_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_602_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_603_ = lean_nat_dec_eq(v_n_598_, v_zero_602_);
                if v_isZero_603_ == 1 {
                    leanh::lean_dec(v_n_598_);
                    v___x_604_ = l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_saveLine(v_n_597_, v_s_599_, v_it_600_, v_r_601_);
                    return v___x_604_;
                } else {
                    v___x_605_ = lean_string_utf8_byte_size(v_s_599_);
                    v___x_606_ = lean_nat_dec_eq(v_it_600_, v___x_605_);
                    if v___x_606_ == 0 {
                        v_one_607_ = leanh::lean_unsigned_to_nat(1);
                        v_n_608_ = lean_nat_sub(v_n_598_, v_one_607_);
                        leanh::lean_dec(v_n_598_);
                        v___x_614_ = lean_string_utf8_get_fast(v_s_599_, v_it_600_);
                        v___x_615_ = 32;
                        v___x_616_ = lean_uint32_dec_eq(v___x_614_, v___x_615_);
                        if v___x_616_ == 0 {
                            v___x_617_ = 9;
                            v___x_618_ = lean_uint32_dec_eq(v___x_614_, v___x_617_);
                            v___y_610_ = v___x_618_;
                            state = 1;
                            continue;
                        } else {
                            v___y_610_ = v___x_616_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_it_600_);
                        leanh::lean_dec(v_n_598_);
                        leanh::lean_dec(v_n_597_);
                        return v_r_601_;
                    }
                }
            }
            1 => {
                if v___y_610_ == 0 {
                    leanh::lean_dec(v_n_608_);
                    v___x_611_ = l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_saveLine(v_n_597_, v_s_599_, v_it_600_, v_r_601_);
                    return v___x_611_;
                } else {
                    v___x_612_ = lean_string_utf8_next_fast(v_s_599_, v_it_600_);
                    leanh::lean_dec(v_it_600_);
                    v_n_598_ = v_n_608_;
                    v_it_600_ = v___x_612_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_saveLine(
    mut v_n_619_: *mut leanh::LeanObject,
    mut v_s_620_: *mut leanh::LeanObject,
    mut v_it_621_: *mut leanh::LeanObject,
    mut v_r_622_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_624_: u8 = 0;
    let mut v___x_625_: u32 = 0;
    let mut v___x_626_: u32 = 0;
    let mut v___x_627_: u8 = 0;
    let mut v___x_628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_623_ = lean_string_utf8_byte_size(v_s_620_);
                v___x_624_ = lean_nat_dec_eq(v_it_621_, v___x_623_);
                if v___x_624_ == 0 {
                    v___x_625_ = lean_string_utf8_get_fast(v_s_620_, v_it_621_);
                    v___x_626_ = 10;
                    v___x_627_ = lean_uint32_dec_eq(v___x_625_, v___x_626_);
                    if v___x_627_ == 0 {
                        v___x_628_ = lean_string_utf8_next_fast(v_s_620_, v_it_621_);
                        leanh::lean_dec(v_it_621_);
                        v___x_629_ = lean_string_push(v_r_622_, v___x_625_);
                        v_it_621_ = v___x_628_;
                        v_r_622_ = v___x_629_;
                        state = 0;
                        continue;
                    } else {
                        v___x_631_ = lean_string_utf8_next_fast(v_s_620_, v_it_621_);
                        leanh::lean_dec(v_it_621_);
                        v___x_632_ = lean_string_push(v_r_622_, v___x_626_);
                        leanh::lean_inc(v_n_619_);
                        v___x_633_ = l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces(v_n_619_, v_n_619_, v_s_620_, v___x_631_, v___x_632_);
                        return v___x_633_;
                    }
                } else {
                    leanh::lean_dec(v_it_621_);
                    leanh::lean_dec(v_n_619_);
                    return v_r_622_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_saveLine___boxed(
    mut v_n_634_: *mut leanh::LeanObject,
    mut v_s_635_: *mut leanh::LeanObject,
    mut v_it_636_: *mut leanh::LeanObject,
    mut v_r_637_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_638_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_638_ = l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_saveLine(
        v_n_634_, v_s_635_, v_it_636_, v_r_637_,
    );
    leanh::lean_dec_ref(v_s_635_);
    return v_res_638_;
}
pub unsafe fn l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces___boxed(
    mut v_n_639_: *mut leanh::LeanObject,
    mut v_n_640_: *mut leanh::LeanObject,
    mut v_s_641_: *mut leanh::LeanObject,
    mut v_it_642_: *mut leanh::LeanObject,
    mut v_r_643_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_644_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_644_ = l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces(
        v_n_639_, v_n_640_, v_s_641_, v_it_642_, v_r_643_,
    );
    leanh::lean_dec_ref(v_s_641_);
    return v_res_644_;
}
pub unsafe fn l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces_match__1_splitter___redArg(
    mut v_n_645_: *mut leanh::LeanObject,
    mut v_h__1_646_: *mut leanh::LeanObject,
    mut v_h__2_647_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_649_: u8 = 0;
    v_zero_648_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_649_ = lean_nat_dec_eq(v_n_645_, v_zero_648_);
    if v_isZero_649_ == 1 {
        let mut v___x_650_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_651_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_647_);
        v___x_650_ = leanh::lean_box(0);
        v___x_651_ = leanh::lean_apply_1(v_h__1_646_, v___x_650_);
        return v___x_651_;
    } else {
        let mut v_one_652_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_653_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_654_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_646_);
        v_one_652_ = leanh::lean_unsigned_to_nat(1);
        v_n_653_ = lean_nat_sub(v_n_645_, v_one_652_);
        v___x_654_ = leanh::lean_apply_1(v_h__2_647_, v_n_653_);
        return v___x_654_;
    }
}
pub unsafe fn l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces_match__1_splitter___redArg___boxed(
    mut v_n_655_: *mut leanh::LeanObject,
    mut v_h__1_656_: *mut leanh::LeanObject,
    mut v_h__2_657_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_658_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_658_ = l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces_match__1_splitter___redArg(v_n_655_, v_h__1_656_, v_h__2_657_);
    leanh::lean_dec(v_n_655_);
    return v_res_658_;
}
pub unsafe fn l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces_match__1_splitter(
    mut v_motive_659_: *mut leanh::LeanObject,
    mut v_n_660_: *mut leanh::LeanObject,
    mut v_h__1_661_: *mut leanh::LeanObject,
    mut v_h__2_662_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_664_: u8 = 0;
    v_zero_663_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_664_ = lean_nat_dec_eq(v_n_660_, v_zero_663_);
    if v_isZero_664_ == 1 {
        let mut v___x_665_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_666_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_662_);
        v___x_665_ = leanh::lean_box(0);
        v___x_666_ = leanh::lean_apply_1(v_h__1_661_, v___x_665_);
        return v___x_666_;
    } else {
        let mut v_one_667_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_668_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_669_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_661_);
        v_one_667_ = leanh::lean_unsigned_to_nat(1);
        v_n_668_ = lean_nat_sub(v_n_660_, v_one_667_);
        v___x_669_ = leanh::lean_apply_1(v_h__2_662_, v_n_668_);
        return v___x_669_;
    }
}
pub unsafe fn l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces_match__1_splitter___boxed(
    mut v_motive_670_: *mut leanh::LeanObject,
    mut v_n_671_: *mut leanh::LeanObject,
    mut v_h__1_672_: *mut leanh::LeanObject,
    mut v_h__2_673_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_674_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_674_ = l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces_match__1_splitter(v_motive_670_, v_n_671_, v_h__1_672_, v_h__2_673_);
    leanh::lean_dec(v_n_671_);
    return v_res_674_;
}
pub unsafe fn l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces(
    mut v_n_676_: *mut leanh::LeanObject,
    mut v_s_677_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_680_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_678_ = leanh::lean_unsigned_to_nat(0);
    v___x_679_ = l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces___closed__0;
    leanh::lean_inc(v_n_676_);
    v___x_680_ = l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces_consumeSpaces(
        v_n_676_, v_n_676_, v_s_677_, v___x_678_, v___x_679_,
    );
    return v___x_680_;
}
pub unsafe fn l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces___boxed(
    mut v_n_681_: *mut leanh::LeanObject,
    mut v_s_682_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_683_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_683_ =
        l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces(v_n_681_, v_s_682_);
    leanh::lean_dec_ref(v_s_682_);
    return v_res_683_;
}
pub unsafe fn l_String_removeLeadingSpaces(
    mut v_s_684_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_n_685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_687_: u8 = 0;
    leanh::lean_inc_ref(v_s_684_);
    v_n_685_ = l___private_Init_Data_String_Extra_0__String_findLeadingSpacesSize(v_s_684_);
    v___x_686_ = leanh::lean_unsigned_to_nat(0);
    v___x_687_ = lean_nat_dec_eq(v_n_685_, v___x_686_);
    if v___x_687_ == 0 {
        let mut v___x_688_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_688_ =
            l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces(v_n_685_, v_s_684_);
        leanh::lean_dec_ref(v_s_684_);
        return v___x_688_;
    } else {
        leanh::lean_dec(v_n_685_);
        return v_s_684_;
    }
}
pub unsafe fn l___private_Init_Data_String_Extra_0__String_crlfToLf_go(
    mut v_text_689_: *mut leanh::LeanObject,
    mut v_acc_690_: *mut leanh::LeanObject,
    mut v_accStop_691_: *mut leanh::LeanObject,
    mut v_pos_692_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_693_: u8 = 0;
    let mut v_c_694_: u32 = 0;
    let mut v_pos_x27_695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_697_: u32 = 0;
    let mut v___x_698_: u8 = 0;
    let mut v___x_700_: u32 = 0;
    let mut v___x_701_: u32 = 0;
    let mut v___x_702_: u8 = 0;
    let mut v___x_704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_708_: u8 = 0;
    let mut v___x_710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_711_: u8 = 0;
    let mut v___x_712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_693_ = lean_string_utf8_at_end(v_text_689_, v_pos_692_);
                if v___x_693_ == 0 {
                    v_c_694_ = lean_string_utf8_get_fast(v_text_689_, v_pos_692_);
                    v_pos_x27_695_ = lean_string_utf8_next_fast(v_text_689_, v_pos_692_);
                    v___x_708_ = lean_string_utf8_at_end(v_text_689_, v_pos_x27_695_);
                    if v___x_708_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        if v___x_693_ == 0 {
                            leanh::lean_dec(v_pos_692_);
                            v_pos_692_ = v_pos_x27_695_;
                            state = 0;
                            continue;
                        } else {
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v___x_710_ = leanh::lean_unsigned_to_nat(0);
                    v___x_711_ = lean_nat_dec_eq(v_accStop_691_, v___x_710_);
                    if v___x_711_ == 0 {
                        v___x_712_ =
                            lean_string_utf8_extract(v_text_689_, v_accStop_691_, v_pos_692_);
                        leanh::lean_dec(v_pos_692_);
                        leanh::lean_dec(v_accStop_691_);
                        v___x_713_ = lean_string_append(v_acc_690_, v___x_712_);
                        leanh::lean_dec_ref(v___x_712_);
                        return v___x_713_;
                    } else {
                        leanh::lean_dec(v_pos_692_);
                        leanh::lean_dec(v_accStop_691_);
                        leanh::lean_dec_ref(v_acc_690_);
                        leanh::lean_inc_ref(v_text_689_);
                        return v_text_689_;
                    }
                }
            }
            1 => {
                v___x_697_ = 13;
                v___x_698_ = lean_uint32_dec_eq(v_c_694_, v___x_697_);
                if v___x_698_ == 0 {
                    leanh::lean_dec(v_pos_692_);
                    v_pos_692_ = v_pos_x27_695_;
                    state = 0;
                    continue;
                } else {
                    v___x_700_ = lean_string_utf8_get(v_text_689_, v_pos_x27_695_);
                    v___x_701_ = 10;
                    v___x_702_ = lean_uint32_dec_eq(v___x_700_, v___x_701_);
                    if v___x_702_ == 0 {
                        leanh::lean_dec(v_pos_692_);
                        v_pos_692_ = v_pos_x27_695_;
                        state = 0;
                        continue;
                    } else {
                        v___x_704_ =
                            lean_string_utf8_extract(v_text_689_, v_accStop_691_, v_pos_692_);
                        leanh::lean_dec(v_pos_692_);
                        leanh::lean_dec(v_accStop_691_);
                        v_acc_705_ = lean_string_append(v_acc_690_, v___x_704_);
                        leanh::lean_dec_ref(v___x_704_);
                        v___x_706_ = lean_string_utf8_next_fast(v_text_689_, v_pos_x27_695_);
                        v_acc_690_ = v_acc_705_;
                        v_accStop_691_ = v_pos_x27_695_;
                        v_pos_692_ = v___x_706_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_String_Extra_0__String_crlfToLf_go___boxed(
    mut v_text_714_: *mut leanh::LeanObject,
    mut v_acc_715_: *mut leanh::LeanObject,
    mut v_accStop_716_: *mut leanh::LeanObject,
    mut v_pos_717_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_718_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_718_ = l___private_Init_Data_String_Extra_0__String_crlfToLf_go(
        v_text_714_,
        v_acc_715_,
        v_accStop_716_,
        v_pos_717_,
    );
    leanh::lean_dec_ref(v_text_714_);
    return v_res_718_;
}
pub unsafe fn l_String_crlfToLf(
    mut v_text_719_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_722_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_720_ = l___private_Init_Data_String_Extra_0__String_removeNumLeadingSpaces___closed__0;
    v___x_721_ = leanh::lean_unsigned_to_nat(0);
    v___x_722_ = l___private_Init_Data_String_Extra_0__String_crlfToLf_go(
        v_text_719_,
        v___x_720_,
        v___x_721_,
        v___x_721_,
    );
    return v___x_722_;
}
pub unsafe fn l_String_crlfToLf___boxed(
    mut v_text_723_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_724_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_724_ = l_String_crlfToLf(v_text_723_);
    leanh::lean_dec_ref(v_text_723_);
    return v_res_724_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_String_Extra(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_ByteArray_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Search(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Termination(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Length(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_String_Extra(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_String_Extra(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_ByteArray_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Search(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Termination(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Length(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Extra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_String_Extra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_String_Extra(builtin);
}