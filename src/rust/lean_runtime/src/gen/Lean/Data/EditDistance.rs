// Lean compiler output
// Module: Lean.Data.EditDistance
// Imports: Init.Data.String.Basic Init.Data.Vector.Basic Init.Data.Nat.Order Init.Data.Order.Lemmas Init.Data.Range Init.While Init.Data.String.Length
use crate::r#gen::Init::Data::Fin::Basic::l_Fin_add;
use crate::r#gen::Init::Data::Nat::Order::{
    initialize_Init_Data_Nat_Order, runtime_initialize_Init_Data_Nat_Order,
};
use crate::r#gen::Init::Data::Order::Lemmas::{
    initialize_Init_Data_Order_Lemmas, runtime_initialize_Init_Data_Order_Lemmas,
};
use crate::r#gen::Init::Data::Range::{
    initialize_Init_Data_Range, runtime_initialize_Init_Data_Range,
};
use crate::r#gen::Init::Data::String::Basic::{
    initialize_Init_Data_String_Basic, runtime_initialize_Init_Data_String_Basic,
};
use crate::r#gen::Init::Data::String::Length::{
    initialize_Init_Data_String_Length, runtime_initialize_Init_Data_String_Length,
};
use crate::r#gen::Init::Data::Vector::Basic::{
    initialize_Init_Data_Vector_Basic, runtime_initialize_Init_Data_Vector_Basic,
};
use crate::r#gen::Init::While::{initialize_Init_While, runtime_initialize_Init_While};
use crate::lean_imports_rs::Init::Data::Array::Basic::{lean_array_uget_borrowed, lean_mk_array};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::String::Basic::{
    lean_string_utf8_get_fast, lean_string_utf8_next_fast,
};
use crate::lean_imports_rs::Init::Data::String::Length::lean_string_length;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_of_nat};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_size, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_mod, lean_nat_sub, lean_string_utf8_byte_size,
    lean_uint32_dec_eq, lean_usize_dec_eq,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_set,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n,
    lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_tag,
    lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___redArg___closed__0_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_EditDistance_levenshtein___closed__0_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_EditDistance_levenshtein___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_EditDistance_levenshtein___closed__0_value) as *mut LeanObject;
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0___redArg(
    mut v_range_383_: *mut LeanObject,
    mut v_b_384_: *mut LeanObject,
    mut v_i_385_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_stop_386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_step_387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_388_: u8 = 0;
    let mut v_v0_389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_390_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stop_386_ = lean_ctor_get(v_range_383_, 1);
                v_step_387_ = lean_ctor_get(v_range_383_, 2);
                v___x_388_ = lean_nat_dec_lt(v_i_385_, v_stop_386_);
                if v___x_388_ == 0 {
                    lean_dec(v_i_385_);
                    return v_b_384_;
                } else {
                    lean_inc(v_i_385_);
                    v_v0_389_ = lean_array_fset(v_b_384_, v_i_385_, v_i_385_);
                    v___x_390_ = lean_nat_add(v_i_385_, v_step_387_);
                    lean_dec(v_i_385_);
                    v_b_384_ = v_v0_389_;
                    v_i_385_ = v___x_390_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0___redArg___boxed(
    mut v_range_392_: *mut LeanObject,
    mut v_b_393_: *mut LeanObject,
    mut v_i_394_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_395_: *mut LeanObject = core::ptr::null_mut();
    v_res_395_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0___redArg(v_range_392_, v_b_393_, v_i_394_);
    lean_dec_ref(v_range_392_);
    return v_res_395_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_EditDistance_levenshtein_spec__1___redArg(
    mut v_str2_396_: *mut LeanObject,
    mut v___x_397_: *mut LeanObject,
    mut v___x_398_: *mut LeanObject,
    mut v___x_399_: *mut LeanObject,
    mut v_str1_400_: *mut LeanObject,
    mut v_a_401_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_snd_402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_406_: u8 = 0;
    let mut v_fst_407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_411_: u8 = 0;
    let mut v___x_412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_413_: u8 = 0;
    let mut v___x_414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_431_: u8 = 0;
    let mut v___x_432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_438_: u8 = 0;
    let mut v___x_439_: u32 = 0;
    let mut v___x_440_: u32 = 0;
    let mut v___x_441_: u8 = 0;
    let mut v___x_442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_451_: u8 = 0;
    let mut v_isSharedCheck_452_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_402_ = lean_ctor_get(v_a_401_, 1);
                v_fst_403_ = lean_ctor_get(v_a_401_, 0);
                v_isSharedCheck_452_ = (!lean_is_exclusive(v_a_401_)) as u8;
                if v_isSharedCheck_452_ == 0 {
                    v___x_405_ = v_a_401_;
                    v_isShared_406_ = v_isSharedCheck_452_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_402_);
                    lean_inc(v_fst_403_);
                    lean_dec(v_a_401_);
                    v___x_405_ = lean_box(0);
                    v_isShared_406_ = v_isSharedCheck_452_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fst_407_ = lean_ctor_get(v_snd_402_, 0);
                v_snd_408_ = lean_ctor_get(v_snd_402_, 1);
                v_isSharedCheck_451_ = (!lean_is_exclusive(v_snd_402_)) as u8;
                if v_isSharedCheck_451_ == 0 {
                    v___x_410_ = v_snd_402_;
                    v_isShared_411_ = v_isSharedCheck_451_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_408_);
                    lean_inc(v_fst_407_);
                    lean_dec(v_snd_402_);
                    v___x_410_ = lean_box(0);
                    v_isShared_411_ = v_isSharedCheck_451_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_412_ = lean_string_utf8_byte_size(v_str2_396_);
                v___x_413_ = lean_nat_dec_eq(v_fst_407_, v___x_412_);
                if v___x_413_ == 0 {
                    v___x_414_ = lean_unsigned_to_nat(1);
                    v___x_415_ = lean_nat_mod(v___x_414_, v___x_397_);
                    v___x_416_ = l_Fin_add(v___x_397_, v_snd_408_, v___x_415_);
                    lean_dec(v___x_415_);
                    v___x_432_ = lean_array_fget_borrowed(v___x_398_, v___x_416_);
                    v___x_433_ = lean_nat_add(v___x_432_, v___x_414_);
                    v___x_434_ = lean_array_fget_borrowed(v_fst_403_, v_snd_408_);
                    v___x_435_ = lean_nat_add(v___x_434_, v___x_414_);
                    v___x_439_ = lean_string_utf8_get_fast(v_str1_400_, v___x_399_);
                    v___x_440_ = lean_string_utf8_get_fast(v_str2_396_, v_fst_407_);
                    v___x_441_ = lean_uint32_dec_eq(v___x_439_, v___x_440_);
                    if v___x_441_ == 0 {
                        v___x_442_ = lean_array_fget_borrowed(v___x_398_, v_snd_408_);
                        lean_dec(v_snd_408_);
                        v___x_443_ = lean_nat_add(v___x_442_, v___x_414_);
                        v___y_437_ = v___x_443_;
                        state = 7;
                        continue;
                    } else {
                        v___x_444_ = lean_array_fget_borrowed(v___x_398_, v_snd_408_);
                        lean_dec(v_snd_408_);
                        lean_inc(v___x_444_);
                        v___y_437_ = v___x_444_;
                        state = 7;
                        continue;
                    }
                } else {
                    if v_isShared_411_ == 0 {
                        v___x_446_ = v___x_410_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_450_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_450_, 0, v_fst_407_);
                        lean_ctor_set(v_reuseFailAlloc_450_, 1, v_snd_408_);
                        v___x_446_ = v_reuseFailAlloc_450_;
                        state = 8;
                        continue;
                    }
                }
            }
            3 => {
                v___x_419_ = lean_array_fset(v_fst_403_, v___x_416_, v___y_418_);
                v___x_420_ = lean_string_utf8_next_fast(v_str2_396_, v_fst_407_);
                lean_dec(v_fst_407_);
                if v_isShared_411_ == 0 {
                    lean_ctor_set(v___x_410_, 1, v___x_416_);
                    lean_ctor_set(v___x_410_, 0, v___x_420_);
                    v___x_422_ = v___x_410_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_427_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_427_, 0, v___x_420_);
                    lean_ctor_set(v_reuseFailAlloc_427_, 1, v___x_416_);
                    v___x_422_ = v_reuseFailAlloc_427_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_406_ == 0 {
                    lean_ctor_set(v___x_405_, 1, v___x_422_);
                    lean_ctor_set(v___x_405_, 0, v___x_419_);
                    v___x_424_ = v___x_405_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_426_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_426_, 0, v___x_419_);
                    lean_ctor_set(v_reuseFailAlloc_426_, 1, v___x_422_);
                    v___x_424_ = v_reuseFailAlloc_426_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_a_401_ = v___x_424_;
                state = 0;
                continue;
            }
            6 => {
                v___x_431_ = lean_nat_dec_le(v___y_430_, v___y_429_);
                if v___x_431_ == 0 {
                    lean_dec(v___y_430_);
                    v___y_418_ = v___y_429_;
                    state = 3;
                    continue;
                } else {
                    lean_dec(v___y_429_);
                    v___y_418_ = v___y_430_;
                    state = 3;
                    continue;
                }
            }
            7 => {
                v___x_438_ = lean_nat_dec_le(v___x_433_, v___x_435_);
                if v___x_438_ == 0 {
                    lean_dec(v___x_433_);
                    v___y_429_ = v___y_437_;
                    v___y_430_ = v___x_435_;
                    state = 6;
                    continue;
                } else {
                    lean_dec(v___x_435_);
                    v___y_429_ = v___y_437_;
                    v___y_430_ = v___x_433_;
                    state = 6;
                    continue;
                }
            }
            8 => {
                if v_isShared_406_ == 0 {
                    lean_ctor_set(v___x_405_, 1, v___x_446_);
                    v___x_448_ = v___x_405_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_449_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_449_, 0, v_fst_403_);
                    lean_ctor_set(v_reuseFailAlloc_449_, 1, v___x_446_);
                    v___x_448_ = v_reuseFailAlloc_449_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_448_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_EditDistance_levenshtein_spec__1___redArg___boxed(
    mut v_str2_453_: *mut LeanObject,
    mut v___x_454_: *mut LeanObject,
    mut v___x_455_: *mut LeanObject,
    mut v___x_456_: *mut LeanObject,
    mut v_str1_457_: *mut LeanObject,
    mut v_a_458_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_459_: *mut LeanObject = core::ptr::null_mut();
    v_res_459_ = l___private_Init_While_0__whileM_erased___at___00Lean_EditDistance_levenshtein_spec__1___redArg(v_str2_453_, v___x_454_, v___x_455_, v___x_456_, v_str1_457_, v_a_458_);
    lean_dec_ref(v_str1_457_);
    lean_dec(v___x_456_);
    lean_dec_ref(v___x_455_);
    lean_dec(v___x_454_);
    lean_dec_ref(v_str2_453_);
    return v_res_459_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_EditDistance_levenshtein_spec__2(
    mut v_cutoff_460_: *mut LeanObject,
    mut v_as_461_: *mut LeanObject,
    mut v_i_462_: usize,
    mut v_stop_463_: usize,
) -> u8 {
    let mut v___x_464_: u8 = 0;
    let mut v___x_465_: u8 = 0;
    let mut v___x_466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_467_: u8 = 0;
    let mut v___x_468_: usize = 0;
    let mut v___x_469_: usize = 0;
    let mut v___x_471_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_464_ = lean_usize_dec_eq(v_i_462_, v_stop_463_);
                if v___x_464_ == 0 {
                    v___x_465_ = 1;
                    v___x_466_ = lean_array_uget_borrowed(v_as_461_, v_i_462_);
                    v___x_467_ = lean_nat_dec_lt(v_cutoff_460_, v___x_466_);
                    if v___x_467_ == 0 {
                        return v___x_465_;
                    } else {
                        if v___x_464_ == 0 {
                            v___x_468_ = 1usize;
                            v___x_469_ = lean_usize_add(v_i_462_, v___x_468_);
                            v_i_462_ = v___x_469_;
                            state = 0;
                            continue;
                        } else {
                            return v___x_465_;
                        }
                    }
                } else {
                    v___x_471_ = 0;
                    return v___x_471_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_EditDistance_levenshtein_spec__2___boxed(
    mut v_cutoff_472_: *mut LeanObject,
    mut v_as_473_: *mut LeanObject,
    mut v_i_474_: *mut LeanObject,
    mut v_stop_475_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_476_: usize = 0;
    let mut v_stop_boxed_477_: usize = 0;
    let mut v_res_478_: u8 = 0;
    let mut v_r_479_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_476_ = lean_unbox_usize(v_i_474_);
    lean_dec(v_i_474_);
    v_stop_boxed_477_ = lean_unbox_usize(v_stop_475_);
    lean_dec(v_stop_475_);
    v_res_478_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_EditDistance_levenshtein_spec__2(v_cutoff_472_, v_as_473_, v_i_boxed_476_, v_stop_boxed_477_);
    lean_dec_ref(v_as_473_);
    lean_dec(v_cutoff_472_);
    v_r_479_ = lean_box((v_res_478_) as usize);
    return v_r_479_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___redArg(
    mut v_str1_482_: *mut LeanObject,
    mut v___x_483_: *mut LeanObject,
    mut v_str2_484_: *mut LeanObject,
    mut v_cutoff_485_: *mut LeanObject,
    mut v_a_486_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_snd_487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_490_: u8 = 0;
    let mut v_snd_491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_496_: u8 = 0;
    let mut v_fst_497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_500_: u8 = 0;
    let mut v_fst_501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_505_: u8 = 0;
    let mut v___x_506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_508_: u8 = 0;
    let mut v___x_509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_522_: u8 = 0;
    let mut v___x_523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_537_: u8 = 0;
    let mut v___x_538_: usize = 0;
    let mut v___x_539_: usize = 0;
    let mut v___x_540_: u8 = 0;
    let mut v___x_541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_546_: u8 = 0;
    let mut v_unused_547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_562_: u8 = 0;
    let mut v_isSharedCheck_563_: u8 = 0;
    let mut v_unused_564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_565_: u8 = 0;
    let mut v_unused_566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_567_: u8 = 0;
    let mut v_unused_568_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_487_ = lean_ctor_get(v_a_486_, 1);
                v_isSharedCheck_567_ = (!lean_is_exclusive(v_a_486_)) as u8;
                if v_isSharedCheck_567_ == 0 {
                    v_unused_568_ = lean_ctor_get(v_a_486_, 0);
                    lean_dec(v_unused_568_);
                    v___x_489_ = v_a_486_;
                    v_isShared_490_ = v_isSharedCheck_567_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_487_);
                    lean_dec(v_a_486_);
                    v___x_489_ = lean_box(0);
                    v_isShared_490_ = v_isSharedCheck_567_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_snd_491_ = lean_ctor_get(v_snd_487_, 1);
                lean_inc(v_snd_491_);
                v_snd_492_ = lean_ctor_get(v_snd_491_, 1);
                lean_inc(v_snd_492_);
                v_fst_493_ = lean_ctor_get(v_snd_487_, 0);
                v_isSharedCheck_565_ = (!lean_is_exclusive(v_snd_487_)) as u8;
                if v_isSharedCheck_565_ == 0 {
                    v_unused_566_ = lean_ctor_get(v_snd_487_, 1);
                    lean_dec(v_unused_566_);
                    v___x_495_ = v_snd_487_;
                    v_isShared_496_ = v_isSharedCheck_565_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_fst_493_);
                    lean_dec(v_snd_487_);
                    v___x_495_ = lean_box(0);
                    v_isShared_496_ = v_isSharedCheck_565_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_fst_497_ = lean_ctor_get(v_snd_491_, 0);
                v_isSharedCheck_563_ = (!lean_is_exclusive(v_snd_491_)) as u8;
                if v_isSharedCheck_563_ == 0 {
                    v_unused_564_ = lean_ctor_get(v_snd_491_, 1);
                    lean_dec(v_unused_564_);
                    v___x_499_ = v_snd_491_;
                    v_isShared_500_ = v_isSharedCheck_563_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_fst_497_);
                    lean_dec(v_snd_491_);
                    v___x_499_ = lean_box(0);
                    v_isShared_500_ = v_isSharedCheck_563_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_fst_501_ = lean_ctor_get(v_snd_492_, 0);
                v_snd_502_ = lean_ctor_get(v_snd_492_, 1);
                v_isSharedCheck_562_ = (!lean_is_exclusive(v_snd_492_)) as u8;
                if v_isSharedCheck_562_ == 0 {
                    v___x_504_ = v_snd_492_;
                    v_isShared_505_ = v_isSharedCheck_562_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_snd_502_);
                    lean_inc(v_fst_501_);
                    lean_dec(v_snd_492_);
                    v___x_504_ = lean_box(0);
                    v_isShared_505_ = v_isSharedCheck_562_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_506_ = lean_box(0);
                v___x_507_ = lean_string_utf8_byte_size(v_str1_482_);
                v___x_508_ = lean_nat_dec_eq(v_fst_501_, v___x_507_);
                if v___x_508_ == 0 {
                    v___x_509_ = lean_unsigned_to_nat(1);
                    v_i_510_ = lean_unsigned_to_nat(0);
                    v___x_511_ = lean_nat_add(v_snd_502_, v___x_509_);
                    lean_dec(v_snd_502_);
                    lean_inc(v___x_511_);
                    v___x_512_ = lean_array_fset(v_fst_497_, v_i_510_, v___x_511_);
                    v___x_513_ = lean_nat_mod(v_i_510_, v___x_483_);
                    if v_isShared_505_ == 0 {
                        lean_ctor_set(v___x_504_, 1, v___x_513_);
                        lean_ctor_set(v___x_504_, 0, v_i_510_);
                        v___x_515_ = v___x_504_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_549_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_549_, 0, v_i_510_);
                        lean_ctor_set(v_reuseFailAlloc_549_, 1, v___x_513_);
                        v___x_515_ = v_reuseFailAlloc_549_;
                        state = 5;
                        continue;
                    }
                } else {
                    if v_isShared_505_ == 0 {
                        v___x_551_ = v___x_504_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_561_, 0, v_fst_501_);
                        lean_ctor_set(v_reuseFailAlloc_561_, 1, v_snd_502_);
                        v___x_551_ = v_reuseFailAlloc_561_;
                        state = 12;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_500_ == 0 {
                    lean_ctor_set(v___x_499_, 1, v___x_515_);
                    lean_ctor_set(v___x_499_, 0, v___x_512_);
                    v___x_517_ = v___x_499_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_548_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_548_, 0, v___x_512_);
                    lean_ctor_set(v_reuseFailAlloc_548_, 1, v___x_515_);
                    v___x_517_ = v_reuseFailAlloc_548_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_518_ = l___private_Init_While_0__whileM_erased___at___00Lean_EditDistance_levenshtein_spec__1___redArg(v_str2_484_, v___x_483_, v_fst_493_, v_fst_501_, v_str1_482_, v___x_517_);
                v_fst_519_ = lean_ctor_get(v___x_518_, 0);
                v_isSharedCheck_546_ = (!lean_is_exclusive(v___x_518_)) as u8;
                if v_isSharedCheck_546_ == 0 {
                    v_unused_547_ = lean_ctor_get(v___x_518_, 1);
                    lean_dec(v_unused_547_);
                    v___x_521_ = v___x_518_;
                    v_isShared_522_ = v_isSharedCheck_546_;
                    state = 7;
                    continue;
                } else {
                    lean_inc(v_fst_519_);
                    lean_dec(v___x_518_);
                    v___x_521_ = lean_box(0);
                    v_isShared_522_ = v_isSharedCheck_546_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_523_ = lean_string_utf8_next_fast(v_str1_482_, v_fst_501_);
                lean_dec(v_fst_501_);
                v___x_536_ = lean_array_get_size(v_fst_519_);
                v___x_537_ = lean_nat_dec_lt(v_i_510_, v___x_536_);
                if v___x_537_ == 0 {
                    state = 8;
                    continue;
                } else {
                    if v___x_537_ == 0 {
                        state = 8;
                        continue;
                    } else {
                        v___x_538_ = 0usize;
                        v___x_539_ = lean_usize_of_nat(v___x_536_);
                        v___x_540_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_EditDistance_levenshtein_spec__2(v_cutoff_485_, v_fst_519_, v___x_538_, v___x_539_);
                        if v___x_540_ == 0 {
                            state = 8;
                            continue;
                        } else {
                            lean_del_object(v___x_521_);
                            lean_del_object(v___x_495_);
                            lean_dec(v_fst_493_);
                            lean_del_object(v___x_489_);
                            v___x_541_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_541_, 0, v___x_523_);
                            lean_ctor_set(v___x_541_, 1, v___x_511_);
                            lean_inc(v_fst_519_);
                            v___x_542_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_542_, 0, v_fst_519_);
                            lean_ctor_set(v___x_542_, 1, v___x_541_);
                            v___x_543_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_543_, 0, v_fst_519_);
                            lean_ctor_set(v___x_543_, 1, v___x_542_);
                            v___x_544_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_544_, 0, v___x_506_);
                            lean_ctor_set(v___x_544_, 1, v___x_543_);
                            v_a_486_ = v___x_544_;
                            state = 0;
                            continue;
                        }
                    }
                }
            }
            8 => {
                v___x_525_ = l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___redArg___closed__0;
                if v_isShared_522_ == 0 {
                    lean_ctor_set(v___x_521_, 1, v___x_511_);
                    lean_ctor_set(v___x_521_, 0, v___x_523_);
                    v___x_527_ = v___x_521_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_535_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_535_, 0, v___x_523_);
                    lean_ctor_set(v_reuseFailAlloc_535_, 1, v___x_511_);
                    v___x_527_ = v_reuseFailAlloc_535_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_496_ == 0 {
                    lean_ctor_set(v___x_495_, 1, v___x_527_);
                    lean_ctor_set(v___x_495_, 0, v_fst_519_);
                    v___x_529_ = v___x_495_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_534_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_534_, 0, v_fst_519_);
                    lean_ctor_set(v_reuseFailAlloc_534_, 1, v___x_527_);
                    v___x_529_ = v_reuseFailAlloc_534_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_490_ == 0 {
                    lean_ctor_set(v___x_489_, 1, v___x_529_);
                    lean_ctor_set(v___x_489_, 0, v_fst_493_);
                    v___x_531_ = v___x_489_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_533_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_533_, 0, v_fst_493_);
                    lean_ctor_set(v_reuseFailAlloc_533_, 1, v___x_529_);
                    v___x_531_ = v_reuseFailAlloc_533_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_532_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_532_, 0, v___x_525_);
                lean_ctor_set(v___x_532_, 1, v___x_531_);
                return v___x_532_;
            }
            12 => {
                if v_isShared_500_ == 0 {
                    lean_ctor_set(v___x_499_, 1, v___x_551_);
                    v___x_553_ = v___x_499_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_560_, 0, v_fst_497_);
                    lean_ctor_set(v_reuseFailAlloc_560_, 1, v___x_551_);
                    v___x_553_ = v_reuseFailAlloc_560_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_496_ == 0 {
                    lean_ctor_set(v___x_495_, 1, v___x_553_);
                    v___x_555_ = v___x_495_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_559_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_559_, 0, v_fst_493_);
                    lean_ctor_set(v_reuseFailAlloc_559_, 1, v___x_553_);
                    v___x_555_ = v_reuseFailAlloc_559_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_490_ == 0 {
                    lean_ctor_set(v___x_489_, 1, v___x_555_);
                    lean_ctor_set(v___x_489_, 0, v___x_506_);
                    v___x_557_ = v___x_489_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_558_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_558_, 0, v___x_506_);
                    lean_ctor_set(v_reuseFailAlloc_558_, 1, v___x_555_);
                    v___x_557_ = v_reuseFailAlloc_558_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_557_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___redArg___boxed(
    mut v_str1_569_: *mut LeanObject,
    mut v___x_570_: *mut LeanObject,
    mut v_str2_571_: *mut LeanObject,
    mut v_cutoff_572_: *mut LeanObject,
    mut v_a_573_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_574_: *mut LeanObject = core::ptr::null_mut();
    v_res_574_ = l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___redArg(v_str1_569_, v___x_570_, v_str2_571_, v_cutoff_572_, v_a_573_);
    lean_dec(v_cutoff_572_);
    lean_dec_ref(v_str2_571_);
    lean_dec(v___x_570_);
    lean_dec_ref(v_str1_569_);
    return v_res_574_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_EditDistance_levenshtein_spec__3___redArg(
    mut v_str2_575_: *mut LeanObject,
    mut v___x_576_: *mut LeanObject,
    mut v_str1_577_: *mut LeanObject,
    mut v_cutoff_578_: *mut LeanObject,
    mut v_a_579_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_snd_580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_583_: u8 = 0;
    let mut v_snd_584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_589_: u8 = 0;
    let mut v_fst_590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_593_: u8 = 0;
    let mut v_fst_594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_598_: u8 = 0;
    let mut v___x_599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_601_: u8 = 0;
    let mut v___x_602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_615_: u8 = 0;
    let mut v___x_616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_630_: u8 = 0;
    let mut v___x_631_: usize = 0;
    let mut v___x_632_: usize = 0;
    let mut v___x_633_: u8 = 0;
    let mut v___x_634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_639_: u8 = 0;
    let mut v_unused_640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_655_: u8 = 0;
    let mut v_isSharedCheck_656_: u8 = 0;
    let mut v_unused_657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_658_: u8 = 0;
    let mut v_unused_659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_660_: u8 = 0;
    let mut v_unused_661_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_580_ = lean_ctor_get(v_a_579_, 1);
                v_isSharedCheck_660_ = (!lean_is_exclusive(v_a_579_)) as u8;
                if v_isSharedCheck_660_ == 0 {
                    v_unused_661_ = lean_ctor_get(v_a_579_, 0);
                    lean_dec(v_unused_661_);
                    v___x_582_ = v_a_579_;
                    v_isShared_583_ = v_isSharedCheck_660_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_580_);
                    lean_dec(v_a_579_);
                    v___x_582_ = lean_box(0);
                    v_isShared_583_ = v_isSharedCheck_660_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_snd_584_ = lean_ctor_get(v_snd_580_, 1);
                lean_inc(v_snd_584_);
                v_snd_585_ = lean_ctor_get(v_snd_584_, 1);
                lean_inc(v_snd_585_);
                v_fst_586_ = lean_ctor_get(v_snd_580_, 0);
                v_isSharedCheck_658_ = (!lean_is_exclusive(v_snd_580_)) as u8;
                if v_isSharedCheck_658_ == 0 {
                    v_unused_659_ = lean_ctor_get(v_snd_580_, 1);
                    lean_dec(v_unused_659_);
                    v___x_588_ = v_snd_580_;
                    v_isShared_589_ = v_isSharedCheck_658_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_fst_586_);
                    lean_dec(v_snd_580_);
                    v___x_588_ = lean_box(0);
                    v_isShared_589_ = v_isSharedCheck_658_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_fst_590_ = lean_ctor_get(v_snd_584_, 0);
                v_isSharedCheck_656_ = (!lean_is_exclusive(v_snd_584_)) as u8;
                if v_isSharedCheck_656_ == 0 {
                    v_unused_657_ = lean_ctor_get(v_snd_584_, 1);
                    lean_dec(v_unused_657_);
                    v___x_592_ = v_snd_584_;
                    v_isShared_593_ = v_isSharedCheck_656_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_fst_590_);
                    lean_dec(v_snd_584_);
                    v___x_592_ = lean_box(0);
                    v_isShared_593_ = v_isSharedCheck_656_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_fst_594_ = lean_ctor_get(v_snd_585_, 0);
                v_snd_595_ = lean_ctor_get(v_snd_585_, 1);
                v_isSharedCheck_655_ = (!lean_is_exclusive(v_snd_585_)) as u8;
                if v_isSharedCheck_655_ == 0 {
                    v___x_597_ = v_snd_585_;
                    v_isShared_598_ = v_isSharedCheck_655_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_snd_595_);
                    lean_inc(v_fst_594_);
                    lean_dec(v_snd_585_);
                    v___x_597_ = lean_box(0);
                    v_isShared_598_ = v_isSharedCheck_655_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_599_ = lean_box(0);
                v___x_600_ = lean_string_utf8_byte_size(v_str1_577_);
                v___x_601_ = lean_nat_dec_eq(v_fst_594_, v___x_600_);
                if v___x_601_ == 0 {
                    v___x_602_ = lean_unsigned_to_nat(1);
                    v_i_603_ = lean_unsigned_to_nat(0);
                    v___x_604_ = lean_nat_add(v_snd_595_, v___x_602_);
                    lean_dec(v_snd_595_);
                    lean_inc(v___x_604_);
                    v___x_605_ = lean_array_fset(v_fst_590_, v_i_603_, v___x_604_);
                    v___x_606_ = lean_nat_mod(v_i_603_, v___x_576_);
                    if v_isShared_598_ == 0 {
                        lean_ctor_set(v___x_597_, 1, v___x_606_);
                        lean_ctor_set(v___x_597_, 0, v_i_603_);
                        v___x_608_ = v___x_597_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_642_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_642_, 0, v_i_603_);
                        lean_ctor_set(v_reuseFailAlloc_642_, 1, v___x_606_);
                        v___x_608_ = v_reuseFailAlloc_642_;
                        state = 5;
                        continue;
                    }
                } else {
                    if v_isShared_598_ == 0 {
                        v___x_644_ = v___x_597_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_654_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_654_, 0, v_fst_594_);
                        lean_ctor_set(v_reuseFailAlloc_654_, 1, v_snd_595_);
                        v___x_644_ = v_reuseFailAlloc_654_;
                        state = 12;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_593_ == 0 {
                    lean_ctor_set(v___x_592_, 1, v___x_608_);
                    lean_ctor_set(v___x_592_, 0, v___x_605_);
                    v___x_610_ = v___x_592_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_641_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_641_, 0, v___x_605_);
                    lean_ctor_set(v_reuseFailAlloc_641_, 1, v___x_608_);
                    v___x_610_ = v_reuseFailAlloc_641_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_611_ = l___private_Init_While_0__whileM_erased___at___00Lean_EditDistance_levenshtein_spec__1___redArg(v_str2_575_, v___x_576_, v_fst_586_, v_fst_594_, v_str1_577_, v___x_610_);
                v_fst_612_ = lean_ctor_get(v___x_611_, 0);
                v_isSharedCheck_639_ = (!lean_is_exclusive(v___x_611_)) as u8;
                if v_isSharedCheck_639_ == 0 {
                    v_unused_640_ = lean_ctor_get(v___x_611_, 1);
                    lean_dec(v_unused_640_);
                    v___x_614_ = v___x_611_;
                    v_isShared_615_ = v_isSharedCheck_639_;
                    state = 7;
                    continue;
                } else {
                    lean_inc(v_fst_612_);
                    lean_dec(v___x_611_);
                    v___x_614_ = lean_box(0);
                    v_isShared_615_ = v_isSharedCheck_639_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_616_ = lean_string_utf8_next_fast(v_str1_577_, v_fst_594_);
                lean_dec(v_fst_594_);
                v___x_629_ = lean_array_get_size(v_fst_612_);
                v___x_630_ = lean_nat_dec_lt(v_i_603_, v___x_629_);
                if v___x_630_ == 0 {
                    state = 8;
                    continue;
                } else {
                    if v___x_630_ == 0 {
                        state = 8;
                        continue;
                    } else {
                        v___x_631_ = 0usize;
                        v___x_632_ = lean_usize_of_nat(v___x_629_);
                        v___x_633_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_EditDistance_levenshtein_spec__2(v_cutoff_578_, v_fst_612_, v___x_631_, v___x_632_);
                        if v___x_633_ == 0 {
                            state = 8;
                            continue;
                        } else {
                            lean_del_object(v___x_614_);
                            lean_del_object(v___x_588_);
                            lean_dec(v_fst_586_);
                            lean_del_object(v___x_582_);
                            v___x_634_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_634_, 0, v___x_616_);
                            lean_ctor_set(v___x_634_, 1, v___x_604_);
                            lean_inc(v_fst_612_);
                            v___x_635_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_635_, 0, v_fst_612_);
                            lean_ctor_set(v___x_635_, 1, v___x_634_);
                            v___x_636_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_636_, 0, v_fst_612_);
                            lean_ctor_set(v___x_636_, 1, v___x_635_);
                            v___x_637_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_637_, 0, v___x_599_);
                            lean_ctor_set(v___x_637_, 1, v___x_636_);
                            v___x_638_ = l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___redArg(v_str1_577_, v___x_576_, v_str2_575_, v_cutoff_578_, v___x_637_);
                            return v___x_638_;
                        }
                    }
                }
            }
            8 => {
                v___x_618_ = l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___redArg___closed__0;
                if v_isShared_615_ == 0 {
                    lean_ctor_set(v___x_614_, 1, v___x_604_);
                    lean_ctor_set(v___x_614_, 0, v___x_616_);
                    v___x_620_ = v___x_614_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_628_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_628_, 0, v___x_616_);
                    lean_ctor_set(v_reuseFailAlloc_628_, 1, v___x_604_);
                    v___x_620_ = v_reuseFailAlloc_628_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_589_ == 0 {
                    lean_ctor_set(v___x_588_, 1, v___x_620_);
                    lean_ctor_set(v___x_588_, 0, v_fst_612_);
                    v___x_622_ = v___x_588_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_627_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_627_, 0, v_fst_612_);
                    lean_ctor_set(v_reuseFailAlloc_627_, 1, v___x_620_);
                    v___x_622_ = v_reuseFailAlloc_627_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_583_ == 0 {
                    lean_ctor_set(v___x_582_, 1, v___x_622_);
                    lean_ctor_set(v___x_582_, 0, v_fst_586_);
                    v___x_624_ = v___x_582_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_626_, 0, v_fst_586_);
                    lean_ctor_set(v_reuseFailAlloc_626_, 1, v___x_622_);
                    v___x_624_ = v_reuseFailAlloc_626_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_625_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_625_, 0, v___x_618_);
                lean_ctor_set(v___x_625_, 1, v___x_624_);
                return v___x_625_;
            }
            12 => {
                if v_isShared_593_ == 0 {
                    lean_ctor_set(v___x_592_, 1, v___x_644_);
                    v___x_646_ = v___x_592_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_653_, 0, v_fst_590_);
                    lean_ctor_set(v_reuseFailAlloc_653_, 1, v___x_644_);
                    v___x_646_ = v_reuseFailAlloc_653_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_589_ == 0 {
                    lean_ctor_set(v___x_588_, 1, v___x_646_);
                    v___x_648_ = v___x_588_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_652_, 0, v_fst_586_);
                    lean_ctor_set(v_reuseFailAlloc_652_, 1, v___x_646_);
                    v___x_648_ = v_reuseFailAlloc_652_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_583_ == 0 {
                    lean_ctor_set(v___x_582_, 1, v___x_648_);
                    lean_ctor_set(v___x_582_, 0, v___x_599_);
                    v___x_650_ = v___x_582_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_651_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_651_, 0, v___x_599_);
                    lean_ctor_set(v_reuseFailAlloc_651_, 1, v___x_648_);
                    v___x_650_ = v_reuseFailAlloc_651_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_650_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_EditDistance_levenshtein_spec__3___redArg___boxed(
    mut v_str2_662_: *mut LeanObject,
    mut v___x_663_: *mut LeanObject,
    mut v_str1_664_: *mut LeanObject,
    mut v_cutoff_665_: *mut LeanObject,
    mut v_a_666_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_667_: *mut LeanObject = core::ptr::null_mut();
    v_res_667_ = l___private_Init_While_0__whileM_erased___at___00Lean_EditDistance_levenshtein_spec__3___redArg(v_str2_662_, v___x_663_, v_str1_664_, v_cutoff_665_, v_a_666_);
    lean_dec(v_cutoff_665_);
    lean_dec_ref(v_str1_664_);
    lean_dec(v___x_663_);
    lean_dec_ref(v_str2_662_);
    return v_res_667_;
}
pub unsafe fn l_Lean_EditDistance_levenshtein(
    mut v_str1_670_: *mut LeanObject,
    mut v_str2_671_: *mut LeanObject,
    mut v_cutoff_672_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_len1_673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_len2_674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_679_: u8 = 0;
    let mut v___x_680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v1_683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_701_: u8 = 0;
    let mut v___x_702_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_len1_673_ = lean_string_length(v_str1_670_);
                v_len2_674_ = lean_string_length(v_str2_671_);
                v___x_702_ = lean_nat_dec_le(v_len1_673_, v_len2_674_);
                if v___x_702_ == 0 {
                    v___y_700_ = v_len1_673_;
                    state = 2;
                    continue;
                } else {
                    v___y_700_ = v_len2_674_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_678_ = lean_nat_sub(v___y_676_, v___y_677_);
                lean_dec(v___y_677_);
                lean_dec(v___y_676_);
                v___x_679_ = lean_nat_dec_lt(v_cutoff_672_, v___x_678_);
                lean_dec(v___x_678_);
                if v___x_679_ == 0 {
                    v___x_680_ = lean_unsigned_to_nat(1);
                    v___x_681_ = lean_nat_add(v_len2_674_, v___x_680_);
                    v_i_682_ = lean_unsigned_to_nat(0);
                    lean_inc_n(v___x_681_, 2);
                    v_v1_683_ = lean_mk_array(v___x_681_, v_i_682_);
                    v___x_684_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_684_, 0, v_i_682_);
                    lean_ctor_set(v___x_684_, 1, v___x_681_);
                    lean_ctor_set(v___x_684_, 2, v___x_680_);
                    lean_inc_ref(v_v1_683_);
                    v___x_685_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0___redArg(v___x_684_, v_v1_683_, v_i_682_);
                    lean_dec_ref_known(v___x_684_, 3);
                    v___x_686_ = lean_box(0);
                    v___x_687_ = l_Lean_EditDistance_levenshtein___closed__0;
                    v___x_688_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_688_, 0, v_v1_683_);
                    lean_ctor_set(v___x_688_, 1, v___x_687_);
                    v___x_689_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_689_, 0, v___x_685_);
                    lean_ctor_set(v___x_689_, 1, v___x_688_);
                    v___x_690_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_690_, 0, v___x_686_);
                    lean_ctor_set(v___x_690_, 1, v___x_689_);
                    v___x_691_ = l___private_Init_While_0__whileM_erased___at___00Lean_EditDistance_levenshtein_spec__3___redArg(v_str2_671_, v___x_681_, v_str1_670_, v_cutoff_672_, v___x_690_);
                    lean_dec(v___x_681_);
                    v_fst_692_ = lean_ctor_get(v___x_691_, 0);
                    lean_inc(v_fst_692_);
                    if lean_obj_tag(v_fst_692_) == 0 {
                        v_snd_693_ = lean_ctor_get(v___x_691_, 1);
                        lean_inc(v_snd_693_);
                        lean_dec_ref(v___x_691_);
                        v_fst_694_ = lean_ctor_get(v_snd_693_, 0);
                        lean_inc(v_fst_694_);
                        lean_dec(v_snd_693_);
                        v___x_695_ = lean_array_fget(v_fst_694_, v_len2_674_);
                        lean_dec(v_fst_694_);
                        v___x_696_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_696_, 0, v___x_695_);
                        return v___x_696_;
                    } else {
                        lean_dec_ref(v___x_691_);
                        v_val_697_ = lean_ctor_get(v_fst_692_, 0);
                        lean_inc(v_val_697_);
                        lean_dec_ref_known(v_fst_692_, 1);
                        return v_val_697_;
                    }
                } else {
                    v___x_698_ = lean_box(0);
                    return v___x_698_;
                }
            }
            2 => {
                v___x_701_ = lean_nat_dec_le(v_len1_673_, v_len2_674_);
                if v___x_701_ == 0 {
                    v___y_676_ = v___y_700_;
                    v___y_677_ = v_len2_674_;
                    state = 1;
                    continue;
                } else {
                    v___y_676_ = v___y_700_;
                    v___y_677_ = v_len1_673_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_EditDistance_levenshtein___boxed(
    mut v_str1_703_: *mut LeanObject,
    mut v_str2_704_: *mut LeanObject,
    mut v_cutoff_705_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_706_: *mut LeanObject = core::ptr::null_mut();
    v_res_706_ = l_Lean_EditDistance_levenshtein(v_str1_703_, v_str2_704_, v_cutoff_705_);
    lean_dec(v_cutoff_705_);
    lean_dec_ref(v_str2_704_);
    lean_dec_ref(v_str1_703_);
    return v_res_706_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0(
    mut v___x_707_: *mut LeanObject,
    mut v_range_708_: *mut LeanObject,
    mut v_b_709_: *mut LeanObject,
    mut v_i_710_: *mut LeanObject,
    mut v_hs_711_: *mut LeanObject,
    mut v_hl_712_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_713_: *mut LeanObject = core::ptr::null_mut();
    v___x_713_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0___redArg(v_range_708_, v_b_709_, v_i_710_);
    return v___x_713_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0___boxed(
    mut v___x_714_: *mut LeanObject,
    mut v_range_715_: *mut LeanObject,
    mut v_b_716_: *mut LeanObject,
    mut v_i_717_: *mut LeanObject,
    mut v_hs_718_: *mut LeanObject,
    mut v_hl_719_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_720_: *mut LeanObject = core::ptr::null_mut();
    v_res_720_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0(v___x_714_, v_range_715_, v_b_716_, v_i_717_, v_hs_718_, v_hl_719_);
    lean_dec_ref(v_range_715_);
    lean_dec(v___x_714_);
    return v_res_720_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_EditDistance_levenshtein_spec__1(
    mut v_str2_721_: *mut LeanObject,
    mut v___x_722_: *mut LeanObject,
    mut v___x_723_: *mut LeanObject,
    mut v___x_724_: *mut LeanObject,
    mut v_str1_725_: *mut LeanObject,
    mut v_inst_726_: *mut LeanObject,
    mut v_a_727_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_728_: *mut LeanObject = core::ptr::null_mut();
    v___x_728_ = l___private_Init_While_0__whileM_erased___at___00Lean_EditDistance_levenshtein_spec__1___redArg(v_str2_721_, v___x_722_, v___x_723_, v___x_724_, v_str1_725_, v_a_727_);
    return v___x_728_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_EditDistance_levenshtein_spec__1___boxed(
    mut v_str2_729_: *mut LeanObject,
    mut v___x_730_: *mut LeanObject,
    mut v___x_731_: *mut LeanObject,
    mut v___x_732_: *mut LeanObject,
    mut v_str1_733_: *mut LeanObject,
    mut v_inst_734_: *mut LeanObject,
    mut v_a_735_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_736_: *mut LeanObject = core::ptr::null_mut();
    v_res_736_ =
        l___private_Init_While_0__whileM_erased___at___00Lean_EditDistance_levenshtein_spec__1(
            v_str2_729_,
            v___x_730_,
            v___x_731_,
            v___x_732_,
            v_str1_733_,
            v_inst_734_,
            v_a_735_,
        );
    lean_dec_ref(v_str1_733_);
    lean_dec(v___x_732_);
    lean_dec_ref(v___x_731_);
    lean_dec(v___x_730_);
    lean_dec_ref(v_str2_729_);
    return v_res_736_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_EditDistance_levenshtein_spec__3(
    mut v_str2_737_: *mut LeanObject,
    mut v___x_738_: *mut LeanObject,
    mut v_str1_739_: *mut LeanObject,
    mut v_cutoff_740_: *mut LeanObject,
    mut v_inst_741_: *mut LeanObject,
    mut v_a_742_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_743_: *mut LeanObject = core::ptr::null_mut();
    v___x_743_ = l___private_Init_While_0__whileM_erased___at___00Lean_EditDistance_levenshtein_spec__3___redArg(v_str2_737_, v___x_738_, v_str1_739_, v_cutoff_740_, v_a_742_);
    return v___x_743_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_EditDistance_levenshtein_spec__3___boxed(
    mut v_str2_744_: *mut LeanObject,
    mut v___x_745_: *mut LeanObject,
    mut v_str1_746_: *mut LeanObject,
    mut v_cutoff_747_: *mut LeanObject,
    mut v_inst_748_: *mut LeanObject,
    mut v_a_749_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_750_: *mut LeanObject = core::ptr::null_mut();
    v_res_750_ =
        l___private_Init_While_0__whileM_erased___at___00Lean_EditDistance_levenshtein_spec__3(
            v_str2_744_,
            v___x_745_,
            v_str1_746_,
            v_cutoff_747_,
            v_inst_748_,
            v_a_749_,
        );
    lean_dec(v_cutoff_747_);
    lean_dec_ref(v_str1_746_);
    lean_dec(v___x_745_);
    lean_dec_ref(v_str2_744_);
    return v_res_750_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3(
    mut v_str1_751_: *mut LeanObject,
    mut v___x_752_: *mut LeanObject,
    mut v_str2_753_: *mut LeanObject,
    mut v_cutoff_754_: *mut LeanObject,
    mut v_inst_755_: *mut LeanObject,
    mut v_a_756_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_757_: *mut LeanObject = core::ptr::null_mut();
    v___x_757_ = l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___redArg(v_str1_751_, v___x_752_, v_str2_753_, v_cutoff_754_, v_a_756_);
    return v___x_757_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___boxed(
    mut v_str1_758_: *mut LeanObject,
    mut v___x_759_: *mut LeanObject,
    mut v_str2_760_: *mut LeanObject,
    mut v_cutoff_761_: *mut LeanObject,
    mut v_inst_762_: *mut LeanObject,
    mut v_a_763_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_764_: *mut LeanObject = core::ptr::null_mut();
    v_res_764_ = l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3(v_str1_758_, v___x_759_, v_str2_760_, v_cutoff_761_, v_inst_762_, v_a_763_);
    lean_dec(v_cutoff_761_);
    lean_dec_ref(v_str2_760_);
    lean_dec(v___x_759_);
    lean_dec_ref(v_str1_758_);
    return v_res_764_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Data_EditDistance(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_String_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Vector_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Order(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Order_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_While(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Length(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data_EditDistance(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Data_EditDistance(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_String_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Vector_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Order(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Order_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Range(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_While(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Length(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_EditDistance(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Data_EditDistance(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Data_EditDistance(builtin);
}
