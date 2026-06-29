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
use crate::ffi::{lean_array_uget_borrowed, lean_mk_array};
use crate::ffi::lean_array_fset;
use crate::ffi::{
    lean_string_utf8_get_fast, lean_string_utf8_next_fast,
};
use crate::ffi::lean_string_length;
use crate::ffi::{lean_usize_add, lean_usize_of_nat};
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_size, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_mod, lean_nat_sub, lean_string_utf8_byte_size,
    lean_uint32_dec_eq, lean_usize_dec_eq,
};
pub static l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___redArg___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_EditDistance_levenshtein___closed__0_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_EditDistance_levenshtein___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_EditDistance_levenshtein___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0___redArg(
    mut v_range_383_: *mut crate::leanh::LeanObject,
    mut v_b_384_: *mut crate::leanh::LeanObject,
    mut v_i_385_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_stop_386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_step_387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_388_: u8 = 0;
    let mut v_v0_389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stop_386_ = crate::leanh::lean_ctor_get(v_range_383_, 1);
                v_step_387_ = crate::leanh::lean_ctor_get(v_range_383_, 2);
                v___x_388_ = lean_nat_dec_lt(v_i_385_, v_stop_386_);
                if v___x_388_ == 0 {
                    crate::leanh::lean_dec(v_i_385_);
                    return v_b_384_;
                } else {
                    crate::leanh::lean_inc(v_i_385_);
                    v_v0_389_ = lean_array_fset(v_b_384_, v_i_385_, v_i_385_);
                    v___x_390_ = lean_nat_add(v_i_385_, v_step_387_);
                    crate::leanh::lean_dec(v_i_385_);
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
    mut v_range_392_: *mut crate::leanh::LeanObject,
    mut v_b_393_: *mut crate::leanh::LeanObject,
    mut v_i_394_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_395_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0___redArg(v_range_392_, v_b_393_, v_i_394_);
    crate::leanh::lean_dec_ref(v_range_392_);
    return v_res_395_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_EditDistance_levenshtein_spec__1___redArg(
    mut v_str2_396_: *mut crate::leanh::LeanObject,
    mut v___x_397_: *mut crate::leanh::LeanObject,
    mut v___x_398_: *mut crate::leanh::LeanObject,
    mut v___x_399_: *mut crate::leanh::LeanObject,
    mut v_str1_400_: *mut crate::leanh::LeanObject,
    mut v_a_401_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_snd_402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_406_: u8 = 0;
    let mut v_fst_407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_411_: u8 = 0;
    let mut v___x_412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_413_: u8 = 0;
    let mut v___x_414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_431_: u8 = 0;
    let mut v___x_432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_438_: u8 = 0;
    let mut v___x_439_: u32 = 0;
    let mut v___x_440_: u32 = 0;
    let mut v___x_441_: u8 = 0;
    let mut v___x_442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_451_: u8 = 0;
    let mut v_isSharedCheck_452_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_402_ = crate::leanh::lean_ctor_get(v_a_401_, 1);
                v_fst_403_ = crate::leanh::lean_ctor_get(v_a_401_, 0);
                v_isSharedCheck_452_ = (!crate::leanh::lean_is_exclusive(v_a_401_)) as u8;
                if v_isSharedCheck_452_ == 0 {
                    v___x_405_ = v_a_401_;
                    v_isShared_406_ = v_isSharedCheck_452_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_402_);
                    crate::leanh::lean_inc(v_fst_403_);
                    crate::leanh::lean_dec(v_a_401_);
                    v___x_405_ = crate::leanh::lean_box(0);
                    v_isShared_406_ = v_isSharedCheck_452_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fst_407_ = crate::leanh::lean_ctor_get(v_snd_402_, 0);
                v_snd_408_ = crate::leanh::lean_ctor_get(v_snd_402_, 1);
                v_isSharedCheck_451_ = (!crate::leanh::lean_is_exclusive(v_snd_402_)) as u8;
                if v_isSharedCheck_451_ == 0 {
                    v___x_410_ = v_snd_402_;
                    v_isShared_411_ = v_isSharedCheck_451_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_408_);
                    crate::leanh::lean_inc(v_fst_407_);
                    crate::leanh::lean_dec(v_snd_402_);
                    v___x_410_ = crate::leanh::lean_box(0);
                    v_isShared_411_ = v_isSharedCheck_451_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_412_ = lean_string_utf8_byte_size(v_str2_396_);
                v___x_413_ = lean_nat_dec_eq(v_fst_407_, v___x_412_);
                if v___x_413_ == 0 {
                    v___x_414_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_415_ = lean_nat_mod(v___x_414_, v___x_397_);
                    v___x_416_ = l_Fin_add(v___x_397_, v_snd_408_, v___x_415_);
                    crate::leanh::lean_dec(v___x_415_);
                    v___x_432_ = lean_array_fget_borrowed(v___x_398_, v___x_416_);
                    v___x_433_ = lean_nat_add(v___x_432_, v___x_414_);
                    v___x_434_ = lean_array_fget_borrowed(v_fst_403_, v_snd_408_);
                    v___x_435_ = lean_nat_add(v___x_434_, v___x_414_);
                    v___x_439_ = lean_string_utf8_get_fast(v_str1_400_, v___x_399_);
                    v___x_440_ = lean_string_utf8_get_fast(v_str2_396_, v_fst_407_);
                    v___x_441_ = lean_uint32_dec_eq(v___x_439_, v___x_440_);
                    if v___x_441_ == 0 {
                        v___x_442_ = lean_array_fget_borrowed(v___x_398_, v_snd_408_);
                        crate::leanh::lean_dec(v_snd_408_);
                        v___x_443_ = lean_nat_add(v___x_442_, v___x_414_);
                        v___y_437_ = v___x_443_;
                        state = 7;
                        continue;
                    } else {
                        v___x_444_ = lean_array_fget_borrowed(v___x_398_, v_snd_408_);
                        crate::leanh::lean_dec(v_snd_408_);
                        crate::leanh::lean_inc(v___x_444_);
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
                        v_reuseFailAlloc_450_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_450_, 0, v_fst_407_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_450_, 1, v_snd_408_);
                        v___x_446_ = v_reuseFailAlloc_450_;
                        state = 8;
                        continue;
                    }
                }
            }
            3 => {
                v___x_419_ = lean_array_fset(v_fst_403_, v___x_416_, v___y_418_);
                v___x_420_ = lean_string_utf8_next_fast(v_str2_396_, v_fst_407_);
                crate::leanh::lean_dec(v_fst_407_);
                if v_isShared_411_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_410_, 1, v___x_416_);
                    crate::leanh::lean_ctor_set(v___x_410_, 0, v___x_420_);
                    v___x_422_ = v___x_410_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_427_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_427_, 0, v___x_420_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_427_, 1, v___x_416_);
                    v___x_422_ = v_reuseFailAlloc_427_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_406_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_405_, 1, v___x_422_);
                    crate::leanh::lean_ctor_set(v___x_405_, 0, v___x_419_);
                    v___x_424_ = v___x_405_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_426_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_426_, 0, v___x_419_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_426_, 1, v___x_422_);
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
                    crate::leanh::lean_dec(v___y_430_);
                    v___y_418_ = v___y_429_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_429_);
                    v___y_418_ = v___y_430_;
                    state = 3;
                    continue;
                }
            }
            7 => {
                v___x_438_ = lean_nat_dec_le(v___x_433_, v___x_435_);
                if v___x_438_ == 0 {
                    crate::leanh::lean_dec(v___x_433_);
                    v___y_429_ = v___y_437_;
                    v___y_430_ = v___x_435_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_435_);
                    v___y_429_ = v___y_437_;
                    v___y_430_ = v___x_433_;
                    state = 6;
                    continue;
                }
            }
            8 => {
                if v_isShared_406_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_405_, 1, v___x_446_);
                    v___x_448_ = v___x_405_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_449_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_449_, 0, v_fst_403_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_449_, 1, v___x_446_);
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
    mut v_str2_453_: *mut crate::leanh::LeanObject,
    mut v___x_454_: *mut crate::leanh::LeanObject,
    mut v___x_455_: *mut crate::leanh::LeanObject,
    mut v___x_456_: *mut crate::leanh::LeanObject,
    mut v_str1_457_: *mut crate::leanh::LeanObject,
    mut v_a_458_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_459_ = l___private_Init_While_0__whileM_erased___at___00Lean_EditDistance_levenshtein_spec__1___redArg(v_str2_453_, v___x_454_, v___x_455_, v___x_456_, v_str1_457_, v_a_458_);
    crate::leanh::lean_dec_ref(v_str1_457_);
    crate::leanh::lean_dec(v___x_456_);
    crate::leanh::lean_dec_ref(v___x_455_);
    crate::leanh::lean_dec(v___x_454_);
    crate::leanh::lean_dec_ref(v_str2_453_);
    return v_res_459_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_EditDistance_levenshtein_spec__2(
    mut v_cutoff_460_: *mut crate::leanh::LeanObject,
    mut v_as_461_: *mut crate::leanh::LeanObject,
    mut v_i_462_: usize,
    mut v_stop_463_: usize,
) -> u8 {
    let mut v___x_464_: u8 = 0;
    let mut v___x_465_: u8 = 0;
    let mut v___x_466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_cutoff_472_: *mut crate::leanh::LeanObject,
    mut v_as_473_: *mut crate::leanh::LeanObject,
    mut v_i_474_: *mut crate::leanh::LeanObject,
    mut v_stop_475_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_476_: usize = 0;
    let mut v_stop_boxed_477_: usize = 0;
    let mut v_res_478_: u8 = 0;
    let mut v_r_479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_476_ = crate::leanh::lean_unbox_usize(v_i_474_);
    crate::leanh::lean_dec(v_i_474_);
    v_stop_boxed_477_ = crate::leanh::lean_unbox_usize(v_stop_475_);
    crate::leanh::lean_dec(v_stop_475_);
    v_res_478_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_EditDistance_levenshtein_spec__2(v_cutoff_472_, v_as_473_, v_i_boxed_476_, v_stop_boxed_477_);
    crate::leanh::lean_dec_ref(v_as_473_);
    crate::leanh::lean_dec(v_cutoff_472_);
    v_r_479_ = crate::leanh::lean_box((v_res_478_) as usize);
    return v_r_479_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___redArg(
    mut v_str1_482_: *mut crate::leanh::LeanObject,
    mut v___x_483_: *mut crate::leanh::LeanObject,
    mut v_str2_484_: *mut crate::leanh::LeanObject,
    mut v_cutoff_485_: *mut crate::leanh::LeanObject,
    mut v_a_486_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_snd_487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_490_: u8 = 0;
    let mut v_snd_491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_496_: u8 = 0;
    let mut v_fst_497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_500_: u8 = 0;
    let mut v_fst_501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_505_: u8 = 0;
    let mut v___x_506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_508_: u8 = 0;
    let mut v___x_509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_522_: u8 = 0;
    let mut v___x_523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_537_: u8 = 0;
    let mut v___x_538_: usize = 0;
    let mut v___x_539_: usize = 0;
    let mut v___x_540_: u8 = 0;
    let mut v___x_541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_546_: u8 = 0;
    let mut v_unused_547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_562_: u8 = 0;
    let mut v_isSharedCheck_563_: u8 = 0;
    let mut v_unused_564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_565_: u8 = 0;
    let mut v_unused_566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_567_: u8 = 0;
    let mut v_unused_568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_487_ = crate::leanh::lean_ctor_get(v_a_486_, 1);
                v_isSharedCheck_567_ = (!crate::leanh::lean_is_exclusive(v_a_486_)) as u8;
                if v_isSharedCheck_567_ == 0 {
                    v_unused_568_ = crate::leanh::lean_ctor_get(v_a_486_, 0);
                    crate::leanh::lean_dec(v_unused_568_);
                    v___x_489_ = v_a_486_;
                    v_isShared_490_ = v_isSharedCheck_567_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_487_);
                    crate::leanh::lean_dec(v_a_486_);
                    v___x_489_ = crate::leanh::lean_box(0);
                    v_isShared_490_ = v_isSharedCheck_567_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_snd_491_ = crate::leanh::lean_ctor_get(v_snd_487_, 1);
                crate::leanh::lean_inc(v_snd_491_);
                v_snd_492_ = crate::leanh::lean_ctor_get(v_snd_491_, 1);
                crate::leanh::lean_inc(v_snd_492_);
                v_fst_493_ = crate::leanh::lean_ctor_get(v_snd_487_, 0);
                v_isSharedCheck_565_ = (!crate::leanh::lean_is_exclusive(v_snd_487_)) as u8;
                if v_isSharedCheck_565_ == 0 {
                    v_unused_566_ = crate::leanh::lean_ctor_get(v_snd_487_, 1);
                    crate::leanh::lean_dec(v_unused_566_);
                    v___x_495_ = v_snd_487_;
                    v_isShared_496_ = v_isSharedCheck_565_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_493_);
                    crate::leanh::lean_dec(v_snd_487_);
                    v___x_495_ = crate::leanh::lean_box(0);
                    v_isShared_496_ = v_isSharedCheck_565_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_fst_497_ = crate::leanh::lean_ctor_get(v_snd_491_, 0);
                v_isSharedCheck_563_ = (!crate::leanh::lean_is_exclusive(v_snd_491_)) as u8;
                if v_isSharedCheck_563_ == 0 {
                    v_unused_564_ = crate::leanh::lean_ctor_get(v_snd_491_, 1);
                    crate::leanh::lean_dec(v_unused_564_);
                    v___x_499_ = v_snd_491_;
                    v_isShared_500_ = v_isSharedCheck_563_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_497_);
                    crate::leanh::lean_dec(v_snd_491_);
                    v___x_499_ = crate::leanh::lean_box(0);
                    v_isShared_500_ = v_isSharedCheck_563_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_fst_501_ = crate::leanh::lean_ctor_get(v_snd_492_, 0);
                v_snd_502_ = crate::leanh::lean_ctor_get(v_snd_492_, 1);
                v_isSharedCheck_562_ = (!crate::leanh::lean_is_exclusive(v_snd_492_)) as u8;
                if v_isSharedCheck_562_ == 0 {
                    v___x_504_ = v_snd_492_;
                    v_isShared_505_ = v_isSharedCheck_562_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_502_);
                    crate::leanh::lean_inc(v_fst_501_);
                    crate::leanh::lean_dec(v_snd_492_);
                    v___x_504_ = crate::leanh::lean_box(0);
                    v_isShared_505_ = v_isSharedCheck_562_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_506_ = crate::leanh::lean_box(0);
                v___x_507_ = lean_string_utf8_byte_size(v_str1_482_);
                v___x_508_ = lean_nat_dec_eq(v_fst_501_, v___x_507_);
                if v___x_508_ == 0 {
                    v___x_509_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_i_510_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_511_ = lean_nat_add(v_snd_502_, v___x_509_);
                    crate::leanh::lean_dec(v_snd_502_);
                    crate::leanh::lean_inc(v___x_511_);
                    v___x_512_ = lean_array_fset(v_fst_497_, v_i_510_, v___x_511_);
                    v___x_513_ = lean_nat_mod(v_i_510_, v___x_483_);
                    if v_isShared_505_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_504_, 1, v___x_513_);
                        crate::leanh::lean_ctor_set(v___x_504_, 0, v_i_510_);
                        v___x_515_ = v___x_504_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_549_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_549_, 0, v_i_510_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_549_, 1, v___x_513_);
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
                        v_reuseFailAlloc_561_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_561_, 0, v_fst_501_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_561_, 1, v_snd_502_);
                        v___x_551_ = v_reuseFailAlloc_561_;
                        state = 12;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_500_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_499_, 1, v___x_515_);
                    crate::leanh::lean_ctor_set(v___x_499_, 0, v___x_512_);
                    v___x_517_ = v___x_499_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_548_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_548_, 0, v___x_512_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_548_, 1, v___x_515_);
                    v___x_517_ = v_reuseFailAlloc_548_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_518_ = l___private_Init_While_0__whileM_erased___at___00Lean_EditDistance_levenshtein_spec__1___redArg(v_str2_484_, v___x_483_, v_fst_493_, v_fst_501_, v_str1_482_, v___x_517_);
                v_fst_519_ = crate::leanh::lean_ctor_get(v___x_518_, 0);
                v_isSharedCheck_546_ = (!crate::leanh::lean_is_exclusive(v___x_518_)) as u8;
                if v_isSharedCheck_546_ == 0 {
                    v_unused_547_ = crate::leanh::lean_ctor_get(v___x_518_, 1);
                    crate::leanh::lean_dec(v_unused_547_);
                    v___x_521_ = v___x_518_;
                    v_isShared_522_ = v_isSharedCheck_546_;
                    state = 7;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_519_);
                    crate::leanh::lean_dec(v___x_518_);
                    v___x_521_ = crate::leanh::lean_box(0);
                    v_isShared_522_ = v_isSharedCheck_546_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_523_ = lean_string_utf8_next_fast(v_str1_482_, v_fst_501_);
                crate::leanh::lean_dec(v_fst_501_);
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
                            crate::leanh::lean_del_object(v___x_521_);
                            crate::leanh::lean_del_object(v___x_495_);
                            crate::leanh::lean_dec(v_fst_493_);
                            crate::leanh::lean_del_object(v___x_489_);
                            v___x_541_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_541_, 0, v___x_523_);
                            crate::leanh::lean_ctor_set(v___x_541_, 1, v___x_511_);
                            crate::leanh::lean_inc(v_fst_519_);
                            v___x_542_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_542_, 0, v_fst_519_);
                            crate::leanh::lean_ctor_set(v___x_542_, 1, v___x_541_);
                            v___x_543_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_543_, 0, v_fst_519_);
                            crate::leanh::lean_ctor_set(v___x_543_, 1, v___x_542_);
                            v___x_544_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_544_, 0, v___x_506_);
                            crate::leanh::lean_ctor_set(v___x_544_, 1, v___x_543_);
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
                    crate::leanh::lean_ctor_set(v___x_521_, 1, v___x_511_);
                    crate::leanh::lean_ctor_set(v___x_521_, 0, v___x_523_);
                    v___x_527_ = v___x_521_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_535_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_535_, 0, v___x_523_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_535_, 1, v___x_511_);
                    v___x_527_ = v_reuseFailAlloc_535_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_496_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_495_, 1, v___x_527_);
                    crate::leanh::lean_ctor_set(v___x_495_, 0, v_fst_519_);
                    v___x_529_ = v___x_495_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_534_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_534_, 0, v_fst_519_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_534_, 1, v___x_527_);
                    v___x_529_ = v_reuseFailAlloc_534_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_490_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_489_, 1, v___x_529_);
                    crate::leanh::lean_ctor_set(v___x_489_, 0, v_fst_493_);
                    v___x_531_ = v___x_489_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_533_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_533_, 0, v_fst_493_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_533_, 1, v___x_529_);
                    v___x_531_ = v_reuseFailAlloc_533_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_532_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_532_, 0, v___x_525_);
                crate::leanh::lean_ctor_set(v___x_532_, 1, v___x_531_);
                return v___x_532_;
            }
            12 => {
                if v_isShared_500_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_499_, 1, v___x_551_);
                    v___x_553_ = v___x_499_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_560_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_560_, 0, v_fst_497_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_560_, 1, v___x_551_);
                    v___x_553_ = v_reuseFailAlloc_560_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_496_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_495_, 1, v___x_553_);
                    v___x_555_ = v___x_495_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_559_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_559_, 0, v_fst_493_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_559_, 1, v___x_553_);
                    v___x_555_ = v_reuseFailAlloc_559_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_490_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_489_, 1, v___x_555_);
                    crate::leanh::lean_ctor_set(v___x_489_, 0, v___x_506_);
                    v___x_557_ = v___x_489_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_558_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_558_, 0, v___x_506_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_558_, 1, v___x_555_);
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
    mut v_str1_569_: *mut crate::leanh::LeanObject,
    mut v___x_570_: *mut crate::leanh::LeanObject,
    mut v_str2_571_: *mut crate::leanh::LeanObject,
    mut v_cutoff_572_: *mut crate::leanh::LeanObject,
    mut v_a_573_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_574_ = l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___redArg(v_str1_569_, v___x_570_, v_str2_571_, v_cutoff_572_, v_a_573_);
    crate::leanh::lean_dec(v_cutoff_572_);
    crate::leanh::lean_dec_ref(v_str2_571_);
    crate::leanh::lean_dec(v___x_570_);
    crate::leanh::lean_dec_ref(v_str1_569_);
    return v_res_574_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_EditDistance_levenshtein_spec__3___redArg(
    mut v_str2_575_: *mut crate::leanh::LeanObject,
    mut v___x_576_: *mut crate::leanh::LeanObject,
    mut v_str1_577_: *mut crate::leanh::LeanObject,
    mut v_cutoff_578_: *mut crate::leanh::LeanObject,
    mut v_a_579_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_snd_580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_583_: u8 = 0;
    let mut v_snd_584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_589_: u8 = 0;
    let mut v_fst_590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_593_: u8 = 0;
    let mut v_fst_594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_598_: u8 = 0;
    let mut v___x_599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_601_: u8 = 0;
    let mut v___x_602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_615_: u8 = 0;
    let mut v___x_616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_630_: u8 = 0;
    let mut v___x_631_: usize = 0;
    let mut v___x_632_: usize = 0;
    let mut v___x_633_: u8 = 0;
    let mut v___x_634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_639_: u8 = 0;
    let mut v_unused_640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_655_: u8 = 0;
    let mut v_isSharedCheck_656_: u8 = 0;
    let mut v_unused_657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_658_: u8 = 0;
    let mut v_unused_659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_660_: u8 = 0;
    let mut v_unused_661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_580_ = crate::leanh::lean_ctor_get(v_a_579_, 1);
                v_isSharedCheck_660_ = (!crate::leanh::lean_is_exclusive(v_a_579_)) as u8;
                if v_isSharedCheck_660_ == 0 {
                    v_unused_661_ = crate::leanh::lean_ctor_get(v_a_579_, 0);
                    crate::leanh::lean_dec(v_unused_661_);
                    v___x_582_ = v_a_579_;
                    v_isShared_583_ = v_isSharedCheck_660_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_580_);
                    crate::leanh::lean_dec(v_a_579_);
                    v___x_582_ = crate::leanh::lean_box(0);
                    v_isShared_583_ = v_isSharedCheck_660_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_snd_584_ = crate::leanh::lean_ctor_get(v_snd_580_, 1);
                crate::leanh::lean_inc(v_snd_584_);
                v_snd_585_ = crate::leanh::lean_ctor_get(v_snd_584_, 1);
                crate::leanh::lean_inc(v_snd_585_);
                v_fst_586_ = crate::leanh::lean_ctor_get(v_snd_580_, 0);
                v_isSharedCheck_658_ = (!crate::leanh::lean_is_exclusive(v_snd_580_)) as u8;
                if v_isSharedCheck_658_ == 0 {
                    v_unused_659_ = crate::leanh::lean_ctor_get(v_snd_580_, 1);
                    crate::leanh::lean_dec(v_unused_659_);
                    v___x_588_ = v_snd_580_;
                    v_isShared_589_ = v_isSharedCheck_658_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_586_);
                    crate::leanh::lean_dec(v_snd_580_);
                    v___x_588_ = crate::leanh::lean_box(0);
                    v_isShared_589_ = v_isSharedCheck_658_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_fst_590_ = crate::leanh::lean_ctor_get(v_snd_584_, 0);
                v_isSharedCheck_656_ = (!crate::leanh::lean_is_exclusive(v_snd_584_)) as u8;
                if v_isSharedCheck_656_ == 0 {
                    v_unused_657_ = crate::leanh::lean_ctor_get(v_snd_584_, 1);
                    crate::leanh::lean_dec(v_unused_657_);
                    v___x_592_ = v_snd_584_;
                    v_isShared_593_ = v_isSharedCheck_656_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_590_);
                    crate::leanh::lean_dec(v_snd_584_);
                    v___x_592_ = crate::leanh::lean_box(0);
                    v_isShared_593_ = v_isSharedCheck_656_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_fst_594_ = crate::leanh::lean_ctor_get(v_snd_585_, 0);
                v_snd_595_ = crate::leanh::lean_ctor_get(v_snd_585_, 1);
                v_isSharedCheck_655_ = (!crate::leanh::lean_is_exclusive(v_snd_585_)) as u8;
                if v_isSharedCheck_655_ == 0 {
                    v___x_597_ = v_snd_585_;
                    v_isShared_598_ = v_isSharedCheck_655_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_595_);
                    crate::leanh::lean_inc(v_fst_594_);
                    crate::leanh::lean_dec(v_snd_585_);
                    v___x_597_ = crate::leanh::lean_box(0);
                    v_isShared_598_ = v_isSharedCheck_655_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_599_ = crate::leanh::lean_box(0);
                v___x_600_ = lean_string_utf8_byte_size(v_str1_577_);
                v___x_601_ = lean_nat_dec_eq(v_fst_594_, v___x_600_);
                if v___x_601_ == 0 {
                    v___x_602_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_i_603_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_604_ = lean_nat_add(v_snd_595_, v___x_602_);
                    crate::leanh::lean_dec(v_snd_595_);
                    crate::leanh::lean_inc(v___x_604_);
                    v___x_605_ = lean_array_fset(v_fst_590_, v_i_603_, v___x_604_);
                    v___x_606_ = lean_nat_mod(v_i_603_, v___x_576_);
                    if v_isShared_598_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_597_, 1, v___x_606_);
                        crate::leanh::lean_ctor_set(v___x_597_, 0, v_i_603_);
                        v___x_608_ = v___x_597_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_642_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_642_, 0, v_i_603_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_642_, 1, v___x_606_);
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
                        v_reuseFailAlloc_654_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_654_, 0, v_fst_594_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_654_, 1, v_snd_595_);
                        v___x_644_ = v_reuseFailAlloc_654_;
                        state = 12;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_593_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_592_, 1, v___x_608_);
                    crate::leanh::lean_ctor_set(v___x_592_, 0, v___x_605_);
                    v___x_610_ = v___x_592_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_641_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_641_, 0, v___x_605_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_641_, 1, v___x_608_);
                    v___x_610_ = v_reuseFailAlloc_641_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_611_ = l___private_Init_While_0__whileM_erased___at___00Lean_EditDistance_levenshtein_spec__1___redArg(v_str2_575_, v___x_576_, v_fst_586_, v_fst_594_, v_str1_577_, v___x_610_);
                v_fst_612_ = crate::leanh::lean_ctor_get(v___x_611_, 0);
                v_isSharedCheck_639_ = (!crate::leanh::lean_is_exclusive(v___x_611_)) as u8;
                if v_isSharedCheck_639_ == 0 {
                    v_unused_640_ = crate::leanh::lean_ctor_get(v___x_611_, 1);
                    crate::leanh::lean_dec(v_unused_640_);
                    v___x_614_ = v___x_611_;
                    v_isShared_615_ = v_isSharedCheck_639_;
                    state = 7;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_612_);
                    crate::leanh::lean_dec(v___x_611_);
                    v___x_614_ = crate::leanh::lean_box(0);
                    v_isShared_615_ = v_isSharedCheck_639_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_616_ = lean_string_utf8_next_fast(v_str1_577_, v_fst_594_);
                crate::leanh::lean_dec(v_fst_594_);
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
                            crate::leanh::lean_del_object(v___x_614_);
                            crate::leanh::lean_del_object(v___x_588_);
                            crate::leanh::lean_dec(v_fst_586_);
                            crate::leanh::lean_del_object(v___x_582_);
                            v___x_634_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_634_, 0, v___x_616_);
                            crate::leanh::lean_ctor_set(v___x_634_, 1, v___x_604_);
                            crate::leanh::lean_inc(v_fst_612_);
                            v___x_635_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_635_, 0, v_fst_612_);
                            crate::leanh::lean_ctor_set(v___x_635_, 1, v___x_634_);
                            v___x_636_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_636_, 0, v_fst_612_);
                            crate::leanh::lean_ctor_set(v___x_636_, 1, v___x_635_);
                            v___x_637_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_637_, 0, v___x_599_);
                            crate::leanh::lean_ctor_set(v___x_637_, 1, v___x_636_);
                            v___x_638_ = l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___redArg(v_str1_577_, v___x_576_, v_str2_575_, v_cutoff_578_, v___x_637_);
                            return v___x_638_;
                        }
                    }
                }
            }
            8 => {
                v___x_618_ = l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___redArg___closed__0;
                if v_isShared_615_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_614_, 1, v___x_604_);
                    crate::leanh::lean_ctor_set(v___x_614_, 0, v___x_616_);
                    v___x_620_ = v___x_614_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_628_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_628_, 0, v___x_616_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_628_, 1, v___x_604_);
                    v___x_620_ = v_reuseFailAlloc_628_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_589_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_588_, 1, v___x_620_);
                    crate::leanh::lean_ctor_set(v___x_588_, 0, v_fst_612_);
                    v___x_622_ = v___x_588_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_627_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_627_, 0, v_fst_612_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_627_, 1, v___x_620_);
                    v___x_622_ = v_reuseFailAlloc_627_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_583_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_582_, 1, v___x_622_);
                    crate::leanh::lean_ctor_set(v___x_582_, 0, v_fst_586_);
                    v___x_624_ = v___x_582_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_626_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_626_, 0, v_fst_586_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_626_, 1, v___x_622_);
                    v___x_624_ = v_reuseFailAlloc_626_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_625_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_625_, 0, v___x_618_);
                crate::leanh::lean_ctor_set(v___x_625_, 1, v___x_624_);
                return v___x_625_;
            }
            12 => {
                if v_isShared_593_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_592_, 1, v___x_644_);
                    v___x_646_ = v___x_592_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_653_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_653_, 0, v_fst_590_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_653_, 1, v___x_644_);
                    v___x_646_ = v_reuseFailAlloc_653_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_589_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_588_, 1, v___x_646_);
                    v___x_648_ = v___x_588_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_652_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_652_, 0, v_fst_586_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_652_, 1, v___x_646_);
                    v___x_648_ = v_reuseFailAlloc_652_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_583_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_582_, 1, v___x_648_);
                    crate::leanh::lean_ctor_set(v___x_582_, 0, v___x_599_);
                    v___x_650_ = v___x_582_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_651_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_651_, 0, v___x_599_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_651_, 1, v___x_648_);
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
    mut v_str2_662_: *mut crate::leanh::LeanObject,
    mut v___x_663_: *mut crate::leanh::LeanObject,
    mut v_str1_664_: *mut crate::leanh::LeanObject,
    mut v_cutoff_665_: *mut crate::leanh::LeanObject,
    mut v_a_666_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_667_ = l___private_Init_While_0__whileM_erased___at___00Lean_EditDistance_levenshtein_spec__3___redArg(v_str2_662_, v___x_663_, v_str1_664_, v_cutoff_665_, v_a_666_);
    crate::leanh::lean_dec(v_cutoff_665_);
    crate::leanh::lean_dec_ref(v_str1_664_);
    crate::leanh::lean_dec(v___x_663_);
    crate::leanh::lean_dec_ref(v_str2_662_);
    return v_res_667_;
}
pub unsafe fn l_Lean_EditDistance_levenshtein(
    mut v_str1_670_: *mut crate::leanh::LeanObject,
    mut v_str2_671_: *mut crate::leanh::LeanObject,
    mut v_cutoff_672_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_len1_673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_len2_674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_679_: u8 = 0;
    let mut v___x_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v1_683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
                crate::leanh::lean_dec(v___y_677_);
                crate::leanh::lean_dec(v___y_676_);
                v___x_679_ = lean_nat_dec_lt(v_cutoff_672_, v___x_678_);
                crate::leanh::lean_dec(v___x_678_);
                if v___x_679_ == 0 {
                    v___x_680_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_681_ = lean_nat_add(v_len2_674_, v___x_680_);
                    v_i_682_ = crate::leanh::lean_unsigned_to_nat(0);
                    crate::leanh::lean_inc_n(v___x_681_, 2);
                    v_v1_683_ = lean_mk_array(v___x_681_, v_i_682_);
                    v___x_684_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_684_, 0, v_i_682_);
                    crate::leanh::lean_ctor_set(v___x_684_, 1, v___x_681_);
                    crate::leanh::lean_ctor_set(v___x_684_, 2, v___x_680_);
                    crate::leanh::lean_inc_ref(v_v1_683_);
                    v___x_685_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0___redArg(v___x_684_, v_v1_683_, v_i_682_);
                    crate::leanh::lean_dec_ref_known(v___x_684_, 3);
                    v___x_686_ = crate::leanh::lean_box(0);
                    v___x_687_ = l_Lean_EditDistance_levenshtein___closed__0;
                    v___x_688_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_688_, 0, v_v1_683_);
                    crate::leanh::lean_ctor_set(v___x_688_, 1, v___x_687_);
                    v___x_689_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_689_, 0, v___x_685_);
                    crate::leanh::lean_ctor_set(v___x_689_, 1, v___x_688_);
                    v___x_690_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_690_, 0, v___x_686_);
                    crate::leanh::lean_ctor_set(v___x_690_, 1, v___x_689_);
                    v___x_691_ = l___private_Init_While_0__whileM_erased___at___00Lean_EditDistance_levenshtein_spec__3___redArg(v_str2_671_, v___x_681_, v_str1_670_, v_cutoff_672_, v___x_690_);
                    crate::leanh::lean_dec(v___x_681_);
                    v_fst_692_ = crate::leanh::lean_ctor_get(v___x_691_, 0);
                    crate::leanh::lean_inc(v_fst_692_);
                    if crate::leanh::lean_obj_tag(v_fst_692_) == 0 {
                        v_snd_693_ = crate::leanh::lean_ctor_get(v___x_691_, 1);
                        crate::leanh::lean_inc(v_snd_693_);
                        crate::leanh::lean_dec_ref(v___x_691_);
                        v_fst_694_ = crate::leanh::lean_ctor_get(v_snd_693_, 0);
                        crate::leanh::lean_inc(v_fst_694_);
                        crate::leanh::lean_dec(v_snd_693_);
                        v___x_695_ = lean_array_fget(v_fst_694_, v_len2_674_);
                        crate::leanh::lean_dec(v_fst_694_);
                        v___x_696_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_696_, 0, v___x_695_);
                        return v___x_696_;
                    } else {
                        crate::leanh::lean_dec_ref(v___x_691_);
                        v_val_697_ = crate::leanh::lean_ctor_get(v_fst_692_, 0);
                        crate::leanh::lean_inc(v_val_697_);
                        crate::leanh::lean_dec_ref_known(v_fst_692_, 1);
                        return v_val_697_;
                    }
                } else {
                    v___x_698_ = crate::leanh::lean_box(0);
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
    mut v_str1_703_: *mut crate::leanh::LeanObject,
    mut v_str2_704_: *mut crate::leanh::LeanObject,
    mut v_cutoff_705_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_706_ = l_Lean_EditDistance_levenshtein(v_str1_703_, v_str2_704_, v_cutoff_705_);
    crate::leanh::lean_dec(v_cutoff_705_);
    crate::leanh::lean_dec_ref(v_str2_704_);
    crate::leanh::lean_dec_ref(v_str1_703_);
    return v_res_706_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0(
    mut v___x_707_: *mut crate::leanh::LeanObject,
    mut v_range_708_: *mut crate::leanh::LeanObject,
    mut v_b_709_: *mut crate::leanh::LeanObject,
    mut v_i_710_: *mut crate::leanh::LeanObject,
    mut v_hs_711_: *mut crate::leanh::LeanObject,
    mut v_hl_712_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_713_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0___redArg(v_range_708_, v_b_709_, v_i_710_);
    return v___x_713_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0___boxed(
    mut v___x_714_: *mut crate::leanh::LeanObject,
    mut v_range_715_: *mut crate::leanh::LeanObject,
    mut v_b_716_: *mut crate::leanh::LeanObject,
    mut v_i_717_: *mut crate::leanh::LeanObject,
    mut v_hs_718_: *mut crate::leanh::LeanObject,
    mut v_hl_719_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_720_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0(v___x_714_, v_range_715_, v_b_716_, v_i_717_, v_hs_718_, v_hl_719_);
    crate::leanh::lean_dec_ref(v_range_715_);
    crate::leanh::lean_dec(v___x_714_);
    return v_res_720_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_EditDistance_levenshtein_spec__1(
    mut v_str2_721_: *mut crate::leanh::LeanObject,
    mut v___x_722_: *mut crate::leanh::LeanObject,
    mut v___x_723_: *mut crate::leanh::LeanObject,
    mut v___x_724_: *mut crate::leanh::LeanObject,
    mut v_str1_725_: *mut crate::leanh::LeanObject,
    mut v_inst_726_: *mut crate::leanh::LeanObject,
    mut v_a_727_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_728_ = l___private_Init_While_0__whileM_erased___at___00Lean_EditDistance_levenshtein_spec__1___redArg(v_str2_721_, v___x_722_, v___x_723_, v___x_724_, v_str1_725_, v_a_727_);
    return v___x_728_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_EditDistance_levenshtein_spec__1___boxed(
    mut v_str2_729_: *mut crate::leanh::LeanObject,
    mut v___x_730_: *mut crate::leanh::LeanObject,
    mut v___x_731_: *mut crate::leanh::LeanObject,
    mut v___x_732_: *mut crate::leanh::LeanObject,
    mut v_str1_733_: *mut crate::leanh::LeanObject,
    mut v_inst_734_: *mut crate::leanh::LeanObject,
    mut v_a_735_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec_ref(v_str1_733_);
    crate::leanh::lean_dec(v___x_732_);
    crate::leanh::lean_dec_ref(v___x_731_);
    crate::leanh::lean_dec(v___x_730_);
    crate::leanh::lean_dec_ref(v_str2_729_);
    return v_res_736_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_EditDistance_levenshtein_spec__3(
    mut v_str2_737_: *mut crate::leanh::LeanObject,
    mut v___x_738_: *mut crate::leanh::LeanObject,
    mut v_str1_739_: *mut crate::leanh::LeanObject,
    mut v_cutoff_740_: *mut crate::leanh::LeanObject,
    mut v_inst_741_: *mut crate::leanh::LeanObject,
    mut v_a_742_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_743_ = l___private_Init_While_0__whileM_erased___at___00Lean_EditDistance_levenshtein_spec__3___redArg(v_str2_737_, v___x_738_, v_str1_739_, v_cutoff_740_, v_a_742_);
    return v___x_743_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_EditDistance_levenshtein_spec__3___boxed(
    mut v_str2_744_: *mut crate::leanh::LeanObject,
    mut v___x_745_: *mut crate::leanh::LeanObject,
    mut v_str1_746_: *mut crate::leanh::LeanObject,
    mut v_cutoff_747_: *mut crate::leanh::LeanObject,
    mut v_inst_748_: *mut crate::leanh::LeanObject,
    mut v_a_749_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_750_ =
        l___private_Init_While_0__whileM_erased___at___00Lean_EditDistance_levenshtein_spec__3(
            v_str2_744_,
            v___x_745_,
            v_str1_746_,
            v_cutoff_747_,
            v_inst_748_,
            v_a_749_,
        );
    crate::leanh::lean_dec(v_cutoff_747_);
    crate::leanh::lean_dec_ref(v_str1_746_);
    crate::leanh::lean_dec(v___x_745_);
    crate::leanh::lean_dec_ref(v_str2_744_);
    return v_res_750_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3(
    mut v_str1_751_: *mut crate::leanh::LeanObject,
    mut v___x_752_: *mut crate::leanh::LeanObject,
    mut v_str2_753_: *mut crate::leanh::LeanObject,
    mut v_cutoff_754_: *mut crate::leanh::LeanObject,
    mut v_inst_755_: *mut crate::leanh::LeanObject,
    mut v_a_756_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_757_ = l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___redArg(v_str1_751_, v___x_752_, v_str2_753_, v_cutoff_754_, v_a_756_);
    return v___x_757_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___boxed(
    mut v_str1_758_: *mut crate::leanh::LeanObject,
    mut v___x_759_: *mut crate::leanh::LeanObject,
    mut v_str2_760_: *mut crate::leanh::LeanObject,
    mut v_cutoff_761_: *mut crate::leanh::LeanObject,
    mut v_inst_762_: *mut crate::leanh::LeanObject,
    mut v_a_763_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_764_ = l___private_Init_While_0__whileM_erased___at___00__private_Init_While_0__whileM_erased___at___00Lean_EditDistance_levenshtein_spec__3_spec__3(v_str1_758_, v___x_759_, v_str2_760_, v_cutoff_761_, v_inst_762_, v_a_763_);
    crate::leanh::lean_dec(v_cutoff_761_);
    crate::leanh::lean_dec_ref(v_str2_760_);
    crate::leanh::lean_dec(v___x_759_);
    crate::leanh::lean_dec_ref(v_str1_758_);
    return v_res_764_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Data_EditDistance(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_String_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Vector_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Order(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Order_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_While(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Length(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data_EditDistance(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Data_EditDistance(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_String_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Vector_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Order(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Order_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Range(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_While(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Length(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_EditDistance(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Data_EditDistance(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Data_EditDistance(builtin);
}
