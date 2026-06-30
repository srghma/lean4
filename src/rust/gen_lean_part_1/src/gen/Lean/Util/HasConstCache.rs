// Lean compiler output
// Module: Lean.Util.HasConstCache
// Imports: Lean.Expr Std.Data.HashMap.Raw
use crate::ffi::{
    lean_array_fget, lean_array_fset, lean_array_get_size, lean_array_uget_borrowed,
    lean_array_uset, lean_mk_array, lean_name_eq, lean_nat_add, lean_nat_dec_le, lean_nat_dec_lt,
    lean_nat_div, lean_nat_mul, lean_ptr_addr, lean_uint64_shift_right, lean_uint64_to_usize,
    lean_uint64_xor, lean_usize_add, lean_usize_dec_eq, lean_usize_land, lean_usize_of_nat,
    lean_usize_sub,
};
use crate::r#gen::Lean::Expr::{
    initialize_Lean_Expr, l_Lean_Expr_hash, runtime_initialize_Lean_Expr,
};
use crate::r#gen::Std::Data::HashMap::Raw::{
    initialize_Std_Data_HashMap_Raw, runtime_initialize_Std_Data_HashMap_Raw,
};
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__0___redArg(
    mut v_a_356_: *mut leanh::LeanObject,
    mut v_x_357_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_358_: u8 = 0;
    let mut v_key_359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_361_: usize = 0;
    let mut v___x_362_: usize = 0;
    let mut v___x_363_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_357_) == 0 {
                    v___x_358_ = 0;
                    return v___x_358_;
                } else {
                    v_key_359_ = leanh::lean_ctor_get(v_x_357_, 0);
                    v_tail_360_ = leanh::lean_ctor_get(v_x_357_, 2);
                    v___x_361_ = lean_ptr_addr(v_key_359_);
                    v___x_362_ = lean_ptr_addr(v_a_356_);
                    v___x_363_ = lean_usize_dec_eq(v___x_361_, v___x_362_);
                    if v___x_363_ == 0 {
                        v_x_357_ = v_tail_360_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_363_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__0___redArg___boxed(
    mut v_a_365_: *mut leanh::LeanObject,
    mut v_x_366_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_367_: u8 = 0;
    let mut v_r_368_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_367_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__0___redArg(v_a_365_, v_x_366_);
    leanh::lean_dec(v_x_366_);
    leanh::lean_dec_ref(v_a_365_);
    v_r_368_ = leanh::lean_box((v_res_367_) as usize);
    return v_r_368_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__2___redArg(
    mut v_a_369_: *mut leanh::LeanObject,
    mut v_b_370_: *mut leanh::LeanObject,
    mut v_x_371_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_377_: u8 = 0;
    let mut v___x_378_: usize = 0;
    let mut v___x_379_: usize = 0;
    let mut v___x_380_: u8 = 0;
    let mut v___x_381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_388_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_371_) == 0 {
                    leanh::lean_dec(v_b_370_);
                    leanh::lean_dec_ref(v_a_369_);
                    return v_x_371_;
                } else {
                    v_key_372_ = leanh::lean_ctor_get(v_x_371_, 0);
                    v_value_373_ = leanh::lean_ctor_get(v_x_371_, 1);
                    v_tail_374_ = leanh::lean_ctor_get(v_x_371_, 2);
                    v_isSharedCheck_388_ = (!leanh::lean_is_exclusive(v_x_371_)) as u8;
                    if v_isSharedCheck_388_ == 0 {
                        v___x_376_ = v_x_371_;
                        v_isShared_377_ = v_isSharedCheck_388_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_374_);
                        leanh::lean_inc(v_value_373_);
                        leanh::lean_inc(v_key_372_);
                        leanh::lean_dec(v_x_371_);
                        v___x_376_ = leanh::lean_box(0);
                        v_isShared_377_ = v_isSharedCheck_388_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_378_ = lean_ptr_addr(v_key_372_);
                v___x_379_ = lean_ptr_addr(v_a_369_);
                v___x_380_ = lean_usize_dec_eq(v___x_378_, v___x_379_);
                if v___x_380_ == 0 {
                    v___x_381_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__2___redArg(v_a_369_, v_b_370_, v_tail_374_);
                    if v_isShared_377_ == 0 {
                        leanh::lean_ctor_set(v___x_376_, 2, v___x_381_);
                        v___x_383_ = v___x_376_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_384_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_384_, 0, v_key_372_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_384_, 1, v_value_373_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_384_, 2, v___x_381_);
                        v___x_383_ = v_reuseFailAlloc_384_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_value_373_);
                    leanh::lean_dec(v_key_372_);
                    if v_isShared_377_ == 0 {
                        leanh::lean_ctor_set(v___x_376_, 1, v_b_370_);
                        leanh::lean_ctor_set(v___x_376_, 0, v_a_369_);
                        v___x_386_ = v___x_376_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_387_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_387_, 0, v_a_369_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_387_, 1, v_b_370_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_387_, 2, v_tail_374_);
                        v___x_386_ = v_reuseFailAlloc_387_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_383_;
            }
            3 => {
                return v___x_386_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__1_spec__2_spec__3___redArg(
    mut v_x_389_: *mut leanh::LeanObject,
    mut v_x_390_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_396_: u8 = 0;
    let mut v___x_397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_398_: u64 = 0;
    let mut v___x_399_: u64 = 0;
    let mut v___x_400_: u64 = 0;
    let mut v_fold_401_: u64 = 0;
    let mut v___x_402_: u64 = 0;
    let mut v___x_403_: u64 = 0;
    let mut v___x_404_: u64 = 0;
    let mut v___x_405_: usize = 0;
    let mut v___x_406_: usize = 0;
    let mut v___x_407_: usize = 0;
    let mut v___x_408_: usize = 0;
    let mut v___x_409_: usize = 0;
    let mut v___x_410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_416_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_390_) == 0 {
                    return v_x_389_;
                } else {
                    v_key_391_ = leanh::lean_ctor_get(v_x_390_, 0);
                    v_value_392_ = leanh::lean_ctor_get(v_x_390_, 1);
                    v_tail_393_ = leanh::lean_ctor_get(v_x_390_, 2);
                    v_isSharedCheck_416_ = (!leanh::lean_is_exclusive(v_x_390_)) as u8;
                    if v_isSharedCheck_416_ == 0 {
                        v___x_395_ = v_x_390_;
                        v_isShared_396_ = v_isSharedCheck_416_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_393_);
                        leanh::lean_inc(v_value_392_);
                        leanh::lean_inc(v_key_391_);
                        leanh::lean_dec(v_x_390_);
                        v___x_395_ = leanh::lean_box(0);
                        v_isShared_396_ = v_isSharedCheck_416_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_397_ = lean_array_get_size(v_x_389_);
                v___x_398_ = l_Lean_Expr_hash(v_key_391_);
                v___x_399_ = 32u64;
                v___x_400_ = lean_uint64_shift_right(v___x_398_, v___x_399_);
                v_fold_401_ = lean_uint64_xor(v___x_398_, v___x_400_);
                v___x_402_ = 16u64;
                v___x_403_ = lean_uint64_shift_right(v_fold_401_, v___x_402_);
                v___x_404_ = lean_uint64_xor(v_fold_401_, v___x_403_);
                v___x_405_ = lean_uint64_to_usize(v___x_404_);
                v___x_406_ = lean_usize_of_nat(v___x_397_);
                v___x_407_ = 1usize;
                v___x_408_ = lean_usize_sub(v___x_406_, v___x_407_);
                v___x_409_ = lean_usize_land(v___x_405_, v___x_408_);
                v___x_410_ = lean_array_uget_borrowed(v_x_389_, v___x_409_);
                leanh::lean_inc(v___x_410_);
                if v_isShared_396_ == 0 {
                    leanh::lean_ctor_set(v___x_395_, 2, v___x_410_);
                    v___x_412_ = v___x_395_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_415_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_415_, 0, v_key_391_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_415_, 1, v_value_392_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_415_, 2, v___x_410_);
                    v___x_412_ = v_reuseFailAlloc_415_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_413_ = lean_array_uset(v_x_389_, v___x_409_, v___x_412_);
                v_x_389_ = v___x_413_;
                v_x_390_ = v_tail_393_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__1_spec__2___redArg(
    mut v_i_417_: *mut leanh::LeanObject,
    mut v_source_418_: *mut leanh::LeanObject,
    mut v_target_419_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_421_: u8 = 0;
    let mut v_es_422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_420_ = lean_array_get_size(v_source_418_);
                v___x_421_ = lean_nat_dec_lt(v_i_417_, v___x_420_);
                if v___x_421_ == 0 {
                    leanh::lean_dec_ref(v_source_418_);
                    leanh::lean_dec(v_i_417_);
                    return v_target_419_;
                } else {
                    v_es_422_ = lean_array_fget(v_source_418_, v_i_417_);
                    v___x_423_ = leanh::lean_box(0);
                    v_source_424_ = lean_array_fset(v_source_418_, v_i_417_, v___x_423_);
                    v_target_425_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__1_spec__2_spec__3___redArg(v_target_419_, v_es_422_);
                    v___x_426_ = leanh::lean_unsigned_to_nat(1);
                    v___x_427_ = lean_nat_add(v_i_417_, v___x_426_);
                    leanh::lean_dec(v_i_417_);
                    v_i_417_ = v___x_427_;
                    v_source_418_ = v_source_424_;
                    v_target_419_ = v_target_425_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__1___redArg(
    mut v_data_429_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_436_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_430_ = lean_array_get_size(v_data_429_);
    v___x_431_ = leanh::lean_unsigned_to_nat(2);
    v_nbuckets_432_ = lean_nat_mul(v___x_430_, v___x_431_);
    v___x_433_ = leanh::lean_unsigned_to_nat(0);
    v___x_434_ = leanh::lean_box(0);
    v___x_435_ = lean_mk_array(v_nbuckets_432_, v___x_434_);
    v___x_436_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__1_spec__2___redArg(v___x_433_, v_data_429_, v___x_435_);
    return v___x_436_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0___redArg(
    mut v_m_437_: *mut leanh::LeanObject,
    mut v_a_438_: *mut leanh::LeanObject,
    mut v_b_439_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_444_: u8 = 0;
    let mut v___x_445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_446_: u64 = 0;
    let mut v___x_447_: u64 = 0;
    let mut v___x_448_: u64 = 0;
    let mut v_fold_449_: u64 = 0;
    let mut v___x_450_: u64 = 0;
    let mut v___x_451_: u64 = 0;
    let mut v___x_452_: u64 = 0;
    let mut v___x_453_: usize = 0;
    let mut v___x_454_: usize = 0;
    let mut v___x_455_: usize = 0;
    let mut v___x_456_: usize = 0;
    let mut v___x_457_: usize = 0;
    let mut v_bkt_458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_459_: u8 = 0;
    let mut v___x_460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_469_: u8 = 0;
    let mut v_val_470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_484_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_440_ = leanh::lean_ctor_get(v_m_437_, 0);
                v_buckets_441_ = leanh::lean_ctor_get(v_m_437_, 1);
                v_isSharedCheck_484_ = (!leanh::lean_is_exclusive(v_m_437_)) as u8;
                if v_isSharedCheck_484_ == 0 {
                    v___x_443_ = v_m_437_;
                    v_isShared_444_ = v_isSharedCheck_484_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_441_);
                    leanh::lean_inc(v_size_440_);
                    leanh::lean_dec(v_m_437_);
                    v___x_443_ = leanh::lean_box(0);
                    v_isShared_444_ = v_isSharedCheck_484_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_445_ = lean_array_get_size(v_buckets_441_);
                v___x_446_ = l_Lean_Expr_hash(v_a_438_);
                v___x_447_ = 32u64;
                v___x_448_ = lean_uint64_shift_right(v___x_446_, v___x_447_);
                v_fold_449_ = lean_uint64_xor(v___x_446_, v___x_448_);
                v___x_450_ = 16u64;
                v___x_451_ = lean_uint64_shift_right(v_fold_449_, v___x_450_);
                v___x_452_ = lean_uint64_xor(v_fold_449_, v___x_451_);
                v___x_453_ = lean_uint64_to_usize(v___x_452_);
                v___x_454_ = lean_usize_of_nat(v___x_445_);
                v___x_455_ = 1usize;
                v___x_456_ = lean_usize_sub(v___x_454_, v___x_455_);
                v___x_457_ = lean_usize_land(v___x_453_, v___x_456_);
                v_bkt_458_ = lean_array_uget_borrowed(v_buckets_441_, v___x_457_);
                v___x_459_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__0___redArg(v_a_438_, v_bkt_458_);
                if v___x_459_ == 0 {
                    v___x_460_ = leanh::lean_unsigned_to_nat(1);
                    v_size_x27_461_ = lean_nat_add(v_size_440_, v___x_460_);
                    leanh::lean_dec(v_size_440_);
                    leanh::lean_inc(v_bkt_458_);
                    v___x_462_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_462_, 0, v_a_438_);
                    leanh::lean_ctor_set(v___x_462_, 1, v_b_439_);
                    leanh::lean_ctor_set(v___x_462_, 2, v_bkt_458_);
                    v_buckets_x27_463_ = lean_array_uset(v_buckets_441_, v___x_457_, v___x_462_);
                    v___x_464_ = leanh::lean_unsigned_to_nat(4);
                    v___x_465_ = lean_nat_mul(v_size_x27_461_, v___x_464_);
                    v___x_466_ = leanh::lean_unsigned_to_nat(3);
                    v___x_467_ = lean_nat_div(v___x_465_, v___x_466_);
                    leanh::lean_dec(v___x_465_);
                    v___x_468_ = lean_array_get_size(v_buckets_x27_463_);
                    v___x_469_ = lean_nat_dec_le(v___x_467_, v___x_468_);
                    leanh::lean_dec(v___x_467_);
                    if v___x_469_ == 0 {
                        v_val_470_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__1___redArg(v_buckets_x27_463_);
                        if v_isShared_444_ == 0 {
                            leanh::lean_ctor_set(v___x_443_, 1, v_val_470_);
                            leanh::lean_ctor_set(v___x_443_, 0, v_size_x27_461_);
                            v___x_472_ = v___x_443_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_473_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_473_, 0, v_size_x27_461_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_473_, 1, v_val_470_);
                            v___x_472_ = v_reuseFailAlloc_473_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_444_ == 0 {
                            leanh::lean_ctor_set(v___x_443_, 1, v_buckets_x27_463_);
                            leanh::lean_ctor_set(v___x_443_, 0, v_size_x27_461_);
                            v___x_475_ = v___x_443_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_476_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_476_, 0, v_size_x27_461_);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_476_,
                                1,
                                v_buckets_x27_463_,
                            );
                            v___x_475_ = v_reuseFailAlloc_476_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_inc(v_bkt_458_);
                    v___x_477_ = leanh::lean_box(0);
                    v_buckets_x27_478_ = lean_array_uset(v_buckets_441_, v___x_457_, v___x_477_);
                    v___x_479_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__2___redArg(v_a_438_, v_b_439_, v_bkt_458_);
                    v___x_480_ = lean_array_uset(v_buckets_x27_478_, v___x_457_, v___x_479_);
                    if v_isShared_444_ == 0 {
                        leanh::lean_ctor_set(v___x_443_, 1, v___x_480_);
                        v___x_482_ = v___x_443_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_483_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_483_, 0, v_size_440_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_483_, 1, v___x_480_);
                        v___x_482_ = v_reuseFailAlloc_483_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_472_;
            }
            3 => {
                return v___x_475_;
            }
            4 => {
                return v___x_482_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache___redArg(
    mut v_e_485_: *mut leanh::LeanObject,
    mut v_r_486_: u8,
    mut v_a_487_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_491_: u8 = 0;
    v_buckets_488_ = leanh::lean_ctor_get(v_a_487_, 1);
    v___x_489_ = leanh::lean_unsigned_to_nat(0);
    v___x_490_ = lean_array_get_size(v_buckets_488_);
    v___x_491_ = lean_nat_dec_lt(v___x_489_, v___x_490_);
    if v___x_491_ == 0 {
        let mut v___x_492_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_493_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_e_485_);
        v___x_492_ = leanh::lean_box((v_r_486_) as usize);
        v___x_493_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_493_, 0, v___x_492_);
        leanh::lean_ctor_set(v___x_493_, 1, v_a_487_);
        return v___x_493_;
    } else {
        let mut v___x_494_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_495_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_496_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_497_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_494_ = leanh::lean_box((v_r_486_) as usize);
        v___x_495_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0___redArg(v_a_487_, v_e_485_, v___x_494_);
        v___x_496_ = leanh::lean_box((v_r_486_) as usize);
        v___x_497_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_497_, 0, v___x_496_);
        leanh::lean_ctor_set(v___x_497_, 1, v___x_495_);
        return v___x_497_;
    }
}
pub unsafe fn l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache___redArg___boxed(
    mut v_e_498_: *mut leanh::LeanObject,
    mut v_r_499_: *mut leanh::LeanObject,
    mut v_a_500_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_r_boxed_501_: u8 = 0;
    let mut v_res_502_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_r_boxed_501_ = (leanh::lean_unbox(v_r_499_) as u8);
    v_res_502_ =
        l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache___redArg(
            v_e_498_,
            v_r_boxed_501_,
            v_a_500_,
        );
    return v_res_502_;
}
pub unsafe fn l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache(
    mut v_declNames_503_: *mut leanh::LeanObject,
    mut v_e_504_: *mut leanh::LeanObject,
    mut v_r_505_: u8,
    mut v_a_506_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_507_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_507_ =
        l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache___redArg(
            v_e_504_, v_r_505_, v_a_506_,
        );
    return v___x_507_;
}
pub unsafe fn l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache___boxed(
    mut v_declNames_508_: *mut leanh::LeanObject,
    mut v_e_509_: *mut leanh::LeanObject,
    mut v_r_510_: *mut leanh::LeanObject,
    mut v_a_511_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_r_boxed_512_: u8 = 0;
    let mut v_res_513_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_r_boxed_512_ = (leanh::lean_unbox(v_r_510_) as u8);
    v_res_513_ = l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache(
        v_declNames_508_,
        v_e_509_,
        v_r_boxed_512_,
        v_a_511_,
    );
    leanh::lean_dec_ref(v_declNames_508_);
    return v_res_513_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0(
    mut v_00_u03b2_514_: *mut leanh::LeanObject,
    mut v_m_515_: *mut leanh::LeanObject,
    mut v_a_516_: *mut leanh::LeanObject,
    mut v_b_517_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_518_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_518_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0___redArg(v_m_515_, v_a_516_, v_b_517_);
    return v___x_518_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__0(
    mut v_00_u03b2_519_: *mut leanh::LeanObject,
    mut v_a_520_: *mut leanh::LeanObject,
    mut v_x_521_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_522_: u8 = 0;
    v___x_522_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__0___redArg(v_a_520_, v_x_521_);
    return v___x_522_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__0___boxed(
    mut v_00_u03b2_523_: *mut leanh::LeanObject,
    mut v_a_524_: *mut leanh::LeanObject,
    mut v_x_525_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_526_: u8 = 0;
    let mut v_r_527_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_526_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__0(v_00_u03b2_523_, v_a_524_, v_x_525_);
    leanh::lean_dec(v_x_525_);
    leanh::lean_dec_ref(v_a_524_);
    v_r_527_ = leanh::lean_box((v_res_526_) as usize);
    return v_r_527_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__1(
    mut v_00_u03b2_528_: *mut leanh::LeanObject,
    mut v_data_529_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_530_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_530_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__1___redArg(v_data_529_);
    return v___x_530_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__2(
    mut v_00_u03b2_531_: *mut leanh::LeanObject,
    mut v_a_532_: *mut leanh::LeanObject,
    mut v_b_533_: *mut leanh::LeanObject,
    mut v_x_534_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_535_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_535_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__2___redArg(v_a_532_, v_b_533_, v_x_534_);
    return v___x_535_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__1_spec__2(
    mut v_00_u03b2_536_: *mut leanh::LeanObject,
    mut v_i_537_: *mut leanh::LeanObject,
    mut v_source_538_: *mut leanh::LeanObject,
    mut v_target_539_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_540_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_540_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__1_spec__2___redArg(v_i_537_, v_source_538_, v_target_539_);
    return v___x_540_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__1_spec__2_spec__3(
    mut v_00_u03b2_541_: *mut leanh::LeanObject,
    mut v_x_542_: *mut leanh::LeanObject,
    mut v_x_543_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_544_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_544_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__1_spec__2_spec__3___redArg(v_x_542_, v_x_543_);
    return v___x_544_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1_spec__2___redArg(
    mut v_a_545_: *mut leanh::LeanObject,
    mut v_x_546_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_551_: usize = 0;
    let mut v___x_552_: usize = 0;
    let mut v___x_553_: u8 = 0;
    let mut v___x_555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_546_) == 0 {
                    v___x_547_ = leanh::lean_box(0);
                    return v___x_547_;
                } else {
                    v_key_548_ = leanh::lean_ctor_get(v_x_546_, 0);
                    v_value_549_ = leanh::lean_ctor_get(v_x_546_, 1);
                    v_tail_550_ = leanh::lean_ctor_get(v_x_546_, 2);
                    v___x_551_ = lean_ptr_addr(v_key_548_);
                    v___x_552_ = lean_ptr_addr(v_a_545_);
                    v___x_553_ = lean_usize_dec_eq(v___x_551_, v___x_552_);
                    if v___x_553_ == 0 {
                        v_x_546_ = v_tail_550_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_inc(v_value_549_);
                        v___x_555_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_555_, 0, v_value_549_);
                        return v___x_555_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1_spec__2___redArg___boxed(
    mut v_a_556_: *mut leanh::LeanObject,
    mut v_x_557_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_558_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_558_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1_spec__2___redArg(v_a_556_, v_x_557_);
    leanh::lean_dec(v_x_557_);
    leanh::lean_dec_ref(v_a_556_);
    return v_res_558_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1___redArg(
    mut v_m_559_: *mut leanh::LeanObject,
    mut v_a_560_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_563_: u64 = 0;
    let mut v___x_564_: u64 = 0;
    let mut v___x_565_: u64 = 0;
    let mut v_fold_566_: u64 = 0;
    let mut v___x_567_: u64 = 0;
    let mut v___x_568_: u64 = 0;
    let mut v___x_569_: u64 = 0;
    let mut v___x_570_: usize = 0;
    let mut v___x_571_: usize = 0;
    let mut v___x_572_: usize = 0;
    let mut v___x_573_: usize = 0;
    let mut v___x_574_: usize = 0;
    let mut v___x_575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_576_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_561_ = leanh::lean_ctor_get(v_m_559_, 1);
    v___x_562_ = lean_array_get_size(v_buckets_561_);
    v___x_563_ = l_Lean_Expr_hash(v_a_560_);
    v___x_564_ = 32u64;
    v___x_565_ = lean_uint64_shift_right(v___x_563_, v___x_564_);
    v_fold_566_ = lean_uint64_xor(v___x_563_, v___x_565_);
    v___x_567_ = 16u64;
    v___x_568_ = lean_uint64_shift_right(v_fold_566_, v___x_567_);
    v___x_569_ = lean_uint64_xor(v_fold_566_, v___x_568_);
    v___x_570_ = lean_uint64_to_usize(v___x_569_);
    v___x_571_ = lean_usize_of_nat(v___x_562_);
    v___x_572_ = 1usize;
    v___x_573_ = lean_usize_sub(v___x_571_, v___x_572_);
    v___x_574_ = lean_usize_land(v___x_570_, v___x_573_);
    v___x_575_ = lean_array_uget_borrowed(v_buckets_561_, v___x_574_);
    v___x_576_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1_spec__2___redArg(v_a_560_, v___x_575_);
    return v___x_576_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1___redArg___boxed(
    mut v_m_577_: *mut leanh::LeanObject,
    mut v_a_578_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_579_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_579_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1___redArg(v_m_577_, v_a_578_);
    leanh::lean_dec_ref(v_a_578_);
    leanh::lean_dec_ref(v_m_577_);
    return v_res_579_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_HasConstCache_containsUnsafe_spec__0_spec__0(
    mut v_a_580_: *mut leanh::LeanObject,
    mut v_as_581_: *mut leanh::LeanObject,
    mut v_i_582_: usize,
    mut v_stop_583_: usize,
) -> u8 {
    let mut v___x_584_: u8 = 0;
    let mut v___x_585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_586_: u8 = 0;
    let mut v___x_587_: usize = 0;
    let mut v___x_588_: usize = 0;
    let mut v___x_590_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_584_ = lean_usize_dec_eq(v_i_582_, v_stop_583_);
                if v___x_584_ == 0 {
                    v___x_585_ = lean_array_uget_borrowed(v_as_581_, v_i_582_);
                    v___x_586_ = lean_name_eq(v_a_580_, v___x_585_);
                    if v___x_586_ == 0 {
                        v___x_587_ = 1usize;
                        v___x_588_ = lean_usize_add(v_i_582_, v___x_587_);
                        v_i_582_ = v___x_588_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_586_;
                    }
                } else {
                    v___x_590_ = 0;
                    return v___x_590_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_HasConstCache_containsUnsafe_spec__0_spec__0___boxed(
    mut v_a_591_: *mut leanh::LeanObject,
    mut v_as_592_: *mut leanh::LeanObject,
    mut v_i_593_: *mut leanh::LeanObject,
    mut v_stop_594_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_595_: usize = 0;
    let mut v_stop_boxed_596_: usize = 0;
    let mut v_res_597_: u8 = 0;
    let mut v_r_598_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_595_ = leanh::lean_unbox_usize(v_i_593_);
    leanh::lean_dec(v_i_593_);
    v_stop_boxed_596_ = leanh::lean_unbox_usize(v_stop_594_);
    leanh::lean_dec(v_stop_594_);
    v_res_597_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_HasConstCache_containsUnsafe_spec__0_spec__0(v_a_591_, v_as_592_, v_i_boxed_595_, v_stop_boxed_596_);
    leanh::lean_dec_ref(v_as_592_);
    leanh::lean_dec(v_a_591_);
    v_r_598_ = leanh::lean_box((v_res_597_) as usize);
    return v_r_598_;
}
pub unsafe fn l_Array_contains___at___00Lean_HasConstCache_containsUnsafe_spec__0(
    mut v_as_599_: *mut leanh::LeanObject,
    mut v_a_600_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_603_: u8 = 0;
    v___x_601_ = leanh::lean_unsigned_to_nat(0);
    v___x_602_ = lean_array_get_size(v_as_599_);
    v___x_603_ = lean_nat_dec_lt(v___x_601_, v___x_602_);
    if v___x_603_ == 0 {
        return v___x_603_;
    } else {
        if v___x_603_ == 0 {
            return v___x_603_;
        } else {
            let mut v___x_604_: usize = 0;
            let mut v___x_605_: usize = 0;
            let mut v___x_606_: u8 = 0;
            v___x_604_ = 0usize;
            v___x_605_ = lean_usize_of_nat(v___x_602_);
            v___x_606_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_HasConstCache_containsUnsafe_spec__0_spec__0(v_a_600_, v_as_599_, v___x_604_, v___x_605_);
            return v___x_606_;
        }
    }
}
pub unsafe fn l_Array_contains___at___00Lean_HasConstCache_containsUnsafe_spec__0___boxed(
    mut v_as_607_: *mut leanh::LeanObject,
    mut v_a_608_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_609_: u8 = 0;
    let mut v_r_610_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_609_ =
        l_Array_contains___at___00Lean_HasConstCache_containsUnsafe_spec__0(v_as_607_, v_a_608_);
    leanh::lean_dec(v_a_608_);
    leanh::lean_dec_ref(v_as_607_);
    v_r_610_ = leanh::lean_box((v_res_609_) as usize);
    return v_r_610_;
}
pub unsafe fn l_Lean_HasConstCache_containsUnsafe(
    mut v_declNames_611_: *mut leanh::LeanObject,
    mut v_e_612_: *mut leanh::LeanObject,
    mut v_a_613_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_618_: u8 = 0;
    let mut v___x_619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_624_: u8 = 0;
    let mut v___x_625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_630_: u8 = 0;
    let mut v___x_631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_d_633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_638_: u8 = 0;
    let mut v_snd_639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_643_: u8 = 0;
    let mut v___x_644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_650_: u8 = 0;
    let mut v_snd_651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_662_: u8 = 0;
    let mut v_snd_663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_666_: u8 = 0;
    let mut v_snd_667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_673_: u8 = 0;
    let mut v___x_674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_679_: u8 = 0;
    let mut v___x_680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_681_: u8 = 0;
    let mut v___x_682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_687_: u8 = 0;
    let mut v___x_688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_684_ = leanh::lean_ctor_get(v_a_613_, 1);
                v___x_685_ = leanh::lean_unsigned_to_nat(0);
                v___x_686_ = lean_array_get_size(v_buckets_684_);
                v___x_687_ = lean_nat_dec_lt(v___x_685_, v___x_686_);
                if v___x_687_ == 0 {
                    state = 5;
                    continue;
                } else {
                    v___x_688_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1___redArg(v_a_613_, v_e_612_);
                    if leanh::lean_obj_tag(v___x_688_) == 1 {
                        leanh::lean_dec_ref(v_e_612_);
                        v_val_689_ = leanh::lean_ctor_get(v___x_688_, 0);
                        leanh::lean_inc(v_val_689_);
                        leanh::lean_dec_ref_known(v___x_688_, 1);
                        v___x_690_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_690_, 0, v_val_689_);
                        leanh::lean_ctor_set(v___x_690_, 1, v_a_613_);
                        return v___x_690_;
                    } else {
                        leanh::lean_dec(v___x_688_);
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_616_ = leanh::lean_ctor_get(v___y_615_, 0);
                leanh::lean_inc(v_fst_616_);
                v_snd_617_ = leanh::lean_ctor_get(v___y_615_, 1);
                leanh::lean_inc(v_snd_617_);
                leanh::lean_dec_ref(v___y_615_);
                v___x_618_ = (leanh::lean_unbox(v_fst_616_) as u8);
                leanh::lean_dec(v_fst_616_);
                v___x_619_ = l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache___redArg(v_e_612_, v___x_618_, v_snd_617_);
                return v___x_619_;
            }
            2 => {
                v_fst_622_ = leanh::lean_ctor_get(v___y_621_, 0);
                leanh::lean_inc(v_fst_622_);
                v_snd_623_ = leanh::lean_ctor_get(v___y_621_, 1);
                leanh::lean_inc(v_snd_623_);
                leanh::lean_dec_ref(v___y_621_);
                v___x_624_ = (leanh::lean_unbox(v_fst_622_) as u8);
                leanh::lean_dec(v_fst_622_);
                v___x_625_ = l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache___redArg(v_e_612_, v___x_624_, v_snd_623_);
                return v___x_625_;
            }
            3 => {
                v_fst_628_ = leanh::lean_ctor_get(v___y_627_, 0);
                leanh::lean_inc(v_fst_628_);
                v_snd_629_ = leanh::lean_ctor_get(v___y_627_, 1);
                leanh::lean_inc(v_snd_629_);
                leanh::lean_dec_ref(v___y_627_);
                v___x_630_ = (leanh::lean_unbox(v_fst_628_) as u8);
                leanh::lean_dec(v_fst_628_);
                v___x_631_ = l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache___redArg(v_e_612_, v___x_630_, v_snd_629_);
                return v___x_631_;
            }
            4 => {
                v___x_636_ =
                    l_Lean_HasConstCache_containsUnsafe(v_declNames_611_, v_d_633_, v___y_635_);
                v_fst_637_ = leanh::lean_ctor_get(v___x_636_, 0);
                leanh::lean_inc(v_fst_637_);
                v___x_638_ = (leanh::lean_unbox(v_fst_637_) as u8);
                leanh::lean_dec(v_fst_637_);
                if v___x_638_ == 0 {
                    v_snd_639_ = leanh::lean_ctor_get(v___x_636_, 1);
                    leanh::lean_inc(v_snd_639_);
                    leanh::lean_dec_ref(v___x_636_);
                    v___x_640_ =
                        l_Lean_HasConstCache_containsUnsafe(v_declNames_611_, v_b_634_, v_snd_639_);
                    v___y_627_ = v___x_640_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_b_634_);
                    v___y_627_ = v___x_636_;
                    state = 3;
                    continue;
                }
            }
            5 => match leanh::lean_obj_tag(v_e_612_) {
                4 => {
                    v_declName_642_ = leanh::lean_ctor_get(v_e_612_, 0);
                    leanh::lean_inc(v_declName_642_);
                    leanh::lean_dec_ref_known(v_e_612_, 2);
                    v___x_643_ =
                        l_Array_contains___at___00Lean_HasConstCache_containsUnsafe_spec__0(
                            v_declNames_611_,
                            v_declName_642_,
                        );
                    leanh::lean_dec(v_declName_642_);
                    v___x_644_ = leanh::lean_box((v___x_643_) as usize);
                    v___x_645_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_645_, 0, v___x_644_);
                    leanh::lean_ctor_set(v___x_645_, 1, v_a_613_);
                    return v___x_645_;
                }
                5 => {
                    v_fn_646_ = leanh::lean_ctor_get(v_e_612_, 0);
                    v_arg_647_ = leanh::lean_ctor_get(v_e_612_, 1);
                    leanh::lean_inc_ref(v_fn_646_);
                    v___x_648_ =
                        l_Lean_HasConstCache_containsUnsafe(v_declNames_611_, v_fn_646_, v_a_613_);
                    v_fst_649_ = leanh::lean_ctor_get(v___x_648_, 0);
                    leanh::lean_inc(v_fst_649_);
                    v___x_650_ = (leanh::lean_unbox(v_fst_649_) as u8);
                    leanh::lean_dec(v_fst_649_);
                    if v___x_650_ == 0 {
                        v_snd_651_ = leanh::lean_ctor_get(v___x_648_, 1);
                        leanh::lean_inc(v_snd_651_);
                        leanh::lean_dec_ref(v___x_648_);
                        leanh::lean_inc_ref(v_arg_647_);
                        v___x_652_ = l_Lean_HasConstCache_containsUnsafe(
                            v_declNames_611_,
                            v_arg_647_,
                            v_snd_651_,
                        );
                        v___y_621_ = v___x_652_;
                        state = 2;
                        continue;
                    } else {
                        v___y_621_ = v___x_648_;
                        state = 2;
                        continue;
                    }
                }
                6 => {
                    v_binderType_653_ = leanh::lean_ctor_get(v_e_612_, 1);
                    v_body_654_ = leanh::lean_ctor_get(v_e_612_, 2);
                    leanh::lean_inc_ref(v_body_654_);
                    leanh::lean_inc_ref(v_binderType_653_);
                    v_d_633_ = v_binderType_653_;
                    v_b_634_ = v_body_654_;
                    v___y_635_ = v_a_613_;
                    state = 4;
                    continue;
                }
                7 => {
                    v_binderType_655_ = leanh::lean_ctor_get(v_e_612_, 1);
                    v_body_656_ = leanh::lean_ctor_get(v_e_612_, 2);
                    leanh::lean_inc_ref(v_body_656_);
                    leanh::lean_inc_ref(v_binderType_655_);
                    v_d_633_ = v_binderType_655_;
                    v_b_634_ = v_body_656_;
                    v___y_635_ = v_a_613_;
                    state = 4;
                    continue;
                }
                8 => {
                    v_type_657_ = leanh::lean_ctor_get(v_e_612_, 1);
                    v_value_658_ = leanh::lean_ctor_get(v_e_612_, 2);
                    v_body_659_ = leanh::lean_ctor_get(v_e_612_, 3);
                    leanh::lean_inc_ref(v_type_657_);
                    v___x_660_ = l_Lean_HasConstCache_containsUnsafe(
                        v_declNames_611_,
                        v_type_657_,
                        v_a_613_,
                    );
                    v_fst_661_ = leanh::lean_ctor_get(v___x_660_, 0);
                    leanh::lean_inc(v_fst_661_);
                    v___x_662_ = (leanh::lean_unbox(v_fst_661_) as u8);
                    leanh::lean_dec(v_fst_661_);
                    if v___x_662_ == 0 {
                        v_snd_663_ = leanh::lean_ctor_get(v___x_660_, 1);
                        leanh::lean_inc(v_snd_663_);
                        leanh::lean_dec_ref(v___x_660_);
                        leanh::lean_inc_ref(v_value_658_);
                        v___x_664_ = l_Lean_HasConstCache_containsUnsafe(
                            v_declNames_611_,
                            v_value_658_,
                            v_snd_663_,
                        );
                        v_fst_665_ = leanh::lean_ctor_get(v___x_664_, 0);
                        leanh::lean_inc(v_fst_665_);
                        v___x_666_ = (leanh::lean_unbox(v_fst_665_) as u8);
                        leanh::lean_dec(v_fst_665_);
                        if v___x_666_ == 0 {
                            v_snd_667_ = leanh::lean_ctor_get(v___x_664_, 1);
                            leanh::lean_inc(v_snd_667_);
                            leanh::lean_dec_ref(v___x_664_);
                            leanh::lean_inc_ref(v_body_659_);
                            v___x_668_ = l_Lean_HasConstCache_containsUnsafe(
                                v_declNames_611_,
                                v_body_659_,
                                v_snd_667_,
                            );
                            v___y_615_ = v___x_668_;
                            state = 1;
                            continue;
                        } else {
                            v___y_615_ = v___x_664_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___y_615_ = v___x_660_;
                        state = 1;
                        continue;
                    }
                }
                10 => {
                    v_expr_669_ = leanh::lean_ctor_get(v_e_612_, 1);
                    leanh::lean_inc_ref(v_expr_669_);
                    v___x_670_ = l_Lean_HasConstCache_containsUnsafe(
                        v_declNames_611_,
                        v_expr_669_,
                        v_a_613_,
                    );
                    v_fst_671_ = leanh::lean_ctor_get(v___x_670_, 0);
                    leanh::lean_inc(v_fst_671_);
                    v_snd_672_ = leanh::lean_ctor_get(v___x_670_, 1);
                    leanh::lean_inc(v_snd_672_);
                    leanh::lean_dec_ref(v___x_670_);
                    v___x_673_ = (leanh::lean_unbox(v_fst_671_) as u8);
                    leanh::lean_dec(v_fst_671_);
                    v___x_674_ = l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache___redArg(v_e_612_, v___x_673_, v_snd_672_);
                    return v___x_674_;
                }
                11 => {
                    v_struct_675_ = leanh::lean_ctor_get(v_e_612_, 2);
                    leanh::lean_inc_ref(v_struct_675_);
                    v___x_676_ = l_Lean_HasConstCache_containsUnsafe(
                        v_declNames_611_,
                        v_struct_675_,
                        v_a_613_,
                    );
                    v_fst_677_ = leanh::lean_ctor_get(v___x_676_, 0);
                    leanh::lean_inc(v_fst_677_);
                    v_snd_678_ = leanh::lean_ctor_get(v___x_676_, 1);
                    leanh::lean_inc(v_snd_678_);
                    leanh::lean_dec_ref(v___x_676_);
                    v___x_679_ = (leanh::lean_unbox(v_fst_677_) as u8);
                    leanh::lean_dec(v_fst_677_);
                    v___x_680_ = l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache___redArg(v_e_612_, v___x_679_, v_snd_678_);
                    return v___x_680_;
                }
                _ => {
                    leanh::lean_dec_ref(v_e_612_);
                    v___x_681_ = 0;
                    v___x_682_ = leanh::lean_box((v___x_681_) as usize);
                    v___x_683_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_683_, 0, v___x_682_);
                    leanh::lean_ctor_set(v___x_683_, 1, v_a_613_);
                    return v___x_683_;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_HasConstCache_containsUnsafe___boxed(
    mut v_declNames_691_: *mut leanh::LeanObject,
    mut v_e_692_: *mut leanh::LeanObject,
    mut v_a_693_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_694_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_694_ = l_Lean_HasConstCache_containsUnsafe(v_declNames_691_, v_e_692_, v_a_693_);
    leanh::lean_dec_ref(v_declNames_691_);
    return v_res_694_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1(
    mut v_00_u03b2_695_: *mut leanh::LeanObject,
    mut v_m_696_: *mut leanh::LeanObject,
    mut v_a_697_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_698_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_698_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1___redArg(v_m_696_, v_a_697_);
    return v___x_698_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1___boxed(
    mut v_00_u03b2_699_: *mut leanh::LeanObject,
    mut v_m_700_: *mut leanh::LeanObject,
    mut v_a_701_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_702_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_702_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1(v_00_u03b2_699_, v_m_700_, v_a_701_);
    leanh::lean_dec_ref(v_a_701_);
    leanh::lean_dec_ref(v_m_700_);
    return v_res_702_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1_spec__2(
    mut v_00_u03b2_703_: *mut leanh::LeanObject,
    mut v_a_704_: *mut leanh::LeanObject,
    mut v_x_705_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_706_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_706_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1_spec__2___redArg(v_a_704_, v_x_705_);
    return v___x_706_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1_spec__2___boxed(
    mut v_00_u03b2_707_: *mut leanh::LeanObject,
    mut v_a_708_: *mut leanh::LeanObject,
    mut v_x_709_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_710_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_710_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1_spec__2(v_00_u03b2_707_, v_a_708_, v_x_709_);
    leanh::lean_dec(v_x_709_);
    leanh::lean_dec_ref(v_a_708_);
    return v_res_710_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Util_HasConstCache(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Expr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_HashMap_Raw(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Util_HasConstCache(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Util_HasConstCache(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Expr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Data_HashMap_Raw(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_HasConstCache(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Util_HasConstCache(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Util_HasConstCache(builtin);
}