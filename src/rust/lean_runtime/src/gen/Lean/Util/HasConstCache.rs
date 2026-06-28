// Lean compiler output
// Module: Lean.Util.HasConstCache
// Imports: Lean.Expr Std.Data.HashMap.Raw
use crate::r#gen::Lean::Expr::{
    initialize_Lean_Expr, l_Lean_Expr_hash, runtime_initialize_Lean_Expr,
};
use crate::r#gen::Std::Data::HashMap::Raw::{
    initialize_Std_Data_HashMap_Raw, runtime_initialize_Std_Data_HashMap_Raw,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_of_nat, lean_usize_sub,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_get_size, lean_name_eq, lean_nat_add, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::Util::lean_ptr_addr;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_set,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_tag, lean_unbox, lean_unbox_usize,
    lean_unsigned_to_nat,
};
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__0___redArg(
    mut v_a_356_: *mut LeanObject,
    mut v_x_357_: *mut LeanObject,
) -> u8 {
    let mut v___x_358_: u8 = 0;
    let mut v_key_359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_361_: usize = 0;
    let mut v___x_362_: usize = 0;
    let mut v___x_363_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_357_) == 0 {
                    v___x_358_ = 0;
                    return v___x_358_;
                } else {
                    v_key_359_ = lean_ctor_get(v_x_357_, 0);
                    v_tail_360_ = lean_ctor_get(v_x_357_, 2);
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
    mut v_a_365_: *mut LeanObject,
    mut v_x_366_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_367_: u8 = 0;
    let mut v_r_368_: *mut LeanObject = core::ptr::null_mut();
    v_res_367_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__0___redArg(v_a_365_, v_x_366_);
    lean_dec(v_x_366_);
    lean_dec_ref(v_a_365_);
    v_r_368_ = lean_box((v_res_367_) as usize);
    return v_r_368_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__2___redArg(
    mut v_a_369_: *mut LeanObject,
    mut v_b_370_: *mut LeanObject,
    mut v_x_371_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_377_: u8 = 0;
    let mut v___x_378_: usize = 0;
    let mut v___x_379_: usize = 0;
    let mut v___x_380_: u8 = 0;
    let mut v___x_381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_388_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_371_) == 0 {
                    lean_dec(v_b_370_);
                    lean_dec_ref(v_a_369_);
                    return v_x_371_;
                } else {
                    v_key_372_ = lean_ctor_get(v_x_371_, 0);
                    v_value_373_ = lean_ctor_get(v_x_371_, 1);
                    v_tail_374_ = lean_ctor_get(v_x_371_, 2);
                    v_isSharedCheck_388_ = (!lean_is_exclusive(v_x_371_)) as u8;
                    if v_isSharedCheck_388_ == 0 {
                        v___x_376_ = v_x_371_;
                        v_isShared_377_ = v_isSharedCheck_388_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_374_);
                        lean_inc(v_value_373_);
                        lean_inc(v_key_372_);
                        lean_dec(v_x_371_);
                        v___x_376_ = lean_box(0);
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
                        lean_ctor_set(v___x_376_, 2, v___x_381_);
                        v___x_383_ = v___x_376_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_384_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_384_, 0, v_key_372_);
                        lean_ctor_set(v_reuseFailAlloc_384_, 1, v_value_373_);
                        lean_ctor_set(v_reuseFailAlloc_384_, 2, v___x_381_);
                        v___x_383_ = v_reuseFailAlloc_384_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_value_373_);
                    lean_dec(v_key_372_);
                    if v_isShared_377_ == 0 {
                        lean_ctor_set(v___x_376_, 1, v_b_370_);
                        lean_ctor_set(v___x_376_, 0, v_a_369_);
                        v___x_386_ = v___x_376_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_387_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_387_, 0, v_a_369_);
                        lean_ctor_set(v_reuseFailAlloc_387_, 1, v_b_370_);
                        lean_ctor_set(v_reuseFailAlloc_387_, 2, v_tail_374_);
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
    mut v_x_389_: *mut LeanObject,
    mut v_x_390_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_396_: u8 = 0;
    let mut v___x_397_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_416_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_390_) == 0 {
                    return v_x_389_;
                } else {
                    v_key_391_ = lean_ctor_get(v_x_390_, 0);
                    v_value_392_ = lean_ctor_get(v_x_390_, 1);
                    v_tail_393_ = lean_ctor_get(v_x_390_, 2);
                    v_isSharedCheck_416_ = (!lean_is_exclusive(v_x_390_)) as u8;
                    if v_isSharedCheck_416_ == 0 {
                        v___x_395_ = v_x_390_;
                        v_isShared_396_ = v_isSharedCheck_416_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_393_);
                        lean_inc(v_value_392_);
                        lean_inc(v_key_391_);
                        lean_dec(v_x_390_);
                        v___x_395_ = lean_box(0);
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
                lean_inc(v___x_410_);
                if v_isShared_396_ == 0 {
                    lean_ctor_set(v___x_395_, 2, v___x_410_);
                    v___x_412_ = v___x_395_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_415_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_415_, 0, v_key_391_);
                    lean_ctor_set(v_reuseFailAlloc_415_, 1, v_value_392_);
                    lean_ctor_set(v_reuseFailAlloc_415_, 2, v___x_410_);
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
    mut v_i_417_: *mut LeanObject,
    mut v_source_418_: *mut LeanObject,
    mut v_target_419_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_421_: u8 = 0;
    let mut v_es_422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_427_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_420_ = lean_array_get_size(v_source_418_);
                v___x_421_ = lean_nat_dec_lt(v_i_417_, v___x_420_);
                if v___x_421_ == 0 {
                    lean_dec_ref(v_source_418_);
                    lean_dec(v_i_417_);
                    return v_target_419_;
                } else {
                    v_es_422_ = lean_array_fget(v_source_418_, v_i_417_);
                    v___x_423_ = lean_box(0);
                    v_source_424_ = lean_array_fset(v_source_418_, v_i_417_, v___x_423_);
                    v_target_425_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__1_spec__2_spec__3___redArg(v_target_419_, v_es_422_);
                    v___x_426_ = lean_unsigned_to_nat(1);
                    v___x_427_ = lean_nat_add(v_i_417_, v___x_426_);
                    lean_dec(v_i_417_);
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
    mut v_data_429_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_436_: *mut LeanObject = core::ptr::null_mut();
    v___x_430_ = lean_array_get_size(v_data_429_);
    v___x_431_ = lean_unsigned_to_nat(2);
    v_nbuckets_432_ = lean_nat_mul(v___x_430_, v___x_431_);
    v___x_433_ = lean_unsigned_to_nat(0);
    v___x_434_ = lean_box(0);
    v___x_435_ = lean_mk_array(v_nbuckets_432_, v___x_434_);
    v___x_436_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__1_spec__2___redArg(v___x_433_, v_data_429_, v___x_435_);
    return v___x_436_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0___redArg(
    mut v_m_437_: *mut LeanObject,
    mut v_a_438_: *mut LeanObject,
    mut v_b_439_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_444_: u8 = 0;
    let mut v___x_445_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_459_: u8 = 0;
    let mut v___x_460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_469_: u8 = 0;
    let mut v_val_470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_484_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_440_ = lean_ctor_get(v_m_437_, 0);
                v_buckets_441_ = lean_ctor_get(v_m_437_, 1);
                v_isSharedCheck_484_ = (!lean_is_exclusive(v_m_437_)) as u8;
                if v_isSharedCheck_484_ == 0 {
                    v___x_443_ = v_m_437_;
                    v_isShared_444_ = v_isSharedCheck_484_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_buckets_441_);
                    lean_inc(v_size_440_);
                    lean_dec(v_m_437_);
                    v___x_443_ = lean_box(0);
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
                    v___x_460_ = lean_unsigned_to_nat(1);
                    v_size_x27_461_ = lean_nat_add(v_size_440_, v___x_460_);
                    lean_dec(v_size_440_);
                    lean_inc(v_bkt_458_);
                    v___x_462_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_462_, 0, v_a_438_);
                    lean_ctor_set(v___x_462_, 1, v_b_439_);
                    lean_ctor_set(v___x_462_, 2, v_bkt_458_);
                    v_buckets_x27_463_ = lean_array_uset(v_buckets_441_, v___x_457_, v___x_462_);
                    v___x_464_ = lean_unsigned_to_nat(4);
                    v___x_465_ = lean_nat_mul(v_size_x27_461_, v___x_464_);
                    v___x_466_ = lean_unsigned_to_nat(3);
                    v___x_467_ = lean_nat_div(v___x_465_, v___x_466_);
                    lean_dec(v___x_465_);
                    v___x_468_ = lean_array_get_size(v_buckets_x27_463_);
                    v___x_469_ = lean_nat_dec_le(v___x_467_, v___x_468_);
                    lean_dec(v___x_467_);
                    if v___x_469_ == 0 {
                        v_val_470_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__1___redArg(v_buckets_x27_463_);
                        if v_isShared_444_ == 0 {
                            lean_ctor_set(v___x_443_, 1, v_val_470_);
                            lean_ctor_set(v___x_443_, 0, v_size_x27_461_);
                            v___x_472_ = v___x_443_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_473_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_473_, 0, v_size_x27_461_);
                            lean_ctor_set(v_reuseFailAlloc_473_, 1, v_val_470_);
                            v___x_472_ = v_reuseFailAlloc_473_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_444_ == 0 {
                            lean_ctor_set(v___x_443_, 1, v_buckets_x27_463_);
                            lean_ctor_set(v___x_443_, 0, v_size_x27_461_);
                            v___x_475_ = v___x_443_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_476_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_476_, 0, v_size_x27_461_);
                            lean_ctor_set(v_reuseFailAlloc_476_, 1, v_buckets_x27_463_);
                            v___x_475_ = v_reuseFailAlloc_476_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_inc(v_bkt_458_);
                    v___x_477_ = lean_box(0);
                    v_buckets_x27_478_ = lean_array_uset(v_buckets_441_, v___x_457_, v___x_477_);
                    v___x_479_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__2___redArg(v_a_438_, v_b_439_, v_bkt_458_);
                    v___x_480_ = lean_array_uset(v_buckets_x27_478_, v___x_457_, v___x_479_);
                    if v_isShared_444_ == 0 {
                        lean_ctor_set(v___x_443_, 1, v___x_480_);
                        v___x_482_ = v___x_443_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_483_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_483_, 0, v_size_440_);
                        lean_ctor_set(v_reuseFailAlloc_483_, 1, v___x_480_);
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
    mut v_e_485_: *mut LeanObject,
    mut v_r_486_: u8,
    mut v_a_487_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_491_: u8 = 0;
    v_buckets_488_ = lean_ctor_get(v_a_487_, 1);
    v___x_489_ = lean_unsigned_to_nat(0);
    v___x_490_ = lean_array_get_size(v_buckets_488_);
    v___x_491_ = lean_nat_dec_lt(v___x_489_, v___x_490_);
    if v___x_491_ == 0 {
        let mut v___x_492_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_493_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_e_485_);
        v___x_492_ = lean_box((v_r_486_) as usize);
        v___x_493_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_493_, 0, v___x_492_);
        lean_ctor_set(v___x_493_, 1, v_a_487_);
        return v___x_493_;
    } else {
        let mut v___x_494_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_495_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_496_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_497_: *mut LeanObject = core::ptr::null_mut();
        v___x_494_ = lean_box((v_r_486_) as usize);
        v___x_495_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0___redArg(v_a_487_, v_e_485_, v___x_494_);
        v___x_496_ = lean_box((v_r_486_) as usize);
        v___x_497_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_497_, 0, v___x_496_);
        lean_ctor_set(v___x_497_, 1, v___x_495_);
        return v___x_497_;
    }
}
pub unsafe fn l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache___redArg___boxed(
    mut v_e_498_: *mut LeanObject,
    mut v_r_499_: *mut LeanObject,
    mut v_a_500_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_r_boxed_501_: u8 = 0;
    let mut v_res_502_: *mut LeanObject = core::ptr::null_mut();
    v_r_boxed_501_ = (lean_unbox(v_r_499_) as u8);
    v_res_502_ =
        l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache___redArg(
            v_e_498_,
            v_r_boxed_501_,
            v_a_500_,
        );
    return v_res_502_;
}
pub unsafe fn l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache(
    mut v_declNames_503_: *mut LeanObject,
    mut v_e_504_: *mut LeanObject,
    mut v_r_505_: u8,
    mut v_a_506_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_507_: *mut LeanObject = core::ptr::null_mut();
    v___x_507_ =
        l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache___redArg(
            v_e_504_, v_r_505_, v_a_506_,
        );
    return v___x_507_;
}
pub unsafe fn l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache___boxed(
    mut v_declNames_508_: *mut LeanObject,
    mut v_e_509_: *mut LeanObject,
    mut v_r_510_: *mut LeanObject,
    mut v_a_511_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_r_boxed_512_: u8 = 0;
    let mut v_res_513_: *mut LeanObject = core::ptr::null_mut();
    v_r_boxed_512_ = (lean_unbox(v_r_510_) as u8);
    v_res_513_ = l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache(
        v_declNames_508_,
        v_e_509_,
        v_r_boxed_512_,
        v_a_511_,
    );
    lean_dec_ref(v_declNames_508_);
    return v_res_513_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0(
    mut v_00_u03b2_514_: *mut LeanObject,
    mut v_m_515_: *mut LeanObject,
    mut v_a_516_: *mut LeanObject,
    mut v_b_517_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_518_: *mut LeanObject = core::ptr::null_mut();
    v___x_518_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0___redArg(v_m_515_, v_a_516_, v_b_517_);
    return v___x_518_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__0(
    mut v_00_u03b2_519_: *mut LeanObject,
    mut v_a_520_: *mut LeanObject,
    mut v_x_521_: *mut LeanObject,
) -> u8 {
    let mut v___x_522_: u8 = 0;
    v___x_522_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__0___redArg(v_a_520_, v_x_521_);
    return v___x_522_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__0___boxed(
    mut v_00_u03b2_523_: *mut LeanObject,
    mut v_a_524_: *mut LeanObject,
    mut v_x_525_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_526_: u8 = 0;
    let mut v_r_527_: *mut LeanObject = core::ptr::null_mut();
    v_res_526_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__0(v_00_u03b2_523_, v_a_524_, v_x_525_);
    lean_dec(v_x_525_);
    lean_dec_ref(v_a_524_);
    v_r_527_ = lean_box((v_res_526_) as usize);
    return v_r_527_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__1(
    mut v_00_u03b2_528_: *mut LeanObject,
    mut v_data_529_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_530_: *mut LeanObject = core::ptr::null_mut();
    v___x_530_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__1___redArg(v_data_529_);
    return v___x_530_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__2(
    mut v_00_u03b2_531_: *mut LeanObject,
    mut v_a_532_: *mut LeanObject,
    mut v_b_533_: *mut LeanObject,
    mut v_x_534_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_535_: *mut LeanObject = core::ptr::null_mut();
    v___x_535_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__2___redArg(v_a_532_, v_b_533_, v_x_534_);
    return v___x_535_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__1_spec__2(
    mut v_00_u03b2_536_: *mut LeanObject,
    mut v_i_537_: *mut LeanObject,
    mut v_source_538_: *mut LeanObject,
    mut v_target_539_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_540_: *mut LeanObject = core::ptr::null_mut();
    v___x_540_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__1_spec__2___redArg(v_i_537_, v_source_538_, v_target_539_);
    return v___x_540_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__1_spec__2_spec__3(
    mut v_00_u03b2_541_: *mut LeanObject,
    mut v_x_542_: *mut LeanObject,
    mut v_x_543_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_544_: *mut LeanObject = core::ptr::null_mut();
    v___x_544_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache_spec__0_spec__1_spec__2_spec__3___redArg(v_x_542_, v_x_543_);
    return v___x_544_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1_spec__2___redArg(
    mut v_a_545_: *mut LeanObject,
    mut v_x_546_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_551_: usize = 0;
    let mut v___x_552_: usize = 0;
    let mut v___x_553_: u8 = 0;
    let mut v___x_555_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_546_) == 0 {
                    v___x_547_ = lean_box(0);
                    return v___x_547_;
                } else {
                    v_key_548_ = lean_ctor_get(v_x_546_, 0);
                    v_value_549_ = lean_ctor_get(v_x_546_, 1);
                    v_tail_550_ = lean_ctor_get(v_x_546_, 2);
                    v___x_551_ = lean_ptr_addr(v_key_548_);
                    v___x_552_ = lean_ptr_addr(v_a_545_);
                    v___x_553_ = lean_usize_dec_eq(v___x_551_, v___x_552_);
                    if v___x_553_ == 0 {
                        v_x_546_ = v_tail_550_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_value_549_);
                        v___x_555_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_555_, 0, v_value_549_);
                        return v___x_555_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1_spec__2___redArg___boxed(
    mut v_a_556_: *mut LeanObject,
    mut v_x_557_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_558_: *mut LeanObject = core::ptr::null_mut();
    v_res_558_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1_spec__2___redArg(v_a_556_, v_x_557_);
    lean_dec(v_x_557_);
    lean_dec_ref(v_a_556_);
    return v_res_558_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1___redArg(
    mut v_m_559_: *mut LeanObject,
    mut v_a_560_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_562_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_576_: *mut LeanObject = core::ptr::null_mut();
    v_buckets_561_ = lean_ctor_get(v_m_559_, 1);
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
    mut v_m_577_: *mut LeanObject,
    mut v_a_578_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_579_: *mut LeanObject = core::ptr::null_mut();
    v_res_579_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1___redArg(v_m_577_, v_a_578_);
    lean_dec_ref(v_a_578_);
    lean_dec_ref(v_m_577_);
    return v_res_579_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_HasConstCache_containsUnsafe_spec__0_spec__0(
    mut v_a_580_: *mut LeanObject,
    mut v_as_581_: *mut LeanObject,
    mut v_i_582_: usize,
    mut v_stop_583_: usize,
) -> u8 {
    let mut v___x_584_: u8 = 0;
    let mut v___x_585_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_591_: *mut LeanObject,
    mut v_as_592_: *mut LeanObject,
    mut v_i_593_: *mut LeanObject,
    mut v_stop_594_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_595_: usize = 0;
    let mut v_stop_boxed_596_: usize = 0;
    let mut v_res_597_: u8 = 0;
    let mut v_r_598_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_595_ = lean_unbox_usize(v_i_593_);
    lean_dec(v_i_593_);
    v_stop_boxed_596_ = lean_unbox_usize(v_stop_594_);
    lean_dec(v_stop_594_);
    v_res_597_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_HasConstCache_containsUnsafe_spec__0_spec__0(v_a_591_, v_as_592_, v_i_boxed_595_, v_stop_boxed_596_);
    lean_dec_ref(v_as_592_);
    lean_dec(v_a_591_);
    v_r_598_ = lean_box((v_res_597_) as usize);
    return v_r_598_;
}
pub unsafe fn l_Array_contains___at___00Lean_HasConstCache_containsUnsafe_spec__0(
    mut v_as_599_: *mut LeanObject,
    mut v_a_600_: *mut LeanObject,
) -> u8 {
    let mut v___x_601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_603_: u8 = 0;
    v___x_601_ = lean_unsigned_to_nat(0);
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
    mut v_as_607_: *mut LeanObject,
    mut v_a_608_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_609_: u8 = 0;
    let mut v_r_610_: *mut LeanObject = core::ptr::null_mut();
    v_res_609_ =
        l_Array_contains___at___00Lean_HasConstCache_containsUnsafe_spec__0(v_as_607_, v_a_608_);
    lean_dec(v_a_608_);
    lean_dec_ref(v_as_607_);
    v_r_610_ = lean_box((v_res_609_) as usize);
    return v_r_610_;
}
pub unsafe fn l_Lean_HasConstCache_containsUnsafe(
    mut v_declNames_611_: *mut LeanObject,
    mut v_e_612_: *mut LeanObject,
    mut v_a_613_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_618_: u8 = 0;
    let mut v___x_619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_624_: u8 = 0;
    let mut v___x_625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_630_: u8 = 0;
    let mut v___x_631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_d_633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_638_: u8 = 0;
    let mut v_snd_639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_643_: u8 = 0;
    let mut v___x_644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_650_: u8 = 0;
    let mut v_snd_651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_662_: u8 = 0;
    let mut v_snd_663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_666_: u8 = 0;
    let mut v_snd_667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_673_: u8 = 0;
    let mut v___x_674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_struct_675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_679_: u8 = 0;
    let mut v___x_680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_681_: u8 = 0;
    let mut v___x_682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_687_: u8 = 0;
    let mut v___x_688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_690_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_684_ = lean_ctor_get(v_a_613_, 1);
                v___x_685_ = lean_unsigned_to_nat(0);
                v___x_686_ = lean_array_get_size(v_buckets_684_);
                v___x_687_ = lean_nat_dec_lt(v___x_685_, v___x_686_);
                if v___x_687_ == 0 {
                    state = 5;
                    continue;
                } else {
                    v___x_688_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1___redArg(v_a_613_, v_e_612_);
                    if lean_obj_tag(v___x_688_) == 1 {
                        lean_dec_ref(v_e_612_);
                        v_val_689_ = lean_ctor_get(v___x_688_, 0);
                        lean_inc(v_val_689_);
                        lean_dec_ref_known(v___x_688_, 1);
                        v___x_690_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_690_, 0, v_val_689_);
                        lean_ctor_set(v___x_690_, 1, v_a_613_);
                        return v___x_690_;
                    } else {
                        lean_dec(v___x_688_);
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_616_ = lean_ctor_get(v___y_615_, 0);
                lean_inc(v_fst_616_);
                v_snd_617_ = lean_ctor_get(v___y_615_, 1);
                lean_inc(v_snd_617_);
                lean_dec_ref(v___y_615_);
                v___x_618_ = (lean_unbox(v_fst_616_) as u8);
                lean_dec(v_fst_616_);
                v___x_619_ = l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache___redArg(v_e_612_, v___x_618_, v_snd_617_);
                return v___x_619_;
            }
            2 => {
                v_fst_622_ = lean_ctor_get(v___y_621_, 0);
                lean_inc(v_fst_622_);
                v_snd_623_ = lean_ctor_get(v___y_621_, 1);
                lean_inc(v_snd_623_);
                lean_dec_ref(v___y_621_);
                v___x_624_ = (lean_unbox(v_fst_622_) as u8);
                lean_dec(v_fst_622_);
                v___x_625_ = l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache___redArg(v_e_612_, v___x_624_, v_snd_623_);
                return v___x_625_;
            }
            3 => {
                v_fst_628_ = lean_ctor_get(v___y_627_, 0);
                lean_inc(v_fst_628_);
                v_snd_629_ = lean_ctor_get(v___y_627_, 1);
                lean_inc(v_snd_629_);
                lean_dec_ref(v___y_627_);
                v___x_630_ = (lean_unbox(v_fst_628_) as u8);
                lean_dec(v_fst_628_);
                v___x_631_ = l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache___redArg(v_e_612_, v___x_630_, v_snd_629_);
                return v___x_631_;
            }
            4 => {
                v___x_636_ =
                    l_Lean_HasConstCache_containsUnsafe(v_declNames_611_, v_d_633_, v___y_635_);
                v_fst_637_ = lean_ctor_get(v___x_636_, 0);
                lean_inc(v_fst_637_);
                v___x_638_ = (lean_unbox(v_fst_637_) as u8);
                lean_dec(v_fst_637_);
                if v___x_638_ == 0 {
                    v_snd_639_ = lean_ctor_get(v___x_636_, 1);
                    lean_inc(v_snd_639_);
                    lean_dec_ref(v___x_636_);
                    v___x_640_ =
                        l_Lean_HasConstCache_containsUnsafe(v_declNames_611_, v_b_634_, v_snd_639_);
                    v___y_627_ = v___x_640_;
                    state = 3;
                    continue;
                } else {
                    lean_dec_ref(v_b_634_);
                    v___y_627_ = v___x_636_;
                    state = 3;
                    continue;
                }
            }
            5 => match lean_obj_tag(v_e_612_) {
                4 => {
                    v_declName_642_ = lean_ctor_get(v_e_612_, 0);
                    lean_inc(v_declName_642_);
                    lean_dec_ref_known(v_e_612_, 2);
                    v___x_643_ =
                        l_Array_contains___at___00Lean_HasConstCache_containsUnsafe_spec__0(
                            v_declNames_611_,
                            v_declName_642_,
                        );
                    lean_dec(v_declName_642_);
                    v___x_644_ = lean_box((v___x_643_) as usize);
                    v___x_645_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_645_, 0, v___x_644_);
                    lean_ctor_set(v___x_645_, 1, v_a_613_);
                    return v___x_645_;
                }
                5 => {
                    v_fn_646_ = lean_ctor_get(v_e_612_, 0);
                    v_arg_647_ = lean_ctor_get(v_e_612_, 1);
                    lean_inc_ref(v_fn_646_);
                    v___x_648_ =
                        l_Lean_HasConstCache_containsUnsafe(v_declNames_611_, v_fn_646_, v_a_613_);
                    v_fst_649_ = lean_ctor_get(v___x_648_, 0);
                    lean_inc(v_fst_649_);
                    v___x_650_ = (lean_unbox(v_fst_649_) as u8);
                    lean_dec(v_fst_649_);
                    if v___x_650_ == 0 {
                        v_snd_651_ = lean_ctor_get(v___x_648_, 1);
                        lean_inc(v_snd_651_);
                        lean_dec_ref(v___x_648_);
                        lean_inc_ref(v_arg_647_);
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
                    v_binderType_653_ = lean_ctor_get(v_e_612_, 1);
                    v_body_654_ = lean_ctor_get(v_e_612_, 2);
                    lean_inc_ref(v_body_654_);
                    lean_inc_ref(v_binderType_653_);
                    v_d_633_ = v_binderType_653_;
                    v_b_634_ = v_body_654_;
                    v___y_635_ = v_a_613_;
                    state = 4;
                    continue;
                }
                7 => {
                    v_binderType_655_ = lean_ctor_get(v_e_612_, 1);
                    v_body_656_ = lean_ctor_get(v_e_612_, 2);
                    lean_inc_ref(v_body_656_);
                    lean_inc_ref(v_binderType_655_);
                    v_d_633_ = v_binderType_655_;
                    v_b_634_ = v_body_656_;
                    v___y_635_ = v_a_613_;
                    state = 4;
                    continue;
                }
                8 => {
                    v_type_657_ = lean_ctor_get(v_e_612_, 1);
                    v_value_658_ = lean_ctor_get(v_e_612_, 2);
                    v_body_659_ = lean_ctor_get(v_e_612_, 3);
                    lean_inc_ref(v_type_657_);
                    v___x_660_ = l_Lean_HasConstCache_containsUnsafe(
                        v_declNames_611_,
                        v_type_657_,
                        v_a_613_,
                    );
                    v_fst_661_ = lean_ctor_get(v___x_660_, 0);
                    lean_inc(v_fst_661_);
                    v___x_662_ = (lean_unbox(v_fst_661_) as u8);
                    lean_dec(v_fst_661_);
                    if v___x_662_ == 0 {
                        v_snd_663_ = lean_ctor_get(v___x_660_, 1);
                        lean_inc(v_snd_663_);
                        lean_dec_ref(v___x_660_);
                        lean_inc_ref(v_value_658_);
                        v___x_664_ = l_Lean_HasConstCache_containsUnsafe(
                            v_declNames_611_,
                            v_value_658_,
                            v_snd_663_,
                        );
                        v_fst_665_ = lean_ctor_get(v___x_664_, 0);
                        lean_inc(v_fst_665_);
                        v___x_666_ = (lean_unbox(v_fst_665_) as u8);
                        lean_dec(v_fst_665_);
                        if v___x_666_ == 0 {
                            v_snd_667_ = lean_ctor_get(v___x_664_, 1);
                            lean_inc(v_snd_667_);
                            lean_dec_ref(v___x_664_);
                            lean_inc_ref(v_body_659_);
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
                    v_expr_669_ = lean_ctor_get(v_e_612_, 1);
                    lean_inc_ref(v_expr_669_);
                    v___x_670_ = l_Lean_HasConstCache_containsUnsafe(
                        v_declNames_611_,
                        v_expr_669_,
                        v_a_613_,
                    );
                    v_fst_671_ = lean_ctor_get(v___x_670_, 0);
                    lean_inc(v_fst_671_);
                    v_snd_672_ = lean_ctor_get(v___x_670_, 1);
                    lean_inc(v_snd_672_);
                    lean_dec_ref(v___x_670_);
                    v___x_673_ = (lean_unbox(v_fst_671_) as u8);
                    lean_dec(v_fst_671_);
                    v___x_674_ = l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache___redArg(v_e_612_, v___x_673_, v_snd_672_);
                    return v___x_674_;
                }
                11 => {
                    v_struct_675_ = lean_ctor_get(v_e_612_, 2);
                    lean_inc_ref(v_struct_675_);
                    v___x_676_ = l_Lean_HasConstCache_containsUnsafe(
                        v_declNames_611_,
                        v_struct_675_,
                        v_a_613_,
                    );
                    v_fst_677_ = lean_ctor_get(v___x_676_, 0);
                    lean_inc(v_fst_677_);
                    v_snd_678_ = lean_ctor_get(v___x_676_, 1);
                    lean_inc(v_snd_678_);
                    lean_dec_ref(v___x_676_);
                    v___x_679_ = (lean_unbox(v_fst_677_) as u8);
                    lean_dec(v_fst_677_);
                    v___x_680_ = l___private_Lean_Util_HasConstCache_0__Lean_HasConstCache_containsUnsafe_cache___redArg(v_e_612_, v___x_679_, v_snd_678_);
                    return v___x_680_;
                }
                _ => {
                    lean_dec_ref(v_e_612_);
                    v___x_681_ = 0;
                    v___x_682_ = lean_box((v___x_681_) as usize);
                    v___x_683_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_683_, 0, v___x_682_);
                    lean_ctor_set(v___x_683_, 1, v_a_613_);
                    return v___x_683_;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_HasConstCache_containsUnsafe___boxed(
    mut v_declNames_691_: *mut LeanObject,
    mut v_e_692_: *mut LeanObject,
    mut v_a_693_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_694_: *mut LeanObject = core::ptr::null_mut();
    v_res_694_ = l_Lean_HasConstCache_containsUnsafe(v_declNames_691_, v_e_692_, v_a_693_);
    lean_dec_ref(v_declNames_691_);
    return v_res_694_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1(
    mut v_00_u03b2_695_: *mut LeanObject,
    mut v_m_696_: *mut LeanObject,
    mut v_a_697_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_698_: *mut LeanObject = core::ptr::null_mut();
    v___x_698_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1___redArg(v_m_696_, v_a_697_);
    return v___x_698_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1___boxed(
    mut v_00_u03b2_699_: *mut LeanObject,
    mut v_m_700_: *mut LeanObject,
    mut v_a_701_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_702_: *mut LeanObject = core::ptr::null_mut();
    v_res_702_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1(v_00_u03b2_699_, v_m_700_, v_a_701_);
    lean_dec_ref(v_a_701_);
    lean_dec_ref(v_m_700_);
    return v_res_702_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1_spec__2(
    mut v_00_u03b2_703_: *mut LeanObject,
    mut v_a_704_: *mut LeanObject,
    mut v_x_705_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_706_: *mut LeanObject = core::ptr::null_mut();
    v___x_706_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1_spec__2___redArg(v_a_704_, v_x_705_);
    return v___x_706_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1_spec__2___boxed(
    mut v_00_u03b2_707_: *mut LeanObject,
    mut v_a_708_: *mut LeanObject,
    mut v_x_709_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_710_: *mut LeanObject = core::ptr::null_mut();
    v_res_710_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_HasConstCache_containsUnsafe_spec__1_spec__2(v_00_u03b2_707_, v_a_708_, v_x_709_);
    lean_dec(v_x_709_);
    lean_dec_ref(v_a_708_);
    return v_res_710_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Util_HasConstCache(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Expr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_HashMap_Raw(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Util_HasConstCache(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Util_HasConstCache(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Expr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Data_HashMap_Raw(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_HasConstCache(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Util_HasConstCache(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Util_HasConstCache(builtin);
}
