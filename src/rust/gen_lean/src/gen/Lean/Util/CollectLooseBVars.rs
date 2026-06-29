// Lean compiler output
// Module: Lean.Util.CollectLooseBVars
// Imports: Lean.Expr
use crate::r#gen::Lean::Expr::{
    initialize_Lean_Expr, l_Lean_Expr_hasLooseBVars, l_Lean_Expr_hash, l_Lean_Expr_looseBVarRange,
    runtime_initialize_Lean_Expr,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_uint64_of_nat, lean_usize_of_nat, lean_usize_sub,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_get_size, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_sub, lean_uint64_mix_hash,
};
use crate::lean_imports_rs::Lean::Expr::lean_expr_eqv;
static mut l_Lean_Expr_collectLooseBVars___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Expr_collectLooseBVars___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Expr_collectLooseBVars___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Expr_collectLooseBVars___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Expr_collectLooseBVars___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Expr_collectLooseBVars___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Expr_collectLooseBVars___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Expr_collectLooseBVars___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Expr_collectLooseBVars___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Expr_collectLooseBVars___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0_spec__0___redArg(
    mut v_a_391_: *mut crate::leanh::LeanObject,
    mut v_x_392_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_393_: u8 = 0;
    let mut v_key_394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_397_: u8 = 0;
    let mut v_fst_399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_403_: u8 = 0;
    let mut v___x_404_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_392_) == 0 {
                    v___x_393_ = 0;
                    return v___x_393_;
                } else {
                    v_key_394_ = crate::leanh::lean_ctor_get(v_x_392_, 0);
                    v_tail_395_ = crate::leanh::lean_ctor_get(v_x_392_, 2);
                    v_fst_399_ = crate::leanh::lean_ctor_get(v_key_394_, 0);
                    v_snd_400_ = crate::leanh::lean_ctor_get(v_key_394_, 1);
                    v_fst_401_ = crate::leanh::lean_ctor_get(v_a_391_, 0);
                    v_snd_402_ = crate::leanh::lean_ctor_get(v_a_391_, 1);
                    v___x_403_ = lean_nat_dec_eq(v_fst_399_, v_fst_401_);
                    if v___x_403_ == 0 {
                        v___y_397_ = v___x_403_;
                        state = 1;
                        continue;
                    } else {
                        v___x_404_ = lean_expr_eqv(v_snd_400_, v_snd_402_);
                        v___y_397_ = v___x_404_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_397_ == 0 {
                    v_x_392_ = v_tail_395_;
                    state = 0;
                    continue;
                } else {
                    return v___y_397_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0_spec__0___redArg___boxed(
    mut v_a_405_: *mut crate::leanh::LeanObject,
    mut v_x_406_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_407_: u8 = 0;
    let mut v_r_408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_407_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0_spec__0___redArg(v_a_405_, v_x_406_);
    crate::leanh::lean_dec(v_x_406_);
    crate::leanh::lean_dec_ref(v_a_405_);
    v_r_408_ = crate::leanh::lean_box((v_res_407_) as usize);
    return v_r_408_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0___redArg(
    mut v_m_409_: *mut crate::leanh::LeanObject,
    mut v_a_410_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_buckets_411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_415_: u64 = 0;
    let mut v___x_416_: u64 = 0;
    let mut v___x_417_: u64 = 0;
    let mut v___x_418_: u64 = 0;
    let mut v___x_419_: u64 = 0;
    let mut v_fold_420_: u64 = 0;
    let mut v___x_421_: u64 = 0;
    let mut v___x_422_: u64 = 0;
    let mut v___x_423_: u64 = 0;
    let mut v___x_424_: usize = 0;
    let mut v___x_425_: usize = 0;
    let mut v___x_426_: usize = 0;
    let mut v___x_427_: usize = 0;
    let mut v___x_428_: usize = 0;
    let mut v___x_429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_430_: u8 = 0;
    v_buckets_411_ = crate::leanh::lean_ctor_get(v_m_409_, 1);
    v_fst_412_ = crate::leanh::lean_ctor_get(v_a_410_, 0);
    v_snd_413_ = crate::leanh::lean_ctor_get(v_a_410_, 1);
    v___x_414_ = lean_array_get_size(v_buckets_411_);
    v___x_415_ = lean_uint64_of_nat(v_fst_412_);
    v___x_416_ = l_Lean_Expr_hash(v_snd_413_);
    v___x_417_ = lean_uint64_mix_hash(v___x_415_, v___x_416_);
    v___x_418_ = 32u64;
    v___x_419_ = lean_uint64_shift_right(v___x_417_, v___x_418_);
    v_fold_420_ = lean_uint64_xor(v___x_417_, v___x_419_);
    v___x_421_ = 16u64;
    v___x_422_ = lean_uint64_shift_right(v_fold_420_, v___x_421_);
    v___x_423_ = lean_uint64_xor(v_fold_420_, v___x_422_);
    v___x_424_ = lean_uint64_to_usize(v___x_423_);
    v___x_425_ = lean_usize_of_nat(v___x_414_);
    v___x_426_ = 1usize;
    v___x_427_ = lean_usize_sub(v___x_425_, v___x_426_);
    v___x_428_ = lean_usize_land(v___x_424_, v___x_427_);
    v___x_429_ = lean_array_uget_borrowed(v_buckets_411_, v___x_428_);
    v___x_430_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0_spec__0___redArg(v_a_410_, v___x_429_);
    return v___x_430_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0___redArg___boxed(
    mut v_m_431_: *mut crate::leanh::LeanObject,
    mut v_a_432_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_433_: u8 = 0;
    let mut v_r_434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_433_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0___redArg(v_m_431_, v_a_432_);
    crate::leanh::lean_dec_ref(v_a_432_);
    crate::leanh::lean_dec_ref(v_m_431_);
    v_r_434_ = crate::leanh::lean_box((v_res_433_) as usize);
    return v_r_434_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2_spec__3_spec__5___redArg(
    mut v_x_435_: *mut crate::leanh::LeanObject,
    mut v_x_436_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_442_: u8 = 0;
    let mut v_fst_443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_446_: u64 = 0;
    let mut v___x_447_: u64 = 0;
    let mut v___x_448_: u64 = 0;
    let mut v___x_449_: u64 = 0;
    let mut v___x_450_: u64 = 0;
    let mut v_fold_451_: u64 = 0;
    let mut v___x_452_: u64 = 0;
    let mut v___x_453_: u64 = 0;
    let mut v___x_454_: u64 = 0;
    let mut v___x_455_: usize = 0;
    let mut v___x_456_: usize = 0;
    let mut v___x_457_: usize = 0;
    let mut v___x_458_: usize = 0;
    let mut v___x_459_: usize = 0;
    let mut v___x_460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_466_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_436_) == 0 {
                    return v_x_435_;
                } else {
                    v_key_437_ = crate::leanh::lean_ctor_get(v_x_436_, 0);
                    v_value_438_ = crate::leanh::lean_ctor_get(v_x_436_, 1);
                    v_tail_439_ = crate::leanh::lean_ctor_get(v_x_436_, 2);
                    v_isSharedCheck_466_ = (!crate::leanh::lean_is_exclusive(v_x_436_)) as u8;
                    if v_isSharedCheck_466_ == 0 {
                        v___x_441_ = v_x_436_;
                        v_isShared_442_ = v_isSharedCheck_466_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_439_);
                        crate::leanh::lean_inc(v_value_438_);
                        crate::leanh::lean_inc(v_key_437_);
                        crate::leanh::lean_dec(v_x_436_);
                        v___x_441_ = crate::leanh::lean_box(0);
                        v_isShared_442_ = v_isSharedCheck_466_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_443_ = crate::leanh::lean_ctor_get(v_key_437_, 0);
                v_snd_444_ = crate::leanh::lean_ctor_get(v_key_437_, 1);
                v___x_445_ = lean_array_get_size(v_x_435_);
                v___x_446_ = lean_uint64_of_nat(v_fst_443_);
                v___x_447_ = l_Lean_Expr_hash(v_snd_444_);
                v___x_448_ = lean_uint64_mix_hash(v___x_446_, v___x_447_);
                v___x_449_ = 32u64;
                v___x_450_ = lean_uint64_shift_right(v___x_448_, v___x_449_);
                v_fold_451_ = lean_uint64_xor(v___x_448_, v___x_450_);
                v___x_452_ = 16u64;
                v___x_453_ = lean_uint64_shift_right(v_fold_451_, v___x_452_);
                v___x_454_ = lean_uint64_xor(v_fold_451_, v___x_453_);
                v___x_455_ = lean_uint64_to_usize(v___x_454_);
                v___x_456_ = lean_usize_of_nat(v___x_445_);
                v___x_457_ = 1usize;
                v___x_458_ = lean_usize_sub(v___x_456_, v___x_457_);
                v___x_459_ = lean_usize_land(v___x_455_, v___x_458_);
                v___x_460_ = lean_array_uget_borrowed(v_x_435_, v___x_459_);
                crate::leanh::lean_inc(v___x_460_);
                if v_isShared_442_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_441_, 2, v___x_460_);
                    v___x_462_ = v___x_441_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_465_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_465_, 0, v_key_437_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_465_, 1, v_value_438_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_465_, 2, v___x_460_);
                    v___x_462_ = v_reuseFailAlloc_465_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_463_ = lean_array_uset(v_x_435_, v___x_459_, v___x_462_);
                v_x_435_ = v___x_463_;
                v_x_436_ = v_tail_439_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2_spec__3___redArg(
    mut v_i_467_: *mut crate::leanh::LeanObject,
    mut v_source_468_: *mut crate::leanh::LeanObject,
    mut v_target_469_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_471_: u8 = 0;
    let mut v_es_472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_470_ = lean_array_get_size(v_source_468_);
                v___x_471_ = lean_nat_dec_lt(v_i_467_, v___x_470_);
                if v___x_471_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_468_);
                    crate::leanh::lean_dec(v_i_467_);
                    return v_target_469_;
                } else {
                    v_es_472_ = lean_array_fget(v_source_468_, v_i_467_);
                    v___x_473_ = crate::leanh::lean_box(0);
                    v_source_474_ = lean_array_fset(v_source_468_, v_i_467_, v___x_473_);
                    v_target_475_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2_spec__3_spec__5___redArg(v_target_469_, v_es_472_);
                    v___x_476_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_477_ = lean_nat_add(v_i_467_, v___x_476_);
                    crate::leanh::lean_dec(v_i_467_);
                    v_i_467_ = v___x_477_;
                    v_source_468_ = v_source_474_;
                    v_target_469_ = v_target_475_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2___redArg(
    mut v_data_479_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_480_ = lean_array_get_size(v_data_479_);
    v___x_481_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_482_ = lean_nat_mul(v___x_480_, v___x_481_);
    v___x_483_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_484_ = crate::leanh::lean_box(0);
    v___x_485_ = lean_mk_array(v_nbuckets_482_, v___x_484_);
    v___x_486_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2_spec__3___redArg(v___x_483_, v_data_479_, v___x_485_);
    return v___x_486_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1___redArg(
    mut v_m_487_: *mut crate::leanh::LeanObject,
    mut v_a_488_: *mut crate::leanh::LeanObject,
    mut v_b_489_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_495_: u64 = 0;
    let mut v___x_496_: u64 = 0;
    let mut v___x_497_: u64 = 0;
    let mut v___x_498_: u64 = 0;
    let mut v___x_499_: u64 = 0;
    let mut v_fold_500_: u64 = 0;
    let mut v___x_501_: u64 = 0;
    let mut v___x_502_: u64 = 0;
    let mut v___x_503_: u64 = 0;
    let mut v___x_504_: usize = 0;
    let mut v___x_505_: usize = 0;
    let mut v___x_506_: usize = 0;
    let mut v___x_507_: usize = 0;
    let mut v___x_508_: usize = 0;
    let mut v_bkt_509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_510_: u8 = 0;
    let mut v___x_512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_513_: u8 = 0;
    let mut v___x_514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_523_: u8 = 0;
    let mut v_val_524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_531_: u8 = 0;
    let mut v_unused_532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_490_ = crate::leanh::lean_ctor_get(v_m_487_, 0);
                v_buckets_491_ = crate::leanh::lean_ctor_get(v_m_487_, 1);
                v_fst_492_ = crate::leanh::lean_ctor_get(v_a_488_, 0);
                v_snd_493_ = crate::leanh::lean_ctor_get(v_a_488_, 1);
                v___x_494_ = lean_array_get_size(v_buckets_491_);
                v___x_495_ = lean_uint64_of_nat(v_fst_492_);
                v___x_496_ = l_Lean_Expr_hash(v_snd_493_);
                v___x_497_ = lean_uint64_mix_hash(v___x_495_, v___x_496_);
                v___x_498_ = 32u64;
                v___x_499_ = lean_uint64_shift_right(v___x_497_, v___x_498_);
                v_fold_500_ = lean_uint64_xor(v___x_497_, v___x_499_);
                v___x_501_ = 16u64;
                v___x_502_ = lean_uint64_shift_right(v_fold_500_, v___x_501_);
                v___x_503_ = lean_uint64_xor(v_fold_500_, v___x_502_);
                v___x_504_ = lean_uint64_to_usize(v___x_503_);
                v___x_505_ = lean_usize_of_nat(v___x_494_);
                v___x_506_ = 1usize;
                v___x_507_ = lean_usize_sub(v___x_505_, v___x_506_);
                v___x_508_ = lean_usize_land(v___x_504_, v___x_507_);
                v_bkt_509_ = lean_array_uget_borrowed(v_buckets_491_, v___x_508_);
                v___x_510_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0_spec__0___redArg(v_a_488_, v_bkt_509_);
                if v___x_510_ == 0 {
                    crate::leanh::lean_inc_ref(v_buckets_491_);
                    crate::leanh::lean_inc(v_size_490_);
                    v_isSharedCheck_531_ = (!crate::leanh::lean_is_exclusive(v_m_487_)) as u8;
                    if v_isSharedCheck_531_ == 0 {
                        v_unused_532_ = crate::leanh::lean_ctor_get(v_m_487_, 1);
                        crate::leanh::lean_dec(v_unused_532_);
                        v_unused_533_ = crate::leanh::lean_ctor_get(v_m_487_, 0);
                        crate::leanh::lean_dec(v_unused_533_);
                        v___x_512_ = v_m_487_;
                        v_isShared_513_ = v_isSharedCheck_531_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_487_);
                        v___x_512_ = crate::leanh::lean_box(0);
                        v_isShared_513_ = v_isSharedCheck_531_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_b_489_);
                    crate::leanh::lean_dec_ref(v_a_488_);
                    return v_m_487_;
                }
            }
            1 => {
                v___x_514_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_515_ = lean_nat_add(v_size_490_, v___x_514_);
                crate::leanh::lean_dec(v_size_490_);
                crate::leanh::lean_inc(v_bkt_509_);
                v___x_516_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_516_, 0, v_a_488_);
                crate::leanh::lean_ctor_set(v___x_516_, 1, v_b_489_);
                crate::leanh::lean_ctor_set(v___x_516_, 2, v_bkt_509_);
                v_buckets_x27_517_ = lean_array_uset(v_buckets_491_, v___x_508_, v___x_516_);
                v___x_518_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_519_ = lean_nat_mul(v_size_x27_515_, v___x_518_);
                v___x_520_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_521_ = lean_nat_div(v___x_519_, v___x_520_);
                crate::leanh::lean_dec(v___x_519_);
                v___x_522_ = lean_array_get_size(v_buckets_x27_517_);
                v___x_523_ = lean_nat_dec_le(v___x_521_, v___x_522_);
                crate::leanh::lean_dec(v___x_521_);
                if v___x_523_ == 0 {
                    v_val_524_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2___redArg(v_buckets_x27_517_);
                    if v_isShared_513_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_512_, 1, v_val_524_);
                        crate::leanh::lean_ctor_set(v___x_512_, 0, v_size_x27_515_);
                        v___x_526_ = v___x_512_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_527_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_527_, 0, v_size_x27_515_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_527_, 1, v_val_524_);
                        v___x_526_ = v_reuseFailAlloc_527_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_513_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_512_, 1, v_buckets_x27_517_);
                        crate::leanh::lean_ctor_set(v___x_512_, 0, v_size_x27_515_);
                        v___x_529_ = v___x_512_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_530_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_530_, 0, v_size_x27_515_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_530_, 1, v_buckets_x27_517_);
                        v___x_529_ = v_reuseFailAlloc_530_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_526_;
            }
            3 => {
                return v___x_529_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__5_spec__7_spec__9___redArg(
    mut v_x_534_: *mut crate::leanh::LeanObject,
    mut v_x_535_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_541_: u8 = 0;
    let mut v___x_542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_543_: u64 = 0;
    let mut v___x_544_: u64 = 0;
    let mut v___x_545_: u64 = 0;
    let mut v_fold_546_: u64 = 0;
    let mut v___x_547_: u64 = 0;
    let mut v___x_548_: u64 = 0;
    let mut v___x_549_: u64 = 0;
    let mut v___x_550_: usize = 0;
    let mut v___x_551_: usize = 0;
    let mut v___x_552_: usize = 0;
    let mut v___x_553_: usize = 0;
    let mut v___x_554_: usize = 0;
    let mut v___x_555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_561_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_535_) == 0 {
                    return v_x_534_;
                } else {
                    v_key_536_ = crate::leanh::lean_ctor_get(v_x_535_, 0);
                    v_value_537_ = crate::leanh::lean_ctor_get(v_x_535_, 1);
                    v_tail_538_ = crate::leanh::lean_ctor_get(v_x_535_, 2);
                    v_isSharedCheck_561_ = (!crate::leanh::lean_is_exclusive(v_x_535_)) as u8;
                    if v_isSharedCheck_561_ == 0 {
                        v___x_540_ = v_x_535_;
                        v_isShared_541_ = v_isSharedCheck_561_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_538_);
                        crate::leanh::lean_inc(v_value_537_);
                        crate::leanh::lean_inc(v_key_536_);
                        crate::leanh::lean_dec(v_x_535_);
                        v___x_540_ = crate::leanh::lean_box(0);
                        v_isShared_541_ = v_isSharedCheck_561_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_542_ = lean_array_get_size(v_x_534_);
                v___x_543_ = lean_uint64_of_nat(v_key_536_);
                v___x_544_ = 32u64;
                v___x_545_ = lean_uint64_shift_right(v___x_543_, v___x_544_);
                v_fold_546_ = lean_uint64_xor(v___x_543_, v___x_545_);
                v___x_547_ = 16u64;
                v___x_548_ = lean_uint64_shift_right(v_fold_546_, v___x_547_);
                v___x_549_ = lean_uint64_xor(v_fold_546_, v___x_548_);
                v___x_550_ = lean_uint64_to_usize(v___x_549_);
                v___x_551_ = lean_usize_of_nat(v___x_542_);
                v___x_552_ = 1usize;
                v___x_553_ = lean_usize_sub(v___x_551_, v___x_552_);
                v___x_554_ = lean_usize_land(v___x_550_, v___x_553_);
                v___x_555_ = lean_array_uget_borrowed(v_x_534_, v___x_554_);
                crate::leanh::lean_inc(v___x_555_);
                if v_isShared_541_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_540_, 2, v___x_555_);
                    v___x_557_ = v___x_540_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_560_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_560_, 0, v_key_536_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_560_, 1, v_value_537_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_560_, 2, v___x_555_);
                    v___x_557_ = v_reuseFailAlloc_560_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_558_ = lean_array_uset(v_x_534_, v___x_554_, v___x_557_);
                v_x_534_ = v___x_558_;
                v_x_535_ = v_tail_538_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__5_spec__7___redArg(
    mut v_i_562_: *mut crate::leanh::LeanObject,
    mut v_source_563_: *mut crate::leanh::LeanObject,
    mut v_target_564_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_566_: u8 = 0;
    let mut v_es_567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_565_ = lean_array_get_size(v_source_563_);
                v___x_566_ = lean_nat_dec_lt(v_i_562_, v___x_565_);
                if v___x_566_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_563_);
                    crate::leanh::lean_dec(v_i_562_);
                    return v_target_564_;
                } else {
                    v_es_567_ = lean_array_fget(v_source_563_, v_i_562_);
                    v___x_568_ = crate::leanh::lean_box(0);
                    v_source_569_ = lean_array_fset(v_source_563_, v_i_562_, v___x_568_);
                    v_target_570_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__5_spec__7_spec__9___redArg(v_target_564_, v_es_567_);
                    v___x_571_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_572_ = lean_nat_add(v_i_562_, v___x_571_);
                    crate::leanh::lean_dec(v_i_562_);
                    v_i_562_ = v___x_572_;
                    v_source_563_ = v_source_569_;
                    v_target_564_ = v_target_570_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__5___redArg(
    mut v_data_574_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_575_ = lean_array_get_size(v_data_574_);
    v___x_576_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_577_ = lean_nat_mul(v___x_575_, v___x_576_);
    v___x_578_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_579_ = crate::leanh::lean_box(0);
    v___x_580_ = lean_mk_array(v_nbuckets_577_, v___x_579_);
    v___x_581_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__5_spec__7___redArg(v___x_578_, v_data_574_, v___x_580_);
    return v___x_581_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__4___redArg(
    mut v_a_582_: *mut crate::leanh::LeanObject,
    mut v_x_583_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_584_: u8 = 0;
    let mut v_key_585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_587_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_583_) == 0 {
                    v___x_584_ = 0;
                    return v___x_584_;
                } else {
                    v_key_585_ = crate::leanh::lean_ctor_get(v_x_583_, 0);
                    v_tail_586_ = crate::leanh::lean_ctor_get(v_x_583_, 2);
                    v___x_587_ = lean_nat_dec_eq(v_key_585_, v_a_582_);
                    if v___x_587_ == 0 {
                        v_x_583_ = v_tail_586_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_587_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__4___redArg___boxed(
    mut v_a_589_: *mut crate::leanh::LeanObject,
    mut v_x_590_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_591_: u8 = 0;
    let mut v_r_592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_591_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__4___redArg(v_a_589_, v_x_590_);
    crate::leanh::lean_dec(v_x_590_);
    crate::leanh::lean_dec(v_a_589_);
    v_r_592_ = crate::leanh::lean_box((v_res_591_) as usize);
    return v_r_592_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2___redArg(
    mut v_m_593_: *mut crate::leanh::LeanObject,
    mut v_a_594_: *mut crate::leanh::LeanObject,
    mut v_b_595_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_599_: u64 = 0;
    let mut v___x_600_: u64 = 0;
    let mut v___x_601_: u64 = 0;
    let mut v_fold_602_: u64 = 0;
    let mut v___x_603_: u64 = 0;
    let mut v___x_604_: u64 = 0;
    let mut v___x_605_: u64 = 0;
    let mut v___x_606_: usize = 0;
    let mut v___x_607_: usize = 0;
    let mut v___x_608_: usize = 0;
    let mut v___x_609_: usize = 0;
    let mut v___x_610_: usize = 0;
    let mut v_bkt_611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_612_: u8 = 0;
    let mut v___x_614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_615_: u8 = 0;
    let mut v___x_616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_625_: u8 = 0;
    let mut v_val_626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_633_: u8 = 0;
    let mut v_unused_634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_596_ = crate::leanh::lean_ctor_get(v_m_593_, 0);
                v_buckets_597_ = crate::leanh::lean_ctor_get(v_m_593_, 1);
                v___x_598_ = lean_array_get_size(v_buckets_597_);
                v___x_599_ = lean_uint64_of_nat(v_a_594_);
                v___x_600_ = 32u64;
                v___x_601_ = lean_uint64_shift_right(v___x_599_, v___x_600_);
                v_fold_602_ = lean_uint64_xor(v___x_599_, v___x_601_);
                v___x_603_ = 16u64;
                v___x_604_ = lean_uint64_shift_right(v_fold_602_, v___x_603_);
                v___x_605_ = lean_uint64_xor(v_fold_602_, v___x_604_);
                v___x_606_ = lean_uint64_to_usize(v___x_605_);
                v___x_607_ = lean_usize_of_nat(v___x_598_);
                v___x_608_ = 1usize;
                v___x_609_ = lean_usize_sub(v___x_607_, v___x_608_);
                v___x_610_ = lean_usize_land(v___x_606_, v___x_609_);
                v_bkt_611_ = lean_array_uget_borrowed(v_buckets_597_, v___x_610_);
                v___x_612_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__4___redArg(v_a_594_, v_bkt_611_);
                if v___x_612_ == 0 {
                    crate::leanh::lean_inc_ref(v_buckets_597_);
                    crate::leanh::lean_inc(v_size_596_);
                    v_isSharedCheck_633_ = (!crate::leanh::lean_is_exclusive(v_m_593_)) as u8;
                    if v_isSharedCheck_633_ == 0 {
                        v_unused_634_ = crate::leanh::lean_ctor_get(v_m_593_, 1);
                        crate::leanh::lean_dec(v_unused_634_);
                        v_unused_635_ = crate::leanh::lean_ctor_get(v_m_593_, 0);
                        crate::leanh::lean_dec(v_unused_635_);
                        v___x_614_ = v_m_593_;
                        v_isShared_615_ = v_isSharedCheck_633_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_593_);
                        v___x_614_ = crate::leanh::lean_box(0);
                        v_isShared_615_ = v_isSharedCheck_633_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_b_595_);
                    crate::leanh::lean_dec(v_a_594_);
                    return v_m_593_;
                }
            }
            1 => {
                v___x_616_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_617_ = lean_nat_add(v_size_596_, v___x_616_);
                crate::leanh::lean_dec(v_size_596_);
                crate::leanh::lean_inc(v_bkt_611_);
                v___x_618_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_618_, 0, v_a_594_);
                crate::leanh::lean_ctor_set(v___x_618_, 1, v_b_595_);
                crate::leanh::lean_ctor_set(v___x_618_, 2, v_bkt_611_);
                v_buckets_x27_619_ = lean_array_uset(v_buckets_597_, v___x_610_, v___x_618_);
                v___x_620_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_621_ = lean_nat_mul(v_size_x27_617_, v___x_620_);
                v___x_622_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_623_ = lean_nat_div(v___x_621_, v___x_622_);
                crate::leanh::lean_dec(v___x_621_);
                v___x_624_ = lean_array_get_size(v_buckets_x27_619_);
                v___x_625_ = lean_nat_dec_le(v___x_623_, v___x_624_);
                crate::leanh::lean_dec(v___x_623_);
                if v___x_625_ == 0 {
                    v_val_626_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__5___redArg(v_buckets_x27_619_);
                    if v_isShared_615_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_614_, 1, v_val_626_);
                        crate::leanh::lean_ctor_set(v___x_614_, 0, v_size_x27_617_);
                        v___x_628_ = v___x_614_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_629_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_629_, 0, v_size_x27_617_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_629_, 1, v_val_626_);
                        v___x_628_ = v_reuseFailAlloc_629_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_615_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_614_, 1, v_buckets_x27_619_);
                        crate::leanh::lean_ctor_set(v___x_614_, 0, v_size_x27_617_);
                        v___x_631_ = v___x_614_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_632_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_632_, 0, v_size_x27_617_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_632_, 1, v_buckets_x27_619_);
                        v___x_631_ = v_reuseFailAlloc_632_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_628_;
            }
            3 => {
                return v___x_631_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_CollectLooseBVars_main(
    mut v_e_636_: *mut crate::leanh::LeanObject,
    mut v_offset_637_: *mut crate::leanh::LeanObject,
    mut v_a_638_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_649_: u8 = 0;
    let mut v___x_650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_visited_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bvars_653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_655_: u8 = 0;
    let mut v___x_657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_658_: u8 = 0;
    let mut v___x_659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_deBruijnIndex_663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_693_: u8 = 0;
    let mut v_unused_694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_648_ = l_Lean_Expr_looseBVarRange(v_e_636_);
                v___x_649_ = lean_nat_dec_lt(v_offset_637_, v___x_648_);
                crate::leanh::lean_dec(v___x_648_);
                if v___x_649_ == 0 {
                    crate::leanh::lean_dec(v_offset_637_);
                    crate::leanh::lean_dec_ref(v_e_636_);
                    v___x_650_ = crate::leanh::lean_box(0);
                    v___x_651_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_651_, 0, v___x_650_);
                    crate::leanh::lean_ctor_set(v___x_651_, 1, v_a_638_);
                    return v___x_651_;
                } else {
                    v_visited_652_ = crate::leanh::lean_ctor_get(v_a_638_, 0);
                    v_bvars_653_ = crate::leanh::lean_ctor_get(v_a_638_, 1);
                    crate::leanh::lean_inc_ref(v_e_636_);
                    crate::leanh::lean_inc(v_offset_637_);
                    v___x_654_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_654_, 0, v_offset_637_);
                    crate::leanh::lean_ctor_set(v___x_654_, 1, v_e_636_);
                    v___x_655_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0___redArg(v_visited_652_, v___x_654_);
                    if v___x_655_ == 0 {
                        crate::leanh::lean_inc_ref(v_bvars_653_);
                        crate::leanh::lean_inc_ref(v_visited_652_);
                        v_isSharedCheck_693_ = (!crate::leanh::lean_is_exclusive(v_a_638_)) as u8;
                        if v_isSharedCheck_693_ == 0 {
                            v_unused_694_ = crate::leanh::lean_ctor_get(v_a_638_, 1);
                            crate::leanh::lean_dec(v_unused_694_);
                            v_unused_695_ = crate::leanh::lean_ctor_get(v_a_638_, 0);
                            crate::leanh::lean_dec(v_unused_695_);
                            v___x_657_ = v_a_638_;
                            v_isShared_658_ = v_isSharedCheck_693_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_a_638_);
                            v___x_657_ = crate::leanh::lean_box(0);
                            v_isShared_658_ = v_isSharedCheck_693_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v___x_654_, 2);
                        crate::leanh::lean_dec(v_offset_637_);
                        crate::leanh::lean_dec_ref(v_e_636_);
                        v___x_696_ = crate::leanh::lean_box(0);
                        v___x_697_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_697_, 0, v___x_696_);
                        crate::leanh::lean_ctor_set(v___x_697_, 1, v_a_638_);
                        return v___x_697_;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_offset_637_);
                v___x_643_ =
                    l_Lean_Expr_CollectLooseBVars_main(v_t_640_, v_offset_637_, v___y_642_);
                v_snd_644_ = crate::leanh::lean_ctor_get(v___x_643_, 1);
                crate::leanh::lean_inc(v_snd_644_);
                crate::leanh::lean_dec_ref(v___x_643_);
                v___x_645_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_646_ = lean_nat_add(v_offset_637_, v___x_645_);
                crate::leanh::lean_dec(v_offset_637_);
                v_e_636_ = v_b_641_;
                v_offset_637_ = v___x_646_;
                v_a_638_ = v_snd_644_;
                state = 0;
                continue;
            }
            2 => {
                v___x_659_ = crate::leanh::lean_box(0);
                v___x_660_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1___redArg(v_visited_652_, v___x_654_, v___x_659_);
                crate::leanh::lean_inc_ref(v_bvars_653_);
                crate::leanh::lean_inc_ref(v___x_660_);
                if v_isShared_658_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_657_, 0, v___x_660_);
                    v___x_662_ = v___x_657_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_692_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_692_, 0, v___x_660_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_692_, 1, v_bvars_653_);
                    v___x_662_ = v_reuseFailAlloc_692_;
                    state = 3;
                    continue;
                }
            }
            3 => match crate::leanh::lean_obj_tag(v_e_636_) {
                0 => {
                    crate::leanh::lean_dec_ref(v___x_662_);
                    v_deBruijnIndex_663_ = crate::leanh::lean_ctor_get(v_e_636_, 0);
                    crate::leanh::lean_inc(v_deBruijnIndex_663_);
                    crate::leanh::lean_dec_ref_known(v_e_636_, 1);
                    v___x_664_ = lean_nat_sub(v_deBruijnIndex_663_, v_offset_637_);
                    crate::leanh::lean_dec(v_offset_637_);
                    crate::leanh::lean_dec(v_deBruijnIndex_663_);
                    v___x_665_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2___redArg(v_bvars_653_, v___x_664_, v___x_659_);
                    v___x_666_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_666_, 0, v___x_660_);
                    crate::leanh::lean_ctor_set(v___x_666_, 1, v___x_665_);
                    v___x_667_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_667_, 0, v___x_659_);
                    crate::leanh::lean_ctor_set(v___x_667_, 1, v___x_666_);
                    return v___x_667_;
                }
                5 => {
                    crate::leanh::lean_dec_ref(v___x_660_);
                    crate::leanh::lean_dec_ref(v_bvars_653_);
                    v_fn_668_ = crate::leanh::lean_ctor_get(v_e_636_, 0);
                    crate::leanh::lean_inc_ref(v_fn_668_);
                    v_arg_669_ = crate::leanh::lean_ctor_get(v_e_636_, 1);
                    crate::leanh::lean_inc_ref(v_arg_669_);
                    crate::leanh::lean_dec_ref_known(v_e_636_, 2);
                    crate::leanh::lean_inc(v_offset_637_);
                    v___x_670_ =
                        l_Lean_Expr_CollectLooseBVars_main(v_fn_668_, v_offset_637_, v___x_662_);
                    v_snd_671_ = crate::leanh::lean_ctor_get(v___x_670_, 1);
                    crate::leanh::lean_inc(v_snd_671_);
                    crate::leanh::lean_dec_ref(v___x_670_);
                    v_e_636_ = v_arg_669_;
                    v_a_638_ = v_snd_671_;
                    state = 0;
                    continue;
                }
                6 => {
                    crate::leanh::lean_dec_ref(v___x_660_);
                    crate::leanh::lean_dec_ref(v_bvars_653_);
                    v_binderType_673_ = crate::leanh::lean_ctor_get(v_e_636_, 1);
                    crate::leanh::lean_inc_ref(v_binderType_673_);
                    v_body_674_ = crate::leanh::lean_ctor_get(v_e_636_, 2);
                    crate::leanh::lean_inc_ref(v_body_674_);
                    crate::leanh::lean_dec_ref_known(v_e_636_, 3);
                    v_t_640_ = v_binderType_673_;
                    v_b_641_ = v_body_674_;
                    v___y_642_ = v___x_662_;
                    state = 1;
                    continue;
                }
                7 => {
                    crate::leanh::lean_dec_ref(v___x_660_);
                    crate::leanh::lean_dec_ref(v_bvars_653_);
                    v_binderType_675_ = crate::leanh::lean_ctor_get(v_e_636_, 1);
                    crate::leanh::lean_inc_ref(v_binderType_675_);
                    v_body_676_ = crate::leanh::lean_ctor_get(v_e_636_, 2);
                    crate::leanh::lean_inc_ref(v_body_676_);
                    crate::leanh::lean_dec_ref_known(v_e_636_, 3);
                    v_t_640_ = v_binderType_675_;
                    v_b_641_ = v_body_676_;
                    v___y_642_ = v___x_662_;
                    state = 1;
                    continue;
                }
                8 => {
                    crate::leanh::lean_dec_ref(v___x_660_);
                    crate::leanh::lean_dec_ref(v_bvars_653_);
                    v_type_677_ = crate::leanh::lean_ctor_get(v_e_636_, 1);
                    crate::leanh::lean_inc_ref(v_type_677_);
                    v_value_678_ = crate::leanh::lean_ctor_get(v_e_636_, 2);
                    crate::leanh::lean_inc_ref(v_value_678_);
                    v_body_679_ = crate::leanh::lean_ctor_get(v_e_636_, 3);
                    crate::leanh::lean_inc_ref(v_body_679_);
                    crate::leanh::lean_dec_ref_known(v_e_636_, 4);
                    crate::leanh::lean_inc_n(v_offset_637_, 2);
                    v___x_680_ =
                        l_Lean_Expr_CollectLooseBVars_main(v_type_677_, v_offset_637_, v___x_662_);
                    v_snd_681_ = crate::leanh::lean_ctor_get(v___x_680_, 1);
                    crate::leanh::lean_inc(v_snd_681_);
                    crate::leanh::lean_dec_ref(v___x_680_);
                    v___x_682_ =
                        l_Lean_Expr_CollectLooseBVars_main(v_value_678_, v_offset_637_, v_snd_681_);
                    v_snd_683_ = crate::leanh::lean_ctor_get(v___x_682_, 1);
                    crate::leanh::lean_inc(v_snd_683_);
                    crate::leanh::lean_dec_ref(v___x_682_);
                    v___x_684_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_685_ = lean_nat_add(v_offset_637_, v___x_684_);
                    crate::leanh::lean_dec(v_offset_637_);
                    v_e_636_ = v_body_679_;
                    v_offset_637_ = v___x_685_;
                    v_a_638_ = v_snd_683_;
                    state = 0;
                    continue;
                }
                10 => {
                    crate::leanh::lean_dec_ref(v___x_660_);
                    crate::leanh::lean_dec_ref(v_bvars_653_);
                    v_expr_687_ = crate::leanh::lean_ctor_get(v_e_636_, 1);
                    crate::leanh::lean_inc_ref(v_expr_687_);
                    crate::leanh::lean_dec_ref_known(v_e_636_, 2);
                    v_e_636_ = v_expr_687_;
                    v_a_638_ = v___x_662_;
                    state = 0;
                    continue;
                }
                11 => {
                    crate::leanh::lean_dec_ref(v___x_660_);
                    crate::leanh::lean_dec_ref(v_bvars_653_);
                    v_struct_689_ = crate::leanh::lean_ctor_get(v_e_636_, 2);
                    crate::leanh::lean_inc_ref(v_struct_689_);
                    crate::leanh::lean_dec_ref_known(v_e_636_, 3);
                    v_e_636_ = v_struct_689_;
                    v_a_638_ = v___x_662_;
                    state = 0;
                    continue;
                }
                _ => {
                    crate::leanh::lean_dec_ref(v___x_660_);
                    crate::leanh::lean_dec_ref(v_bvars_653_);
                    crate::leanh::lean_dec(v_offset_637_);
                    crate::leanh::lean_dec_ref(v_e_636_);
                    v___x_691_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_691_, 0, v___x_659_);
                    crate::leanh::lean_ctor_set(v___x_691_, 1, v___x_662_);
                    return v___x_691_;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0(
    mut v_00_u03b2_698_: *mut crate::leanh::LeanObject,
    mut v_m_699_: *mut crate::leanh::LeanObject,
    mut v_a_700_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_701_: u8 = 0;
    v___x_701_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0___redArg(v_m_699_, v_a_700_);
    return v___x_701_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0___boxed(
    mut v_00_u03b2_702_: *mut crate::leanh::LeanObject,
    mut v_m_703_: *mut crate::leanh::LeanObject,
    mut v_a_704_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_705_: u8 = 0;
    let mut v_r_706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_705_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0(v_00_u03b2_702_, v_m_703_, v_a_704_);
    crate::leanh::lean_dec_ref(v_a_704_);
    crate::leanh::lean_dec_ref(v_m_703_);
    v_r_706_ = crate::leanh::lean_box((v_res_705_) as usize);
    return v_r_706_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1(
    mut v_00_u03b2_707_: *mut crate::leanh::LeanObject,
    mut v_m_708_: *mut crate::leanh::LeanObject,
    mut v_a_709_: *mut crate::leanh::LeanObject,
    mut v_b_710_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_711_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1___redArg(v_m_708_, v_a_709_, v_b_710_);
    return v___x_711_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2(
    mut v_00_u03b2_712_: *mut crate::leanh::LeanObject,
    mut v_m_713_: *mut crate::leanh::LeanObject,
    mut v_a_714_: *mut crate::leanh::LeanObject,
    mut v_b_715_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_716_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2___redArg(v_m_713_, v_a_714_, v_b_715_);
    return v___x_716_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0_spec__0(
    mut v_00_u03b2_717_: *mut crate::leanh::LeanObject,
    mut v_a_718_: *mut crate::leanh::LeanObject,
    mut v_x_719_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_720_: u8 = 0;
    v___x_720_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0_spec__0___redArg(v_a_718_, v_x_719_);
    return v___x_720_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0_spec__0___boxed(
    mut v_00_u03b2_721_: *mut crate::leanh::LeanObject,
    mut v_a_722_: *mut crate::leanh::LeanObject,
    mut v_x_723_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_724_: u8 = 0;
    let mut v_r_725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_724_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__0_spec__0(v_00_u03b2_721_, v_a_722_, v_x_723_);
    crate::leanh::lean_dec(v_x_723_);
    crate::leanh::lean_dec_ref(v_a_722_);
    v_r_725_ = crate::leanh::lean_box((v_res_724_) as usize);
    return v_r_725_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2(
    mut v_00_u03b2_726_: *mut crate::leanh::LeanObject,
    mut v_data_727_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_728_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2___redArg(v_data_727_);
    return v___x_728_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__4(
    mut v_00_u03b2_729_: *mut crate::leanh::LeanObject,
    mut v_a_730_: *mut crate::leanh::LeanObject,
    mut v_x_731_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_732_: u8 = 0;
    v___x_732_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__4___redArg(v_a_730_, v_x_731_);
    return v___x_732_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__4___boxed(
    mut v_00_u03b2_733_: *mut crate::leanh::LeanObject,
    mut v_a_734_: *mut crate::leanh::LeanObject,
    mut v_x_735_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_736_: u8 = 0;
    let mut v_r_737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_736_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__4(v_00_u03b2_733_, v_a_734_, v_x_735_);
    crate::leanh::lean_dec(v_x_735_);
    crate::leanh::lean_dec(v_a_734_);
    v_r_737_ = crate::leanh::lean_box((v_res_736_) as usize);
    return v_r_737_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__5(
    mut v_00_u03b2_738_: *mut crate::leanh::LeanObject,
    mut v_data_739_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_740_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__5___redArg(v_data_739_);
    return v___x_740_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2_spec__3(
    mut v_00_u03b2_741_: *mut crate::leanh::LeanObject,
    mut v_i_742_: *mut crate::leanh::LeanObject,
    mut v_source_743_: *mut crate::leanh::LeanObject,
    mut v_target_744_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_745_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2_spec__3___redArg(v_i_742_, v_source_743_, v_target_744_);
    return v___x_745_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__5_spec__7(
    mut v_00_u03b2_746_: *mut crate::leanh::LeanObject,
    mut v_i_747_: *mut crate::leanh::LeanObject,
    mut v_source_748_: *mut crate::leanh::LeanObject,
    mut v_target_749_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_750_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__5_spec__7___redArg(v_i_747_, v_source_748_, v_target_749_);
    return v___x_750_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2_spec__3_spec__5(
    mut v_00_u03b2_751_: *mut crate::leanh::LeanObject,
    mut v_x_752_: *mut crate::leanh::LeanObject,
    mut v_x_753_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_754_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2_spec__3_spec__5___redArg(v_x_752_, v_x_753_);
    return v___x_754_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__5_spec__7_spec__9(
    mut v_00_u03b2_755_: *mut crate::leanh::LeanObject,
    mut v_x_756_: *mut crate::leanh::LeanObject,
    mut v_x_757_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_758_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__5_spec__7_spec__9___redArg(v_x_756_, v_x_757_);
    return v___x_758_;
}
pub unsafe fn _init_l_Lean_Expr_collectLooseBVars___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_759_ = crate::leanh::lean_box(0);
    v___x_760_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_761_ = lean_mk_array(v___x_760_, v___x_759_);
    return v___x_761_;
}
pub unsafe fn _init_l_Lean_Expr_collectLooseBVars___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_762_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Expr_collectLooseBVars___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Expr_collectLooseBVars___closed__0_once),
        _init_l_Lean_Expr_collectLooseBVars___closed__0,
    );
    v___x_763_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_764_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_764_, 0, v___x_763_);
    crate::leanh::lean_ctor_set(v___x_764_, 1, v___x_762_);
    return v___x_764_;
}
pub unsafe fn _init_l_Lean_Expr_collectLooseBVars___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_765_ = crate::leanh::lean_box(0);
    v___x_766_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_767_ = lean_mk_array(v___x_766_, v___x_765_);
    return v___x_767_;
}
pub unsafe fn _init_l_Lean_Expr_collectLooseBVars___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_768_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Expr_collectLooseBVars___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Expr_collectLooseBVars___closed__2_once),
        _init_l_Lean_Expr_collectLooseBVars___closed__2,
    );
    v___x_769_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_770_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_770_, 0, v___x_769_);
    crate::leanh::lean_ctor_set(v___x_770_, 1, v___x_768_);
    return v___x_770_;
}
pub unsafe fn _init_l_Lean_Expr_collectLooseBVars___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_771_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Expr_collectLooseBVars___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Expr_collectLooseBVars___closed__3_once),
        _init_l_Lean_Expr_collectLooseBVars___closed__3,
    );
    v___x_772_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_772_, 0, v___x_771_);
    crate::leanh::lean_ctor_set(v___x_772_, 1, v___x_771_);
    return v___x_772_;
}
pub unsafe fn l_Lean_Expr_collectLooseBVars(
    mut v_e_773_: *mut crate::leanh::LeanObject,
    mut v_offset_774_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_775_: u8 = 0;
    v___x_775_ = l_Lean_Expr_hasLooseBVars(v_e_773_);
    if v___x_775_ == 0 {
        let mut v___x_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_offset_774_);
        crate::leanh::lean_dec_ref(v_e_773_);
        v___x_776_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Expr_collectLooseBVars___closed__1),
            core::ptr::addr_of_mut!(l_Lean_Expr_collectLooseBVars___closed__1_once),
            _init_l_Lean_Expr_collectLooseBVars___closed__1,
        );
        return v___x_776_;
    } else {
        let mut v___x_777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_bvars_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_777_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Expr_collectLooseBVars___closed__4),
            core::ptr::addr_of_mut!(l_Lean_Expr_collectLooseBVars___closed__4_once),
            _init_l_Lean_Expr_collectLooseBVars___closed__4,
        );
        v___x_778_ = l_Lean_Expr_CollectLooseBVars_main(v_e_773_, v_offset_774_, v___x_777_);
        v_snd_779_ = crate::leanh::lean_ctor_get(v___x_778_, 1);
        crate::leanh::lean_inc(v_snd_779_);
        crate::leanh::lean_dec_ref(v___x_778_);
        v_bvars_780_ = crate::leanh::lean_ctor_get(v_snd_779_, 1);
        crate::leanh::lean_inc_ref(v_bvars_780_);
        crate::leanh::lean_dec(v_snd_779_);
        return v_bvars_780_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Util_CollectLooseBVars(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Expr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Util_CollectLooseBVars(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Util_CollectLooseBVars(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Expr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_CollectLooseBVars(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Util_CollectLooseBVars(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Util_CollectLooseBVars(builtin);
}
