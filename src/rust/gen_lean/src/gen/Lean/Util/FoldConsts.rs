// Lean compiler output
// Module: Lean.Util.FoldConsts
// Imports: Lean.Util.PtrSet Lean.Declaration
use crate::ffi::{
    lean_array_fget, lean_array_fset, lean_array_get_size, lean_array_push,
    lean_array_uget_borrowed, lean_array_uset, lean_mk_array, lean_nat_add, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_ptr_addr, lean_uint64_mix_hash,
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_dec_eq,
    lean_usize_land, lean_usize_of_nat, lean_usize_sub, lean_usize_to_uint64,
};
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Lean_NameHashSet_contains, l_Lean_NameHashSet_insert, l_Lean_NameSet_append,
    l_Lean_NameSet_empty, l_Lean_NameSet_insert, l_Lean_NameSet_ofList,
};
use crate::r#gen::Lean::Declaration::{
    initialize_Lean_Declaration, l_Lean_ConstantInfo_type, l_Lean_ConstantInfo_value_x3f,
    runtime_initialize_Lean_Declaration,
};
use crate::r#gen::Lean::Util::PtrSet::{
    initialize_Lean_Util_PtrSet, l_Lean_mkPtrSet___redArg, runtime_initialize_Lean_Util_PtrSet,
};
static mut l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Expr_getUsedConstants___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Expr_getUsedConstants___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Expr_getUsedConstants___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_getUsedConstants___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Expr_getUsedConstants___closed__1_value: crate::leanh::LeanArrayObject<0> =
    crate::leanh::LeanArrayObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Expr_getUsedConstants___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_getUsedConstants___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Expr_getUsedConstantsAsSet___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Expr_getUsedConstantsAsSet___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Expr_getUsedConstantsAsSet___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_getUsedConstantsAsSet___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0_spec__0___redArg(
    mut v_a_317_: *mut crate::leanh::LeanObject,
    mut v_x_318_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_319_: u8 = 0;
    let mut v_key_320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_322_: usize = 0;
    let mut v___x_323_: usize = 0;
    let mut v___x_324_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_318_) == 0 {
                    v___x_319_ = 0;
                    return v___x_319_;
                } else {
                    v_key_320_ = crate::leanh::lean_ctor_get(v_x_318_, 0);
                    v_tail_321_ = crate::leanh::lean_ctor_get(v_x_318_, 2);
                    v___x_322_ = lean_ptr_addr(v_key_320_);
                    v___x_323_ = lean_ptr_addr(v_a_317_);
                    v___x_324_ = lean_usize_dec_eq(v___x_322_, v___x_323_);
                    if v___x_324_ == 0 {
                        v_x_318_ = v_tail_321_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_324_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0_spec__0___redArg___boxed(
    mut v_a_326_: *mut crate::leanh::LeanObject,
    mut v_x_327_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_328_: u8 = 0;
    let mut v_r_329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_328_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0_spec__0___redArg(v_a_326_, v_x_327_);
    crate::leanh::lean_dec(v_x_327_);
    crate::leanh::lean_dec_ref(v_a_326_);
    v_r_329_ = crate::leanh::lean_box((v_res_328_) as usize);
    return v_r_329_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1_spec__2_spec__3_spec__4___redArg(
    mut v_x_330_: *mut crate::leanh::LeanObject,
    mut v_x_331_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_337_: u8 = 0;
    let mut v___x_338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_339_: usize = 0;
    let mut v___x_340_: u64 = 0;
    let mut v___x_341_: u64 = 0;
    let mut v___x_342_: u64 = 0;
    let mut v___x_343_: u64 = 0;
    let mut v___x_344_: u64 = 0;
    let mut v_fold_345_: u64 = 0;
    let mut v___x_346_: u64 = 0;
    let mut v___x_347_: u64 = 0;
    let mut v___x_348_: u64 = 0;
    let mut v___x_349_: usize = 0;
    let mut v___x_350_: usize = 0;
    let mut v___x_351_: usize = 0;
    let mut v___x_352_: usize = 0;
    let mut v___x_353_: usize = 0;
    let mut v___x_354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_360_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_331_) == 0 {
                    return v_x_330_;
                } else {
                    v_key_332_ = crate::leanh::lean_ctor_get(v_x_331_, 0);
                    v_value_333_ = crate::leanh::lean_ctor_get(v_x_331_, 1);
                    v_tail_334_ = crate::leanh::lean_ctor_get(v_x_331_, 2);
                    v_isSharedCheck_360_ = (!crate::leanh::lean_is_exclusive(v_x_331_)) as u8;
                    if v_isSharedCheck_360_ == 0 {
                        v___x_336_ = v_x_331_;
                        v_isShared_337_ = v_isSharedCheck_360_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_334_);
                        crate::leanh::lean_inc(v_value_333_);
                        crate::leanh::lean_inc(v_key_332_);
                        crate::leanh::lean_dec(v_x_331_);
                        v___x_336_ = crate::leanh::lean_box(0);
                        v_isShared_337_ = v_isSharedCheck_360_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_338_ = lean_array_get_size(v_x_330_);
                v___x_339_ = lean_ptr_addr(v_key_332_);
                v___x_340_ = lean_usize_to_uint64(v___x_339_);
                v___x_341_ = 11u64;
                v___x_342_ = lean_uint64_mix_hash(v___x_340_, v___x_341_);
                v___x_343_ = 32u64;
                v___x_344_ = lean_uint64_shift_right(v___x_342_, v___x_343_);
                v_fold_345_ = lean_uint64_xor(v___x_342_, v___x_344_);
                v___x_346_ = 16u64;
                v___x_347_ = lean_uint64_shift_right(v_fold_345_, v___x_346_);
                v___x_348_ = lean_uint64_xor(v_fold_345_, v___x_347_);
                v___x_349_ = lean_uint64_to_usize(v___x_348_);
                v___x_350_ = lean_usize_of_nat(v___x_338_);
                v___x_351_ = 1usize;
                v___x_352_ = lean_usize_sub(v___x_350_, v___x_351_);
                v___x_353_ = lean_usize_land(v___x_349_, v___x_352_);
                v___x_354_ = lean_array_uget_borrowed(v_x_330_, v___x_353_);
                crate::leanh::lean_inc(v___x_354_);
                if v_isShared_337_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_336_, 2, v___x_354_);
                    v___x_356_ = v___x_336_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_359_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_359_, 0, v_key_332_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_359_, 1, v_value_333_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_359_, 2, v___x_354_);
                    v___x_356_ = v_reuseFailAlloc_359_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_357_ = lean_array_uset(v_x_330_, v___x_353_, v___x_356_);
                v_x_330_ = v___x_357_;
                v_x_331_ = v_tail_334_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1_spec__2_spec__3___redArg(
    mut v_i_361_: *mut crate::leanh::LeanObject,
    mut v_source_362_: *mut crate::leanh::LeanObject,
    mut v_target_363_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_365_: u8 = 0;
    let mut v_es_366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_364_ = lean_array_get_size(v_source_362_);
                v___x_365_ = lean_nat_dec_lt(v_i_361_, v___x_364_);
                if v___x_365_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_362_);
                    crate::leanh::lean_dec(v_i_361_);
                    return v_target_363_;
                } else {
                    v_es_366_ = lean_array_fget(v_source_362_, v_i_361_);
                    v___x_367_ = crate::leanh::lean_box(0);
                    v_source_368_ = lean_array_fset(v_source_362_, v_i_361_, v___x_367_);
                    v_target_369_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1_spec__2_spec__3_spec__4___redArg(v_target_363_, v_es_366_);
                    v___x_370_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_371_ = lean_nat_add(v_i_361_, v___x_370_);
                    crate::leanh::lean_dec(v_i_361_);
                    v_i_361_ = v___x_371_;
                    v_source_362_ = v_source_368_;
                    v_target_363_ = v_target_369_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1_spec__2___redArg(
    mut v_data_373_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_374_ = lean_array_get_size(v_data_373_);
    v___x_375_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_376_ = lean_nat_mul(v___x_374_, v___x_375_);
    v___x_377_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_378_ = crate::leanh::lean_box(0);
    v___x_379_ = lean_mk_array(v_nbuckets_376_, v___x_378_);
    v___x_380_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1_spec__2_spec__3___redArg(v___x_377_, v_data_373_, v___x_379_);
    return v___x_380_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1___redArg(
    mut v_m_381_: *mut crate::leanh::LeanObject,
    mut v_a_382_: *mut crate::leanh::LeanObject,
    mut v_b_383_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_387_: usize = 0;
    let mut v___x_388_: u64 = 0;
    let mut v___x_389_: u64 = 0;
    let mut v___x_390_: u64 = 0;
    let mut v___x_391_: u64 = 0;
    let mut v___x_392_: u64 = 0;
    let mut v_fold_393_: u64 = 0;
    let mut v___x_394_: u64 = 0;
    let mut v___x_395_: u64 = 0;
    let mut v___x_396_: u64 = 0;
    let mut v___x_397_: usize = 0;
    let mut v___x_398_: usize = 0;
    let mut v___x_399_: usize = 0;
    let mut v___x_400_: usize = 0;
    let mut v___x_401_: usize = 0;
    let mut v_bkt_402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_403_: u8 = 0;
    let mut v___x_405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_406_: u8 = 0;
    let mut v___x_407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_416_: u8 = 0;
    let mut v_val_417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_424_: u8 = 0;
    let mut v_unused_425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_384_ = crate::leanh::lean_ctor_get(v_m_381_, 0);
                v_buckets_385_ = crate::leanh::lean_ctor_get(v_m_381_, 1);
                v___x_386_ = lean_array_get_size(v_buckets_385_);
                v___x_387_ = lean_ptr_addr(v_a_382_);
                v___x_388_ = lean_usize_to_uint64(v___x_387_);
                v___x_389_ = 11u64;
                v___x_390_ = lean_uint64_mix_hash(v___x_388_, v___x_389_);
                v___x_391_ = 32u64;
                v___x_392_ = lean_uint64_shift_right(v___x_390_, v___x_391_);
                v_fold_393_ = lean_uint64_xor(v___x_390_, v___x_392_);
                v___x_394_ = 16u64;
                v___x_395_ = lean_uint64_shift_right(v_fold_393_, v___x_394_);
                v___x_396_ = lean_uint64_xor(v_fold_393_, v___x_395_);
                v___x_397_ = lean_uint64_to_usize(v___x_396_);
                v___x_398_ = lean_usize_of_nat(v___x_386_);
                v___x_399_ = 1usize;
                v___x_400_ = lean_usize_sub(v___x_398_, v___x_399_);
                v___x_401_ = lean_usize_land(v___x_397_, v___x_400_);
                v_bkt_402_ = lean_array_uget_borrowed(v_buckets_385_, v___x_401_);
                v___x_403_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0_spec__0___redArg(v_a_382_, v_bkt_402_);
                if v___x_403_ == 0 {
                    crate::leanh::lean_inc_ref(v_buckets_385_);
                    crate::leanh::lean_inc(v_size_384_);
                    v_isSharedCheck_424_ = (!crate::leanh::lean_is_exclusive(v_m_381_)) as u8;
                    if v_isSharedCheck_424_ == 0 {
                        v_unused_425_ = crate::leanh::lean_ctor_get(v_m_381_, 1);
                        crate::leanh::lean_dec(v_unused_425_);
                        v_unused_426_ = crate::leanh::lean_ctor_get(v_m_381_, 0);
                        crate::leanh::lean_dec(v_unused_426_);
                        v___x_405_ = v_m_381_;
                        v_isShared_406_ = v_isSharedCheck_424_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_381_);
                        v___x_405_ = crate::leanh::lean_box(0);
                        v_isShared_406_ = v_isSharedCheck_424_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_b_383_);
                    crate::leanh::lean_dec_ref(v_a_382_);
                    return v_m_381_;
                }
            }
            1 => {
                v___x_407_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_408_ = lean_nat_add(v_size_384_, v___x_407_);
                crate::leanh::lean_dec(v_size_384_);
                crate::leanh::lean_inc(v_bkt_402_);
                v___x_409_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_409_, 0, v_a_382_);
                crate::leanh::lean_ctor_set(v___x_409_, 1, v_b_383_);
                crate::leanh::lean_ctor_set(v___x_409_, 2, v_bkt_402_);
                v_buckets_x27_410_ = lean_array_uset(v_buckets_385_, v___x_401_, v___x_409_);
                v___x_411_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_412_ = lean_nat_mul(v_size_x27_408_, v___x_411_);
                v___x_413_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_414_ = lean_nat_div(v___x_412_, v___x_413_);
                crate::leanh::lean_dec(v___x_412_);
                v___x_415_ = lean_array_get_size(v_buckets_x27_410_);
                v___x_416_ = lean_nat_dec_le(v___x_414_, v___x_415_);
                crate::leanh::lean_dec(v___x_414_);
                if v___x_416_ == 0 {
                    v_val_417_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1_spec__2___redArg(v_buckets_x27_410_);
                    if v_isShared_406_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_405_, 1, v_val_417_);
                        crate::leanh::lean_ctor_set(v___x_405_, 0, v_size_x27_408_);
                        v___x_419_ = v___x_405_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_420_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_420_, 0, v_size_x27_408_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_420_, 1, v_val_417_);
                        v___x_419_ = v_reuseFailAlloc_420_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_406_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_405_, 1, v_buckets_x27_410_);
                        crate::leanh::lean_ctor_set(v___x_405_, 0, v_size_x27_408_);
                        v___x_422_ = v___x_405_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_423_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_423_, 0, v_size_x27_408_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_423_, 1, v_buckets_x27_410_);
                        v___x_422_ = v_reuseFailAlloc_423_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_419_;
            }
            3 => {
                return v___x_422_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0___redArg(
    mut v_m_427_: *mut crate::leanh::LeanObject,
    mut v_a_428_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_buckets_429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_431_: usize = 0;
    let mut v___x_432_: u64 = 0;
    let mut v___x_433_: u64 = 0;
    let mut v___x_434_: u64 = 0;
    let mut v___x_435_: u64 = 0;
    let mut v___x_436_: u64 = 0;
    let mut v_fold_437_: u64 = 0;
    let mut v___x_438_: u64 = 0;
    let mut v___x_439_: u64 = 0;
    let mut v___x_440_: u64 = 0;
    let mut v___x_441_: usize = 0;
    let mut v___x_442_: usize = 0;
    let mut v___x_443_: usize = 0;
    let mut v___x_444_: usize = 0;
    let mut v___x_445_: usize = 0;
    let mut v___x_446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_447_: u8 = 0;
    v_buckets_429_ = crate::leanh::lean_ctor_get(v_m_427_, 1);
    v___x_430_ = lean_array_get_size(v_buckets_429_);
    v___x_431_ = lean_ptr_addr(v_a_428_);
    v___x_432_ = lean_usize_to_uint64(v___x_431_);
    v___x_433_ = 11u64;
    v___x_434_ = lean_uint64_mix_hash(v___x_432_, v___x_433_);
    v___x_435_ = 32u64;
    v___x_436_ = lean_uint64_shift_right(v___x_434_, v___x_435_);
    v_fold_437_ = lean_uint64_xor(v___x_434_, v___x_436_);
    v___x_438_ = 16u64;
    v___x_439_ = lean_uint64_shift_right(v_fold_437_, v___x_438_);
    v___x_440_ = lean_uint64_xor(v_fold_437_, v___x_439_);
    v___x_441_ = lean_uint64_to_usize(v___x_440_);
    v___x_442_ = lean_usize_of_nat(v___x_430_);
    v___x_443_ = 1usize;
    v___x_444_ = lean_usize_sub(v___x_442_, v___x_443_);
    v___x_445_ = lean_usize_land(v___x_441_, v___x_444_);
    v___x_446_ = lean_array_uget_borrowed(v_buckets_429_, v___x_445_);
    v___x_447_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0_spec__0___redArg(v_a_428_, v___x_446_);
    return v___x_447_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0___redArg___boxed(
    mut v_m_448_: *mut crate::leanh::LeanObject,
    mut v_a_449_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_450_: u8 = 0;
    let mut v_r_451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_450_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0___redArg(v_m_448_, v_a_449_);
    crate::leanh::lean_dec_ref(v_a_449_);
    crate::leanh::lean_dec_ref(v_m_448_);
    v_r_451_ = crate::leanh::lean_box((v_res_450_) as usize);
    return v_r_451_;
}
pub unsafe fn l___private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit___redArg(
    mut v_f_452_: *mut crate::leanh::LeanObject,
    mut v_e_453_: *mut crate::leanh::LeanObject,
    mut v_acc_454_: *mut crate::leanh::LeanObject,
    mut v_a_455_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_d_457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_visited_464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_visitedConsts_465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_466_: u8 = 0;
    let mut v___x_468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_469_: u8 = 0;
    let mut v___x_470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_499_: u8 = 0;
    let mut v___x_500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_507_: u8 = 0;
    let mut v_unused_508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_visited_464_ = crate::leanh::lean_ctor_get(v_a_455_, 0);
                v_visitedConsts_465_ = crate::leanh::lean_ctor_get(v_a_455_, 1);
                v___x_466_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0___redArg(v_visited_464_, v_e_453_);
                if v___x_466_ == 0 {
                    crate::leanh::lean_inc_ref(v_visitedConsts_465_);
                    crate::leanh::lean_inc_ref(v_visited_464_);
                    v_isSharedCheck_507_ = (!crate::leanh::lean_is_exclusive(v_a_455_)) as u8;
                    if v_isSharedCheck_507_ == 0 {
                        v_unused_508_ = crate::leanh::lean_ctor_get(v_a_455_, 1);
                        crate::leanh::lean_dec(v_unused_508_);
                        v_unused_509_ = crate::leanh::lean_ctor_get(v_a_455_, 0);
                        crate::leanh::lean_dec(v_unused_509_);
                        v___x_468_ = v_a_455_;
                        v_isShared_469_ = v_isSharedCheck_507_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_a_455_);
                        v___x_468_ = crate::leanh::lean_box(0);
                        v_isShared_469_ = v_isSharedCheck_507_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_453_);
                    crate::leanh::lean_dec(v_f_452_);
                    v___x_510_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_510_, 0, v_acc_454_);
                    crate::leanh::lean_ctor_set(v___x_510_, 1, v_a_455_);
                    return v___x_510_;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_f_452_);
                v___x_460_ = l___private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit___redArg(v_f_452_, v_d_457_, v_acc_454_, v___y_459_);
                v_fst_461_ = crate::leanh::lean_ctor_get(v___x_460_, 0);
                crate::leanh::lean_inc(v_fst_461_);
                v_snd_462_ = crate::leanh::lean_ctor_get(v___x_460_, 1);
                crate::leanh::lean_inc(v_snd_462_);
                crate::leanh::lean_dec_ref(v___x_460_);
                v_e_453_ = v_b_458_;
                v_acc_454_ = v_fst_461_;
                v_a_455_ = v_snd_462_;
                state = 0;
                continue;
            }
            2 => {
                v___x_470_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc_ref(v_e_453_);
                v___x_471_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1___redArg(v_visited_464_, v_e_453_, v___x_470_);
                crate::leanh::lean_inc_ref(v_visitedConsts_465_);
                crate::leanh::lean_inc_ref(v___x_471_);
                if v_isShared_469_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_468_, 0, v___x_471_);
                    v___x_473_ = v___x_468_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_506_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_506_, 0, v___x_471_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_506_, 1, v_visitedConsts_465_);
                    v___x_473_ = v_reuseFailAlloc_506_;
                    state = 3;
                    continue;
                }
            }
            3 => match crate::leanh::lean_obj_tag(v_e_453_) {
                7 => {
                    crate::leanh::lean_dec_ref(v___x_471_);
                    crate::leanh::lean_dec_ref(v_visitedConsts_465_);
                    v_binderType_474_ = crate::leanh::lean_ctor_get(v_e_453_, 1);
                    crate::leanh::lean_inc_ref(v_binderType_474_);
                    v_body_475_ = crate::leanh::lean_ctor_get(v_e_453_, 2);
                    crate::leanh::lean_inc_ref(v_body_475_);
                    crate::leanh::lean_dec_ref_known(v_e_453_, 3);
                    v_d_457_ = v_binderType_474_;
                    v_b_458_ = v_body_475_;
                    v___y_459_ = v___x_473_;
                    state = 1;
                    continue;
                }
                6 => {
                    crate::leanh::lean_dec_ref(v___x_471_);
                    crate::leanh::lean_dec_ref(v_visitedConsts_465_);
                    v_binderType_476_ = crate::leanh::lean_ctor_get(v_e_453_, 1);
                    crate::leanh::lean_inc_ref(v_binderType_476_);
                    v_body_477_ = crate::leanh::lean_ctor_get(v_e_453_, 2);
                    crate::leanh::lean_inc_ref(v_body_477_);
                    crate::leanh::lean_dec_ref_known(v_e_453_, 3);
                    v_d_457_ = v_binderType_476_;
                    v_b_458_ = v_body_477_;
                    v___y_459_ = v___x_473_;
                    state = 1;
                    continue;
                }
                10 => {
                    crate::leanh::lean_dec_ref(v___x_471_);
                    crate::leanh::lean_dec_ref(v_visitedConsts_465_);
                    v_expr_478_ = crate::leanh::lean_ctor_get(v_e_453_, 1);
                    crate::leanh::lean_inc_ref(v_expr_478_);
                    crate::leanh::lean_dec_ref_known(v_e_453_, 2);
                    v_e_453_ = v_expr_478_;
                    v_a_455_ = v___x_473_;
                    state = 0;
                    continue;
                }
                8 => {
                    crate::leanh::lean_dec_ref(v___x_471_);
                    crate::leanh::lean_dec_ref(v_visitedConsts_465_);
                    v_type_480_ = crate::leanh::lean_ctor_get(v_e_453_, 1);
                    crate::leanh::lean_inc_ref(v_type_480_);
                    v_value_481_ = crate::leanh::lean_ctor_get(v_e_453_, 2);
                    crate::leanh::lean_inc_ref(v_value_481_);
                    v_body_482_ = crate::leanh::lean_ctor_get(v_e_453_, 3);
                    crate::leanh::lean_inc_ref(v_body_482_);
                    crate::leanh::lean_dec_ref_known(v_e_453_, 4);
                    crate::leanh::lean_inc_n(v_f_452_, 2);
                    v___x_483_ = l___private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit___redArg(v_f_452_, v_type_480_, v_acc_454_, v___x_473_);
                    v_fst_484_ = crate::leanh::lean_ctor_get(v___x_483_, 0);
                    crate::leanh::lean_inc(v_fst_484_);
                    v_snd_485_ = crate::leanh::lean_ctor_get(v___x_483_, 1);
                    crate::leanh::lean_inc(v_snd_485_);
                    crate::leanh::lean_dec_ref(v___x_483_);
                    v___x_486_ = l___private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit___redArg(v_f_452_, v_value_481_, v_fst_484_, v_snd_485_);
                    v_fst_487_ = crate::leanh::lean_ctor_get(v___x_486_, 0);
                    crate::leanh::lean_inc(v_fst_487_);
                    v_snd_488_ = crate::leanh::lean_ctor_get(v___x_486_, 1);
                    crate::leanh::lean_inc(v_snd_488_);
                    crate::leanh::lean_dec_ref(v___x_486_);
                    v_e_453_ = v_body_482_;
                    v_acc_454_ = v_fst_487_;
                    v_a_455_ = v_snd_488_;
                    state = 0;
                    continue;
                }
                5 => {
                    crate::leanh::lean_dec_ref(v___x_471_);
                    crate::leanh::lean_dec_ref(v_visitedConsts_465_);
                    v_fn_490_ = crate::leanh::lean_ctor_get(v_e_453_, 0);
                    crate::leanh::lean_inc_ref(v_fn_490_);
                    v_arg_491_ = crate::leanh::lean_ctor_get(v_e_453_, 1);
                    crate::leanh::lean_inc_ref(v_arg_491_);
                    crate::leanh::lean_dec_ref_known(v_e_453_, 2);
                    crate::leanh::lean_inc(v_f_452_);
                    v___x_492_ = l___private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit___redArg(v_f_452_, v_fn_490_, v_acc_454_, v___x_473_);
                    v_fst_493_ = crate::leanh::lean_ctor_get(v___x_492_, 0);
                    crate::leanh::lean_inc(v_fst_493_);
                    v_snd_494_ = crate::leanh::lean_ctor_get(v___x_492_, 1);
                    crate::leanh::lean_inc(v_snd_494_);
                    crate::leanh::lean_dec_ref(v___x_492_);
                    v_e_453_ = v_arg_491_;
                    v_acc_454_ = v_fst_493_;
                    v_a_455_ = v_snd_494_;
                    state = 0;
                    continue;
                }
                11 => {
                    crate::leanh::lean_dec_ref(v___x_471_);
                    crate::leanh::lean_dec_ref(v_visitedConsts_465_);
                    v_struct_496_ = crate::leanh::lean_ctor_get(v_e_453_, 2);
                    crate::leanh::lean_inc_ref(v_struct_496_);
                    crate::leanh::lean_dec_ref_known(v_e_453_, 3);
                    v_e_453_ = v_struct_496_;
                    v_a_455_ = v___x_473_;
                    state = 0;
                    continue;
                }
                4 => {
                    v_declName_498_ = crate::leanh::lean_ctor_get(v_e_453_, 0);
                    crate::leanh::lean_inc(v_declName_498_);
                    crate::leanh::lean_dec_ref_known(v_e_453_, 2);
                    v___x_499_ = l_Lean_NameHashSet_contains(v_visitedConsts_465_, v_declName_498_);
                    if v___x_499_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_473_);
                        crate::leanh::lean_inc(v_declName_498_);
                        v___x_500_ =
                            l_Lean_NameHashSet_insert(v_visitedConsts_465_, v_declName_498_);
                        v___x_501_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_501_, 0, v___x_471_);
                        crate::leanh::lean_ctor_set(v___x_501_, 1, v___x_500_);
                        v___x_502_ =
                            crate::leanh::lean_apply_2(v_f_452_, v_declName_498_, v_acc_454_);
                        v___x_503_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_503_, 0, v___x_502_);
                        crate::leanh::lean_ctor_set(v___x_503_, 1, v___x_501_);
                        return v___x_503_;
                    } else {
                        crate::leanh::lean_dec(v_declName_498_);
                        crate::leanh::lean_dec_ref(v___x_471_);
                        crate::leanh::lean_dec_ref(v_visitedConsts_465_);
                        crate::leanh::lean_dec(v_f_452_);
                        v___x_504_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_504_, 0, v_acc_454_);
                        crate::leanh::lean_ctor_set(v___x_504_, 1, v___x_473_);
                        return v___x_504_;
                    }
                }
                _ => {
                    crate::leanh::lean_dec_ref(v___x_471_);
                    crate::leanh::lean_dec_ref(v_visitedConsts_465_);
                    crate::leanh::lean_dec_ref(v_e_453_);
                    crate::leanh::lean_dec(v_f_452_);
                    v___x_505_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_505_, 0, v_acc_454_);
                    crate::leanh::lean_ctor_set(v___x_505_, 1, v___x_473_);
                    return v___x_505_;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit(
    mut v_00_u03b1_511_: *mut crate::leanh::LeanObject,
    mut v_f_512_: *mut crate::leanh::LeanObject,
    mut v_e_513_: *mut crate::leanh::LeanObject,
    mut v_acc_514_: *mut crate::leanh::LeanObject,
    mut v_a_515_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_516_ = l___private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit___redArg(
        v_f_512_, v_e_513_, v_acc_514_, v_a_515_,
    );
    return v___x_516_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0(
    mut v_00_u03b2_517_: *mut crate::leanh::LeanObject,
    mut v_m_518_: *mut crate::leanh::LeanObject,
    mut v_a_519_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_520_: u8 = 0;
    v___x_520_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0___redArg(v_m_518_, v_a_519_);
    return v___x_520_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0___boxed(
    mut v_00_u03b2_521_: *mut crate::leanh::LeanObject,
    mut v_m_522_: *mut crate::leanh::LeanObject,
    mut v_a_523_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_524_: u8 = 0;
    let mut v_r_525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_524_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0(v_00_u03b2_521_, v_m_522_, v_a_523_);
    crate::leanh::lean_dec_ref(v_a_523_);
    crate::leanh::lean_dec_ref(v_m_522_);
    v_r_525_ = crate::leanh::lean_box((v_res_524_) as usize);
    return v_r_525_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1(
    mut v_00_u03b2_526_: *mut crate::leanh::LeanObject,
    mut v_m_527_: *mut crate::leanh::LeanObject,
    mut v_a_528_: *mut crate::leanh::LeanObject,
    mut v_b_529_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_530_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1___redArg(v_m_527_, v_a_528_, v_b_529_);
    return v___x_530_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0_spec__0(
    mut v_00_u03b2_531_: *mut crate::leanh::LeanObject,
    mut v_a_532_: *mut crate::leanh::LeanObject,
    mut v_x_533_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_534_: u8 = 0;
    v___x_534_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0_spec__0___redArg(v_a_532_, v_x_533_);
    return v___x_534_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0_spec__0___boxed(
    mut v_00_u03b2_535_: *mut crate::leanh::LeanObject,
    mut v_a_536_: *mut crate::leanh::LeanObject,
    mut v_x_537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_538_: u8 = 0;
    let mut v_r_539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_538_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__0_spec__0(v_00_u03b2_535_, v_a_536_, v_x_537_);
    crate::leanh::lean_dec(v_x_537_);
    crate::leanh::lean_dec_ref(v_a_536_);
    v_r_539_ = crate::leanh::lean_box((v_res_538_) as usize);
    return v_r_539_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1_spec__2(
    mut v_00_u03b2_540_: *mut crate::leanh::LeanObject,
    mut v_data_541_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_542_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1_spec__2___redArg(v_data_541_);
    return v___x_542_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1_spec__2_spec__3(
    mut v_00_u03b2_543_: *mut crate::leanh::LeanObject,
    mut v_i_544_: *mut crate::leanh::LeanObject,
    mut v_source_545_: *mut crate::leanh::LeanObject,
    mut v_target_546_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_547_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1_spec__2_spec__3___redArg(v_i_544_, v_source_545_, v_target_546_);
    return v___x_547_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1_spec__2_spec__3_spec__4(
    mut v_00_u03b2_548_: *mut crate::leanh::LeanObject,
    mut v_x_549_: *mut crate::leanh::LeanObject,
    mut v_x_550_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_551_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit_spec__1_spec__2_spec__3_spec__4___redArg(v_x_549_, v_x_550_);
    return v___x_551_;
}
pub unsafe fn l_Lean_Expr_FoldConstsImpl_fold___redArg(
    mut v_f_552_: *mut crate::leanh::LeanObject,
    mut v_e_553_: *mut crate::leanh::LeanObject,
    mut v_acc_554_: *mut crate::leanh::LeanObject,
    mut v_a_555_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_556_ = l___private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit___redArg(
        v_f_552_, v_e_553_, v_acc_554_, v_a_555_,
    );
    return v___x_556_;
}
pub unsafe fn l_Lean_Expr_FoldConstsImpl_fold(
    mut v_00_u03b1_557_: *mut crate::leanh::LeanObject,
    mut v_f_558_: *mut crate::leanh::LeanObject,
    mut v_e_559_: *mut crate::leanh::LeanObject,
    mut v_acc_560_: *mut crate::leanh::LeanObject,
    mut v_a_561_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_562_ = l___private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit___redArg(
        v_f_558_, v_e_559_, v_acc_560_, v_a_561_,
    );
    return v___x_562_;
}
pub unsafe fn _init_l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_563_ = crate::leanh::lean_unsigned_to_nat(64);
    v___x_564_ = l_Lean_mkPtrSet___redArg(v___x_563_);
    return v___x_564_;
}
pub unsafe fn _init_l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_565_ = crate::leanh::lean_box(0);
    v___x_566_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_567_ = lean_mk_array(v___x_566_, v___x_565_);
    return v___x_567_;
}
pub unsafe fn _init_l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_568_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__1_once),
        _init_l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__1,
    );
    v___x_569_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_570_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_570_, 0, v___x_569_);
    crate::leanh::lean_ctor_set(v___x_570_, 1, v___x_568_);
    return v___x_570_;
}
pub unsafe fn _init_l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_571_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__2_once),
        _init_l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__2,
    );
    v___x_572_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__0_once),
        _init_l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__0,
    );
    v___x_573_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_573_, 0, v___x_572_);
    crate::leanh::lean_ctor_set(v___x_573_, 1, v___x_571_);
    return v___x_573_;
}
pub unsafe fn l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg(
    mut v_e_574_: *mut crate::leanh::LeanObject,
    mut v_init_575_: *mut crate::leanh::LeanObject,
    mut v_f_576_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_577_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__3_once),
        _init_l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__3,
    );
    v___x_578_ = l___private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit___redArg(
        v_f_576_,
        v_e_574_,
        v_init_575_,
        v___x_577_,
    );
    v_fst_579_ = crate::leanh::lean_ctor_get(v___x_578_, 0);
    crate::leanh::lean_inc(v_fst_579_);
    crate::leanh::lean_dec_ref(v___x_578_);
    return v_fst_579_;
}
pub unsafe fn l_Lean_Expr_FoldConstsImpl_foldUnsafe(
    mut v_00_u03b1_580_: *mut crate::leanh::LeanObject,
    mut v_e_581_: *mut crate::leanh::LeanObject,
    mut v_init_582_: *mut crate::leanh::LeanObject,
    mut v_f_583_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_584_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__3_once),
        _init_l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__3,
    );
    v___x_585_ = l___private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit___redArg(
        v_f_583_,
        v_e_581_,
        v_init_582_,
        v___x_584_,
    );
    v_fst_586_ = crate::leanh::lean_ctor_get(v___x_585_, 0);
    crate::leanh::lean_inc(v_fst_586_);
    crate::leanh::lean_dec_ref(v___x_585_);
    return v_fst_586_;
}
pub unsafe fn l_Lean_Expr_getUsedConstants___lam__0(
    mut v_c_587_: *mut crate::leanh::LeanObject,
    mut v_cs_588_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_589_ = lean_array_push(v_cs_588_, v_c_587_);
    return v___x_589_;
}
pub unsafe fn l_Lean_Expr_getUsedConstants(
    mut v_e_593_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_594_ = l_Lean_Expr_getUsedConstants___closed__0;
    v___x_595_ = l_Lean_Expr_getUsedConstants___closed__1;
    v___x_596_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__3_once),
        _init_l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__3,
    );
    v___x_597_ = l___private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit___redArg(
        v___f_594_, v_e_593_, v___x_595_, v___x_596_,
    );
    v_fst_598_ = crate::leanh::lean_ctor_get(v___x_597_, 0);
    crate::leanh::lean_inc(v_fst_598_);
    crate::leanh::lean_dec_ref(v___x_597_);
    return v_fst_598_;
}
pub unsafe fn l_Lean_Expr_getUsedConstantsAsSet___lam__0(
    mut v_c_599_: *mut crate::leanh::LeanObject,
    mut v_cs_600_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_601_ = l_Lean_NameSet_insert(v_cs_600_, v_c_599_);
    return v___x_601_;
}
pub unsafe fn l_Lean_Expr_getUsedConstantsAsSet(
    mut v_e_603_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_604_ = l_Lean_Expr_getUsedConstantsAsSet___closed__0;
    v___x_605_ = l_Lean_NameSet_empty;
    v___x_606_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__3_once),
        _init_l_Lean_Expr_FoldConstsImpl_foldUnsafe___redArg___closed__3,
    );
    v___x_607_ = l___private_Lean_Util_FoldConsts_0__Lean_Expr_FoldConstsImpl_fold_visit___redArg(
        v___f_604_, v_e_603_, v___x_605_, v___x_606_,
    );
    v_fst_608_ = crate::leanh::lean_ctor_get(v___x_607_, 0);
    crate::leanh::lean_inc(v_fst_608_);
    crate::leanh::lean_dec_ref(v___x_607_);
    return v_fst_608_;
}
pub unsafe fn l_Lean_ConstantInfo_getUsedConstantsAsSet(
    mut v_c_609_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_612_: u8 = 0;
    let mut v___x_613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_610_ = l_Lean_ConstantInfo_type(v_c_609_);
    v___x_611_ = l_Lean_Expr_getUsedConstantsAsSet(v___x_610_);
    v___x_612_ = 1;
    crate::leanh::lean_inc_ref(v_c_609_);
    v___x_613_ = l_Lean_ConstantInfo_value_x3f(v_c_609_, v___x_612_);
    if crate::leanh::lean_obj_tag(v___x_613_) == 0 {
        match crate::leanh::lean_obj_tag(v_c_609_) {
            5 => {
                let mut v_val_614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_ctors_615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_val_614_ = crate::leanh::lean_ctor_get(v_c_609_, 0);
                crate::leanh::lean_inc_ref(v_val_614_);
                crate::leanh::lean_dec_ref_known(v_c_609_, 1);
                v_ctors_615_ = crate::leanh::lean_ctor_get(v_val_614_, 4);
                crate::leanh::lean_inc(v_ctors_615_);
                crate::leanh::lean_dec_ref(v_val_614_);
                v___x_616_ = l_Lean_NameSet_ofList(v_ctors_615_);
                crate::leanh::lean_dec(v_ctors_615_);
                v___x_617_ = l_Lean_NameSet_append(v___x_611_, v___x_616_);
                return v___x_617_;
            }
            6 => {
                let mut v_val_618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_toConstantVal_619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_name_620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_val_618_ = crate::leanh::lean_ctor_get(v_c_609_, 0);
                crate::leanh::lean_inc_ref(v_val_618_);
                crate::leanh::lean_dec_ref_known(v_c_609_, 1);
                v_toConstantVal_619_ = crate::leanh::lean_ctor_get(v_val_618_, 0);
                crate::leanh::lean_inc_ref(v_toConstantVal_619_);
                crate::leanh::lean_dec_ref(v_val_618_);
                v_name_620_ = crate::leanh::lean_ctor_get(v_toConstantVal_619_, 0);
                crate::leanh::lean_inc(v_name_620_);
                crate::leanh::lean_dec_ref(v_toConstantVal_619_);
                v___x_621_ = l_Lean_NameSet_empty;
                v___x_622_ = l_Lean_NameSet_insert(v___x_621_, v_name_620_);
                v___x_623_ = l_Lean_NameSet_append(v___x_611_, v___x_622_);
                return v___x_623_;
            }
            7 => {
                let mut v_val_624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_all_625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_val_624_ = crate::leanh::lean_ctor_get(v_c_609_, 0);
                crate::leanh::lean_inc_ref(v_val_624_);
                crate::leanh::lean_dec_ref_known(v_c_609_, 1);
                v_all_625_ = crate::leanh::lean_ctor_get(v_val_624_, 1);
                crate::leanh::lean_inc(v_all_625_);
                crate::leanh::lean_dec_ref(v_val_624_);
                v___x_626_ = l_Lean_NameSet_ofList(v_all_625_);
                crate::leanh::lean_dec(v_all_625_);
                v___x_627_ = l_Lean_NameSet_append(v___x_611_, v___x_626_);
                return v___x_627_;
            }
            _ => {
                let mut v___x_628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v_c_609_);
                v___x_628_ = l_Lean_NameSet_empty;
                v___x_629_ = l_Lean_NameSet_append(v___x_611_, v___x_628_);
                return v___x_629_;
            }
        }
    } else {
        let mut v_val_630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_c_609_);
        v_val_630_ = crate::leanh::lean_ctor_get(v___x_613_, 0);
        crate::leanh::lean_inc(v_val_630_);
        crate::leanh::lean_dec_ref_known(v___x_613_, 1);
        v___x_631_ = l_Lean_Expr_getUsedConstantsAsSet(v_val_630_);
        v___x_632_ = l_Lean_NameSet_append(v___x_611_, v___x_631_);
        return v___x_632_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Util_FoldConsts(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Util_PtrSet(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Declaration(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Util_FoldConsts(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Util_FoldConsts(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Util_PtrSet(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Declaration(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_FoldConsts(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Util_FoldConsts(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Util_FoldConsts(builtin);
}
