// Lean compiler output
// Module: Lean.Util.CollectLevelMVars
// Imports: Lean.Expr
use crate::r#gen::Lean::Expr::{
    initialize_Lean_Expr, l_Lean_Expr_hasMVar, l_Lean_Expr_hash, runtime_initialize_Lean_Expr,
};
use crate::r#gen::Lean::Level::{l_Lean_Level_hasMVar, l_Lean_Level_hash};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_of_nat, lean_usize_sub};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity,
    lean_nat_add, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul,
};
use crate::lean_imports_rs::Lean::Expr::lean_expr_eqv;
use crate::lean_imports_rs::Lean::Level::lean_level_eq;
static mut l_Lean_CollectLevelMVars_instInhabitedState___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_CollectLevelMVars_instInhabitedState___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_CollectLevelMVars_instInhabitedState___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_CollectLevelMVars_instInhabitedState___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_CollectLevelMVars_instInhabitedState___closed__2_value:
    crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_CollectLevelMVars_instInhabitedState___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_CollectLevelMVars_instInhabitedState___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_CollectLevelMVars_instInhabitedState___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_CollectLevelMVars_instInhabitedState___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_CollectLevelMVars_instInhabitedState: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn _init_l_Lean_CollectLevelMVars_instInhabitedState___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_436_ = crate::leanh::lean_box(0);
    v___x_437_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_438_ = lean_mk_array(v___x_437_, v___x_436_);
    return v___x_438_;
}
pub unsafe fn _init_l_Lean_CollectLevelMVars_instInhabitedState___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_439_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_CollectLevelMVars_instInhabitedState___closed__0),
        core::ptr::addr_of_mut!(l_Lean_CollectLevelMVars_instInhabitedState___closed__0_once),
        _init_l_Lean_CollectLevelMVars_instInhabitedState___closed__0,
    );
    v___x_440_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_441_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_441_, 0, v___x_440_);
    crate::leanh::lean_ctor_set(v___x_441_, 1, v___x_439_);
    return v___x_441_;
}
pub unsafe fn _init_l_Lean_CollectLevelMVars_instInhabitedState___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_444_ = l_Lean_CollectLevelMVars_instInhabitedState___closed__2;
    v___x_445_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_CollectLevelMVars_instInhabitedState___closed__1),
        core::ptr::addr_of_mut!(l_Lean_CollectLevelMVars_instInhabitedState___closed__1_once),
        _init_l_Lean_CollectLevelMVars_instInhabitedState___closed__1,
    );
    v___x_446_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_446_, 0, v___x_445_);
    crate::leanh::lean_ctor_set(v___x_446_, 1, v___x_445_);
    crate::leanh::lean_ctor_set(v___x_446_, 2, v___x_444_);
    return v___x_446_;
}
pub unsafe fn _init_l_Lean_CollectLevelMVars_instInhabitedState() -> *mut crate::leanh::LeanObject {
    let mut v___x_447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_447_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_CollectLevelMVars_instInhabitedState___closed__3),
        core::ptr::addr_of_mut!(l_Lean_CollectLevelMVars_instInhabitedState___closed__3_once),
        _init_l_Lean_CollectLevelMVars_instInhabitedState___closed__3,
    );
    return v___x_447_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__1___redArg(
    mut v_a_448_: *mut crate::leanh::LeanObject,
    mut v_x_449_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_450_: u8 = 0;
    let mut v_key_451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_453_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_449_) == 0 {
                    v___x_450_ = 0;
                    return v___x_450_;
                } else {
                    v_key_451_ = crate::leanh::lean_ctor_get(v_x_449_, 0);
                    v_tail_452_ = crate::leanh::lean_ctor_get(v_x_449_, 2);
                    v___x_453_ = lean_level_eq(v_key_451_, v_a_448_);
                    if v___x_453_ == 0 {
                        v_x_449_ = v_tail_452_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_453_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__1___redArg___boxed(
    mut v_a_455_: *mut crate::leanh::LeanObject,
    mut v_x_456_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_457_: u8 = 0;
    let mut v_r_458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_457_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__1___redArg(v_a_455_, v_x_456_);
    crate::leanh::lean_dec(v_x_456_);
    crate::leanh::lean_dec(v_a_455_);
    v_r_458_ = crate::leanh::lean_box((v_res_457_) as usize);
    return v_r_458_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0___redArg(
    mut v_m_459_: *mut crate::leanh::LeanObject,
    mut v_a_460_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_buckets_461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_463_: u64 = 0;
    let mut v___x_464_: u64 = 0;
    let mut v___x_465_: u64 = 0;
    let mut v_fold_466_: u64 = 0;
    let mut v___x_467_: u64 = 0;
    let mut v___x_468_: u64 = 0;
    let mut v___x_469_: u64 = 0;
    let mut v___x_470_: usize = 0;
    let mut v___x_471_: usize = 0;
    let mut v___x_472_: usize = 0;
    let mut v___x_473_: usize = 0;
    let mut v___x_474_: usize = 0;
    let mut v___x_475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_476_: u8 = 0;
    v_buckets_461_ = crate::leanh::lean_ctor_get(v_m_459_, 1);
    v___x_462_ = lean_array_get_size(v_buckets_461_);
    v___x_463_ = l_Lean_Level_hash(v_a_460_);
    v___x_464_ = 32u64;
    v___x_465_ = lean_uint64_shift_right(v___x_463_, v___x_464_);
    v_fold_466_ = lean_uint64_xor(v___x_463_, v___x_465_);
    v___x_467_ = 16u64;
    v___x_468_ = lean_uint64_shift_right(v_fold_466_, v___x_467_);
    v___x_469_ = lean_uint64_xor(v_fold_466_, v___x_468_);
    v___x_470_ = lean_uint64_to_usize(v___x_469_);
    v___x_471_ = lean_usize_of_nat(v___x_462_);
    v___x_472_ = 1usize;
    v___x_473_ = lean_usize_sub(v___x_471_, v___x_472_);
    v___x_474_ = lean_usize_land(v___x_470_, v___x_473_);
    v___x_475_ = lean_array_uget_borrowed(v_buckets_461_, v___x_474_);
    v___x_476_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__1___redArg(v_a_460_, v___x_475_);
    return v___x_476_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0___redArg___boxed(
    mut v_m_477_: *mut crate::leanh::LeanObject,
    mut v_a_478_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_479_: u8 = 0;
    let mut v_r_480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_479_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0___redArg(v_m_477_, v_a_478_);
    crate::leanh::lean_dec(v_a_478_);
    crate::leanh::lean_dec_ref(v_m_477_);
    v_r_480_ = crate::leanh::lean_box((v_res_479_) as usize);
    return v_r_480_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__1_spec__3_spec__4_spec__5___redArg(
    mut v_x_481_: *mut crate::leanh::LeanObject,
    mut v_x_482_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_488_: u8 = 0;
    let mut v___x_489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_490_: u64 = 0;
    let mut v___x_491_: u64 = 0;
    let mut v___x_492_: u64 = 0;
    let mut v_fold_493_: u64 = 0;
    let mut v___x_494_: u64 = 0;
    let mut v___x_495_: u64 = 0;
    let mut v___x_496_: u64 = 0;
    let mut v___x_497_: usize = 0;
    let mut v___x_498_: usize = 0;
    let mut v___x_499_: usize = 0;
    let mut v___x_500_: usize = 0;
    let mut v___x_501_: usize = 0;
    let mut v___x_502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_508_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_482_) == 0 {
                    return v_x_481_;
                } else {
                    v_key_483_ = crate::leanh::lean_ctor_get(v_x_482_, 0);
                    v_value_484_ = crate::leanh::lean_ctor_get(v_x_482_, 1);
                    v_tail_485_ = crate::leanh::lean_ctor_get(v_x_482_, 2);
                    v_isSharedCheck_508_ = (!crate::leanh::lean_is_exclusive(v_x_482_)) as u8;
                    if v_isSharedCheck_508_ == 0 {
                        v___x_487_ = v_x_482_;
                        v_isShared_488_ = v_isSharedCheck_508_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_485_);
                        crate::leanh::lean_inc(v_value_484_);
                        crate::leanh::lean_inc(v_key_483_);
                        crate::leanh::lean_dec(v_x_482_);
                        v___x_487_ = crate::leanh::lean_box(0);
                        v_isShared_488_ = v_isSharedCheck_508_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_489_ = lean_array_get_size(v_x_481_);
                v___x_490_ = l_Lean_Level_hash(v_key_483_);
                v___x_491_ = 32u64;
                v___x_492_ = lean_uint64_shift_right(v___x_490_, v___x_491_);
                v_fold_493_ = lean_uint64_xor(v___x_490_, v___x_492_);
                v___x_494_ = 16u64;
                v___x_495_ = lean_uint64_shift_right(v_fold_493_, v___x_494_);
                v___x_496_ = lean_uint64_xor(v_fold_493_, v___x_495_);
                v___x_497_ = lean_uint64_to_usize(v___x_496_);
                v___x_498_ = lean_usize_of_nat(v___x_489_);
                v___x_499_ = 1usize;
                v___x_500_ = lean_usize_sub(v___x_498_, v___x_499_);
                v___x_501_ = lean_usize_land(v___x_497_, v___x_500_);
                v___x_502_ = lean_array_uget_borrowed(v_x_481_, v___x_501_);
                crate::leanh::lean_inc(v___x_502_);
                if v_isShared_488_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_487_, 2, v___x_502_);
                    v___x_504_ = v___x_487_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_507_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_507_, 0, v_key_483_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_507_, 1, v_value_484_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_507_, 2, v___x_502_);
                    v___x_504_ = v_reuseFailAlloc_507_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_505_ = lean_array_uset(v_x_481_, v___x_501_, v___x_504_);
                v_x_481_ = v___x_505_;
                v_x_482_ = v_tail_485_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__1_spec__3_spec__4___redArg(
    mut v_i_509_: *mut crate::leanh::LeanObject,
    mut v_source_510_: *mut crate::leanh::LeanObject,
    mut v_target_511_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_513_: u8 = 0;
    let mut v_es_514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_512_ = lean_array_get_size(v_source_510_);
                v___x_513_ = lean_nat_dec_lt(v_i_509_, v___x_512_);
                if v___x_513_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_510_);
                    crate::leanh::lean_dec(v_i_509_);
                    return v_target_511_;
                } else {
                    v_es_514_ = lean_array_fget(v_source_510_, v_i_509_);
                    v___x_515_ = crate::leanh::lean_box(0);
                    v_source_516_ = lean_array_fset(v_source_510_, v_i_509_, v___x_515_);
                    v_target_517_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__1_spec__3_spec__4_spec__5___redArg(v_target_511_, v_es_514_);
                    v___x_518_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_519_ = lean_nat_add(v_i_509_, v___x_518_);
                    crate::leanh::lean_dec(v_i_509_);
                    v_i_509_ = v___x_519_;
                    v_source_510_ = v_source_516_;
                    v_target_511_ = v_target_517_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__1_spec__3___redArg(
    mut v_data_521_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_522_ = lean_array_get_size(v_data_521_);
    v___x_523_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_524_ = lean_nat_mul(v___x_522_, v___x_523_);
    v___x_525_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_526_ = crate::leanh::lean_box(0);
    v___x_527_ = lean_mk_array(v_nbuckets_524_, v___x_526_);
    v___x_528_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__1_spec__3_spec__4___redArg(v___x_525_, v_data_521_, v___x_527_);
    return v___x_528_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__1___redArg(
    mut v_m_529_: *mut crate::leanh::LeanObject,
    mut v_a_530_: *mut crate::leanh::LeanObject,
    mut v_b_531_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_535_: u64 = 0;
    let mut v___x_536_: u64 = 0;
    let mut v___x_537_: u64 = 0;
    let mut v_fold_538_: u64 = 0;
    let mut v___x_539_: u64 = 0;
    let mut v___x_540_: u64 = 0;
    let mut v___x_541_: u64 = 0;
    let mut v___x_542_: usize = 0;
    let mut v___x_543_: usize = 0;
    let mut v___x_544_: usize = 0;
    let mut v___x_545_: usize = 0;
    let mut v___x_546_: usize = 0;
    let mut v_bkt_547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_548_: u8 = 0;
    let mut v___x_550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_551_: u8 = 0;
    let mut v___x_552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_561_: u8 = 0;
    let mut v_val_562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_569_: u8 = 0;
    let mut v_unused_570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_532_ = crate::leanh::lean_ctor_get(v_m_529_, 0);
                v_buckets_533_ = crate::leanh::lean_ctor_get(v_m_529_, 1);
                v___x_534_ = lean_array_get_size(v_buckets_533_);
                v___x_535_ = l_Lean_Level_hash(v_a_530_);
                v___x_536_ = 32u64;
                v___x_537_ = lean_uint64_shift_right(v___x_535_, v___x_536_);
                v_fold_538_ = lean_uint64_xor(v___x_535_, v___x_537_);
                v___x_539_ = 16u64;
                v___x_540_ = lean_uint64_shift_right(v_fold_538_, v___x_539_);
                v___x_541_ = lean_uint64_xor(v_fold_538_, v___x_540_);
                v___x_542_ = lean_uint64_to_usize(v___x_541_);
                v___x_543_ = lean_usize_of_nat(v___x_534_);
                v___x_544_ = 1usize;
                v___x_545_ = lean_usize_sub(v___x_543_, v___x_544_);
                v___x_546_ = lean_usize_land(v___x_542_, v___x_545_);
                v_bkt_547_ = lean_array_uget_borrowed(v_buckets_533_, v___x_546_);
                v___x_548_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__1___redArg(v_a_530_, v_bkt_547_);
                if v___x_548_ == 0 {
                    crate::leanh::lean_inc_ref(v_buckets_533_);
                    crate::leanh::lean_inc(v_size_532_);
                    v_isSharedCheck_569_ = (!crate::leanh::lean_is_exclusive(v_m_529_)) as u8;
                    if v_isSharedCheck_569_ == 0 {
                        v_unused_570_ = crate::leanh::lean_ctor_get(v_m_529_, 1);
                        crate::leanh::lean_dec(v_unused_570_);
                        v_unused_571_ = crate::leanh::lean_ctor_get(v_m_529_, 0);
                        crate::leanh::lean_dec(v_unused_571_);
                        v___x_550_ = v_m_529_;
                        v_isShared_551_ = v_isSharedCheck_569_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_529_);
                        v___x_550_ = crate::leanh::lean_box(0);
                        v_isShared_551_ = v_isSharedCheck_569_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_b_531_);
                    crate::leanh::lean_dec(v_a_530_);
                    return v_m_529_;
                }
            }
            1 => {
                v___x_552_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_553_ = lean_nat_add(v_size_532_, v___x_552_);
                crate::leanh::lean_dec(v_size_532_);
                crate::leanh::lean_inc(v_bkt_547_);
                v___x_554_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_554_, 0, v_a_530_);
                crate::leanh::lean_ctor_set(v___x_554_, 1, v_b_531_);
                crate::leanh::lean_ctor_set(v___x_554_, 2, v_bkt_547_);
                v_buckets_x27_555_ = lean_array_uset(v_buckets_533_, v___x_546_, v___x_554_);
                v___x_556_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_557_ = lean_nat_mul(v_size_x27_553_, v___x_556_);
                v___x_558_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_559_ = lean_nat_div(v___x_557_, v___x_558_);
                crate::leanh::lean_dec(v___x_557_);
                v___x_560_ = lean_array_get_size(v_buckets_x27_555_);
                v___x_561_ = lean_nat_dec_le(v___x_559_, v___x_560_);
                crate::leanh::lean_dec(v___x_559_);
                if v___x_561_ == 0 {
                    v_val_562_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__1_spec__3___redArg(v_buckets_x27_555_);
                    if v_isShared_551_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_550_, 1, v_val_562_);
                        crate::leanh::lean_ctor_set(v___x_550_, 0, v_size_x27_553_);
                        v___x_564_ = v___x_550_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_565_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_565_, 0, v_size_x27_553_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_565_, 1, v_val_562_);
                        v___x_564_ = v_reuseFailAlloc_565_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_551_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_550_, 1, v_buckets_x27_555_);
                        crate::leanh::lean_ctor_set(v___x_550_, 0, v_size_x27_553_);
                        v___x_567_ = v___x_550_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_568_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_568_, 0, v_size_x27_553_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_568_, 1, v_buckets_x27_555_);
                        v___x_567_ = v_reuseFailAlloc_568_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_564_;
            }
            3 => {
                return v___x_567_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_CollectLevelMVars_collect(
    mut v_x_572_: *mut crate::leanh::LeanObject,
    mut v_a_573_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_u_575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_visitedLevel_587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_visitedExpr_588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_592_: u8 = 0;
    let mut v___x_593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_597_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_572_) {
                1 => {
                    v_a_580_ = crate::leanh::lean_ctor_get(v_x_572_, 0);
                    crate::leanh::lean_inc(v_a_580_);
                    crate::leanh::lean_dec_ref_known(v_x_572_, 1);
                    v___x_581_ = l_Lean_CollectLevelMVars_visitLevel(v_a_580_, v_a_573_);
                    return v___x_581_;
                }
                2 => {
                    v_a_582_ = crate::leanh::lean_ctor_get(v_x_572_, 0);
                    crate::leanh::lean_inc(v_a_582_);
                    v_a_583_ = crate::leanh::lean_ctor_get(v_x_572_, 1);
                    crate::leanh::lean_inc(v_a_583_);
                    crate::leanh::lean_dec_ref_known(v_x_572_, 2);
                    v_u_575_ = v_a_582_;
                    v_v_576_ = v_a_583_;
                    v___y_577_ = v_a_573_;
                    state = 1;
                    continue;
                }
                3 => {
                    v_a_584_ = crate::leanh::lean_ctor_get(v_x_572_, 0);
                    crate::leanh::lean_inc(v_a_584_);
                    v_a_585_ = crate::leanh::lean_ctor_get(v_x_572_, 1);
                    crate::leanh::lean_inc(v_a_585_);
                    crate::leanh::lean_dec_ref_known(v_x_572_, 2);
                    v_u_575_ = v_a_584_;
                    v_v_576_ = v_a_585_;
                    v___y_577_ = v_a_573_;
                    state = 1;
                    continue;
                }
                5 => {
                    v_a_586_ = crate::leanh::lean_ctor_get(v_x_572_, 0);
                    crate::leanh::lean_inc(v_a_586_);
                    crate::leanh::lean_dec_ref_known(v_x_572_, 1);
                    v_visitedLevel_587_ = crate::leanh::lean_ctor_get(v_a_573_, 0);
                    v_visitedExpr_588_ = crate::leanh::lean_ctor_get(v_a_573_, 1);
                    v_result_589_ = crate::leanh::lean_ctor_get(v_a_573_, 2);
                    v_isSharedCheck_597_ = (!crate::leanh::lean_is_exclusive(v_a_573_)) as u8;
                    if v_isSharedCheck_597_ == 0 {
                        v___x_591_ = v_a_573_;
                        v_isShared_592_ = v_isSharedCheck_597_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_result_589_);
                        crate::leanh::lean_inc(v_visitedExpr_588_);
                        crate::leanh::lean_inc(v_visitedLevel_587_);
                        crate::leanh::lean_dec(v_a_573_);
                        v___x_591_ = crate::leanh::lean_box(0);
                        v_isShared_592_ = v_isSharedCheck_597_;
                        state = 2;
                        continue;
                    }
                }
                _ => {
                    crate::leanh::lean_dec(v_x_572_);
                    return v_a_573_;
                }
            },
            1 => {
                v___x_578_ = l_Lean_CollectLevelMVars_visitLevel(v_u_575_, v___y_577_);
                v___x_579_ = l_Lean_CollectLevelMVars_visitLevel(v_v_576_, v___x_578_);
                return v___x_579_;
            }
            2 => {
                v___x_593_ = lean_array_push(v_result_589_, v_a_586_);
                if v_isShared_592_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_591_, 2, v___x_593_);
                    v___x_595_ = v___x_591_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_596_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_596_, 0, v_visitedLevel_587_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_596_, 1, v_visitedExpr_588_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_596_, 2, v___x_593_);
                    v___x_595_ = v_reuseFailAlloc_596_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_595_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_CollectLevelMVars_visitLevel(
    mut v_u_598_: *mut crate::leanh::LeanObject,
    mut v_s_599_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_600_: u8 = 0;
    let mut v_visitedLevel_601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_visitedExpr_602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_604_: u8 = 0;
    let mut v___x_606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_607_: u8 = 0;
    let mut v___x_608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_614_: u8 = 0;
    let mut v_unused_615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_600_ = l_Lean_Level_hasMVar(v_u_598_);
                if v___x_600_ == 0 {
                    crate::leanh::lean_dec(v_u_598_);
                    return v_s_599_;
                } else {
                    v_visitedLevel_601_ = crate::leanh::lean_ctor_get(v_s_599_, 0);
                    v_visitedExpr_602_ = crate::leanh::lean_ctor_get(v_s_599_, 1);
                    v_result_603_ = crate::leanh::lean_ctor_get(v_s_599_, 2);
                    v___x_604_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0___redArg(v_visitedLevel_601_, v_u_598_);
                    if v___x_604_ == 0 {
                        crate::leanh::lean_inc_ref(v_result_603_);
                        crate::leanh::lean_inc_ref(v_visitedExpr_602_);
                        crate::leanh::lean_inc_ref(v_visitedLevel_601_);
                        v_isSharedCheck_614_ = (!crate::leanh::lean_is_exclusive(v_s_599_)) as u8;
                        if v_isSharedCheck_614_ == 0 {
                            v_unused_615_ = crate::leanh::lean_ctor_get(v_s_599_, 2);
                            crate::leanh::lean_dec(v_unused_615_);
                            v_unused_616_ = crate::leanh::lean_ctor_get(v_s_599_, 1);
                            crate::leanh::lean_dec(v_unused_616_);
                            v_unused_617_ = crate::leanh::lean_ctor_get(v_s_599_, 0);
                            crate::leanh::lean_dec(v_unused_617_);
                            v___x_606_ = v_s_599_;
                            v_isShared_607_ = v_isSharedCheck_614_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_s_599_);
                            v___x_606_ = crate::leanh::lean_box(0);
                            v_isShared_607_ = v_isSharedCheck_614_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_u_598_);
                        return v_s_599_;
                    }
                }
            }
            1 => {
                v___x_608_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v_u_598_);
                v___x_609_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__1___redArg(v_visitedLevel_601_, v_u_598_, v___x_608_);
                if v_isShared_607_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_606_, 0, v___x_609_);
                    v___x_611_ = v___x_606_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_613_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_613_, 0, v___x_609_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_613_, 1, v_visitedExpr_602_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_613_, 2, v_result_603_);
                    v___x_611_ = v_reuseFailAlloc_613_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_612_ = l_Lean_CollectLevelMVars_collect(v_u_598_, v___x_611_);
                return v___x_612_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0(
    mut v_00_u03b2_618_: *mut crate::leanh::LeanObject,
    mut v_m_619_: *mut crate::leanh::LeanObject,
    mut v_a_620_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_621_: u8 = 0;
    v___x_621_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0___redArg(v_m_619_, v_a_620_);
    return v___x_621_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0___boxed(
    mut v_00_u03b2_622_: *mut crate::leanh::LeanObject,
    mut v_m_623_: *mut crate::leanh::LeanObject,
    mut v_a_624_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_625_: u8 = 0;
    let mut v_r_626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_625_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0(v_00_u03b2_622_, v_m_623_, v_a_624_);
    crate::leanh::lean_dec(v_a_624_);
    crate::leanh::lean_dec_ref(v_m_623_);
    v_r_626_ = crate::leanh::lean_box((v_res_625_) as usize);
    return v_r_626_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__1(
    mut v_00_u03b2_627_: *mut crate::leanh::LeanObject,
    mut v_m_628_: *mut crate::leanh::LeanObject,
    mut v_a_629_: *mut crate::leanh::LeanObject,
    mut v_b_630_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_631_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__1___redArg(v_m_628_, v_a_629_, v_b_630_);
    return v___x_631_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__1(
    mut v_00_u03b2_632_: *mut crate::leanh::LeanObject,
    mut v_a_633_: *mut crate::leanh::LeanObject,
    mut v_x_634_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_635_: u8 = 0;
    v___x_635_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__1___redArg(v_a_633_, v_x_634_);
    return v___x_635_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__1___boxed(
    mut v_00_u03b2_636_: *mut crate::leanh::LeanObject,
    mut v_a_637_: *mut crate::leanh::LeanObject,
    mut v_x_638_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_639_: u8 = 0;
    let mut v_r_640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_639_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitLevel_spec__0_spec__1(v_00_u03b2_636_, v_a_637_, v_x_638_);
    crate::leanh::lean_dec(v_x_638_);
    crate::leanh::lean_dec(v_a_637_);
    v_r_640_ = crate::leanh::lean_box((v_res_639_) as usize);
    return v_r_640_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__1_spec__3(
    mut v_00_u03b2_641_: *mut crate::leanh::LeanObject,
    mut v_data_642_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_643_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__1_spec__3___redArg(v_data_642_);
    return v___x_643_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__1_spec__3_spec__4(
    mut v_00_u03b2_644_: *mut crate::leanh::LeanObject,
    mut v_i_645_: *mut crate::leanh::LeanObject,
    mut v_source_646_: *mut crate::leanh::LeanObject,
    mut v_target_647_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_648_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__1_spec__3_spec__4___redArg(v_i_645_, v_source_646_, v_target_647_);
    return v___x_648_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__1_spec__3_spec__4_spec__5(
    mut v_00_u03b2_649_: *mut crate::leanh::LeanObject,
    mut v_x_650_: *mut crate::leanh::LeanObject,
    mut v_x_651_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_652_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitLevel_spec__1_spec__3_spec__4_spec__5___redArg(v_x_650_, v_x_651_);
    return v___x_652_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1_spec__2_spec__4_spec__6___redArg(
    mut v_x_653_: *mut crate::leanh::LeanObject,
    mut v_x_654_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_660_: u8 = 0;
    let mut v___x_661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_662_: u64 = 0;
    let mut v___x_663_: u64 = 0;
    let mut v___x_664_: u64 = 0;
    let mut v_fold_665_: u64 = 0;
    let mut v___x_666_: u64 = 0;
    let mut v___x_667_: u64 = 0;
    let mut v___x_668_: u64 = 0;
    let mut v___x_669_: usize = 0;
    let mut v___x_670_: usize = 0;
    let mut v___x_671_: usize = 0;
    let mut v___x_672_: usize = 0;
    let mut v___x_673_: usize = 0;
    let mut v___x_674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_680_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_654_) == 0 {
                    return v_x_653_;
                } else {
                    v_key_655_ = crate::leanh::lean_ctor_get(v_x_654_, 0);
                    v_value_656_ = crate::leanh::lean_ctor_get(v_x_654_, 1);
                    v_tail_657_ = crate::leanh::lean_ctor_get(v_x_654_, 2);
                    v_isSharedCheck_680_ = (!crate::leanh::lean_is_exclusive(v_x_654_)) as u8;
                    if v_isSharedCheck_680_ == 0 {
                        v___x_659_ = v_x_654_;
                        v_isShared_660_ = v_isSharedCheck_680_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_657_);
                        crate::leanh::lean_inc(v_value_656_);
                        crate::leanh::lean_inc(v_key_655_);
                        crate::leanh::lean_dec(v_x_654_);
                        v___x_659_ = crate::leanh::lean_box(0);
                        v_isShared_660_ = v_isSharedCheck_680_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_661_ = lean_array_get_size(v_x_653_);
                v___x_662_ = l_Lean_Expr_hash(v_key_655_);
                v___x_663_ = 32u64;
                v___x_664_ = lean_uint64_shift_right(v___x_662_, v___x_663_);
                v_fold_665_ = lean_uint64_xor(v___x_662_, v___x_664_);
                v___x_666_ = 16u64;
                v___x_667_ = lean_uint64_shift_right(v_fold_665_, v___x_666_);
                v___x_668_ = lean_uint64_xor(v_fold_665_, v___x_667_);
                v___x_669_ = lean_uint64_to_usize(v___x_668_);
                v___x_670_ = lean_usize_of_nat(v___x_661_);
                v___x_671_ = 1usize;
                v___x_672_ = lean_usize_sub(v___x_670_, v___x_671_);
                v___x_673_ = lean_usize_land(v___x_669_, v___x_672_);
                v___x_674_ = lean_array_uget_borrowed(v_x_653_, v___x_673_);
                crate::leanh::lean_inc(v___x_674_);
                if v_isShared_660_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_659_, 2, v___x_674_);
                    v___x_676_ = v___x_659_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_679_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_679_, 0, v_key_655_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_679_, 1, v_value_656_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_679_, 2, v___x_674_);
                    v___x_676_ = v_reuseFailAlloc_679_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_677_ = lean_array_uset(v_x_653_, v___x_673_, v___x_676_);
                v_x_653_ = v___x_677_;
                v_x_654_ = v_tail_657_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1_spec__2_spec__4___redArg(
    mut v_i_681_: *mut crate::leanh::LeanObject,
    mut v_source_682_: *mut crate::leanh::LeanObject,
    mut v_target_683_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_685_: u8 = 0;
    let mut v_es_686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_684_ = lean_array_get_size(v_source_682_);
                v___x_685_ = lean_nat_dec_lt(v_i_681_, v___x_684_);
                if v___x_685_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_682_);
                    crate::leanh::lean_dec(v_i_681_);
                    return v_target_683_;
                } else {
                    v_es_686_ = lean_array_fget(v_source_682_, v_i_681_);
                    v___x_687_ = crate::leanh::lean_box(0);
                    v_source_688_ = lean_array_fset(v_source_682_, v_i_681_, v___x_687_);
                    v_target_689_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1_spec__2_spec__4_spec__6___redArg(v_target_683_, v_es_686_);
                    v___x_690_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_691_ = lean_nat_add(v_i_681_, v___x_690_);
                    crate::leanh::lean_dec(v_i_681_);
                    v_i_681_ = v___x_691_;
                    v_source_682_ = v_source_688_;
                    v_target_683_ = v_target_689_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1_spec__2___redArg(
    mut v_data_693_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_694_ = lean_array_get_size(v_data_693_);
    v___x_695_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_696_ = lean_nat_mul(v___x_694_, v___x_695_);
    v___x_697_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_698_ = crate::leanh::lean_box(0);
    v___x_699_ = lean_mk_array(v_nbuckets_696_, v___x_698_);
    v___x_700_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1_spec__2_spec__4___redArg(v___x_697_, v_data_693_, v___x_699_);
    return v___x_700_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0_spec__0___redArg(
    mut v_a_701_: *mut crate::leanh::LeanObject,
    mut v_x_702_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_703_: u8 = 0;
    let mut v_key_704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_706_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_702_) == 0 {
                    v___x_703_ = 0;
                    return v___x_703_;
                } else {
                    v_key_704_ = crate::leanh::lean_ctor_get(v_x_702_, 0);
                    v_tail_705_ = crate::leanh::lean_ctor_get(v_x_702_, 2);
                    v___x_706_ = lean_expr_eqv(v_key_704_, v_a_701_);
                    if v___x_706_ == 0 {
                        v_x_702_ = v_tail_705_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_706_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0_spec__0___redArg___boxed(
    mut v_a_708_: *mut crate::leanh::LeanObject,
    mut v_x_709_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_710_: u8 = 0;
    let mut v_r_711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_710_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0_spec__0___redArg(v_a_708_, v_x_709_);
    crate::leanh::lean_dec(v_x_709_);
    crate::leanh::lean_dec_ref(v_a_708_);
    v_r_711_ = crate::leanh::lean_box((v_res_710_) as usize);
    return v_r_711_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1___redArg(
    mut v_m_712_: *mut crate::leanh::LeanObject,
    mut v_a_713_: *mut crate::leanh::LeanObject,
    mut v_b_714_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_718_: u64 = 0;
    let mut v___x_719_: u64 = 0;
    let mut v___x_720_: u64 = 0;
    let mut v_fold_721_: u64 = 0;
    let mut v___x_722_: u64 = 0;
    let mut v___x_723_: u64 = 0;
    let mut v___x_724_: u64 = 0;
    let mut v___x_725_: usize = 0;
    let mut v___x_726_: usize = 0;
    let mut v___x_727_: usize = 0;
    let mut v___x_728_: usize = 0;
    let mut v___x_729_: usize = 0;
    let mut v_bkt_730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_731_: u8 = 0;
    let mut v___x_733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_734_: u8 = 0;
    let mut v___x_735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_744_: u8 = 0;
    let mut v_val_745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_752_: u8 = 0;
    let mut v_unused_753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_715_ = crate::leanh::lean_ctor_get(v_m_712_, 0);
                v_buckets_716_ = crate::leanh::lean_ctor_get(v_m_712_, 1);
                v___x_717_ = lean_array_get_size(v_buckets_716_);
                v___x_718_ = l_Lean_Expr_hash(v_a_713_);
                v___x_719_ = 32u64;
                v___x_720_ = lean_uint64_shift_right(v___x_718_, v___x_719_);
                v_fold_721_ = lean_uint64_xor(v___x_718_, v___x_720_);
                v___x_722_ = 16u64;
                v___x_723_ = lean_uint64_shift_right(v_fold_721_, v___x_722_);
                v___x_724_ = lean_uint64_xor(v_fold_721_, v___x_723_);
                v___x_725_ = lean_uint64_to_usize(v___x_724_);
                v___x_726_ = lean_usize_of_nat(v___x_717_);
                v___x_727_ = 1usize;
                v___x_728_ = lean_usize_sub(v___x_726_, v___x_727_);
                v___x_729_ = lean_usize_land(v___x_725_, v___x_728_);
                v_bkt_730_ = lean_array_uget_borrowed(v_buckets_716_, v___x_729_);
                v___x_731_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0_spec__0___redArg(v_a_713_, v_bkt_730_);
                if v___x_731_ == 0 {
                    crate::leanh::lean_inc_ref(v_buckets_716_);
                    crate::leanh::lean_inc(v_size_715_);
                    v_isSharedCheck_752_ = (!crate::leanh::lean_is_exclusive(v_m_712_)) as u8;
                    if v_isSharedCheck_752_ == 0 {
                        v_unused_753_ = crate::leanh::lean_ctor_get(v_m_712_, 1);
                        crate::leanh::lean_dec(v_unused_753_);
                        v_unused_754_ = crate::leanh::lean_ctor_get(v_m_712_, 0);
                        crate::leanh::lean_dec(v_unused_754_);
                        v___x_733_ = v_m_712_;
                        v_isShared_734_ = v_isSharedCheck_752_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_712_);
                        v___x_733_ = crate::leanh::lean_box(0);
                        v_isShared_734_ = v_isSharedCheck_752_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_b_714_);
                    crate::leanh::lean_dec_ref(v_a_713_);
                    return v_m_712_;
                }
            }
            1 => {
                v___x_735_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_736_ = lean_nat_add(v_size_715_, v___x_735_);
                crate::leanh::lean_dec(v_size_715_);
                crate::leanh::lean_inc(v_bkt_730_);
                v___x_737_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_737_, 0, v_a_713_);
                crate::leanh::lean_ctor_set(v___x_737_, 1, v_b_714_);
                crate::leanh::lean_ctor_set(v___x_737_, 2, v_bkt_730_);
                v_buckets_x27_738_ = lean_array_uset(v_buckets_716_, v___x_729_, v___x_737_);
                v___x_739_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_740_ = lean_nat_mul(v_size_x27_736_, v___x_739_);
                v___x_741_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_742_ = lean_nat_div(v___x_740_, v___x_741_);
                crate::leanh::lean_dec(v___x_740_);
                v___x_743_ = lean_array_get_size(v_buckets_x27_738_);
                v___x_744_ = lean_nat_dec_le(v___x_742_, v___x_743_);
                crate::leanh::lean_dec(v___x_742_);
                if v___x_744_ == 0 {
                    v_val_745_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1_spec__2___redArg(v_buckets_x27_738_);
                    if v_isShared_734_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_733_, 1, v_val_745_);
                        crate::leanh::lean_ctor_set(v___x_733_, 0, v_size_x27_736_);
                        v___x_747_ = v___x_733_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_748_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_748_, 0, v_size_x27_736_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_748_, 1, v_val_745_);
                        v___x_747_ = v_reuseFailAlloc_748_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_734_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_733_, 1, v_buckets_x27_738_);
                        crate::leanh::lean_ctor_set(v___x_733_, 0, v_size_x27_736_);
                        v___x_750_ = v___x_733_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_751_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_751_, 0, v_size_x27_736_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_751_, 1, v_buckets_x27_738_);
                        v___x_750_ = v_reuseFailAlloc_751_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_747_;
            }
            3 => {
                return v___x_750_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0___redArg(
    mut v_m_755_: *mut crate::leanh::LeanObject,
    mut v_a_756_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_buckets_757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_759_: u64 = 0;
    let mut v___x_760_: u64 = 0;
    let mut v___x_761_: u64 = 0;
    let mut v_fold_762_: u64 = 0;
    let mut v___x_763_: u64 = 0;
    let mut v___x_764_: u64 = 0;
    let mut v___x_765_: u64 = 0;
    let mut v___x_766_: usize = 0;
    let mut v___x_767_: usize = 0;
    let mut v___x_768_: usize = 0;
    let mut v___x_769_: usize = 0;
    let mut v___x_770_: usize = 0;
    let mut v___x_771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_772_: u8 = 0;
    v_buckets_757_ = crate::leanh::lean_ctor_get(v_m_755_, 1);
    v___x_758_ = lean_array_get_size(v_buckets_757_);
    v___x_759_ = l_Lean_Expr_hash(v_a_756_);
    v___x_760_ = 32u64;
    v___x_761_ = lean_uint64_shift_right(v___x_759_, v___x_760_);
    v_fold_762_ = lean_uint64_xor(v___x_759_, v___x_761_);
    v___x_763_ = 16u64;
    v___x_764_ = lean_uint64_shift_right(v_fold_762_, v___x_763_);
    v___x_765_ = lean_uint64_xor(v_fold_762_, v___x_764_);
    v___x_766_ = lean_uint64_to_usize(v___x_765_);
    v___x_767_ = lean_usize_of_nat(v___x_758_);
    v___x_768_ = 1usize;
    v___x_769_ = lean_usize_sub(v___x_767_, v___x_768_);
    v___x_770_ = lean_usize_land(v___x_766_, v___x_769_);
    v___x_771_ = lean_array_uget_borrowed(v_buckets_757_, v___x_770_);
    v___x_772_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0_spec__0___redArg(v_a_756_, v___x_771_);
    return v___x_772_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0___redArg___boxed(
    mut v_m_773_: *mut crate::leanh::LeanObject,
    mut v_a_774_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_775_: u8 = 0;
    let mut v_r_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_775_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0___redArg(v_m_773_, v_a_774_);
    crate::leanh::lean_dec_ref(v_a_774_);
    crate::leanh::lean_dec_ref(v_m_773_);
    v_r_776_ = crate::leanh::lean_box((v_res_775_) as usize);
    return v_r_776_;
}
pub unsafe fn l_List_foldl___at___00Lean_CollectLevelMVars_main_spec__3(
    mut v_x_777_: *mut crate::leanh::LeanObject,
    mut v_x_778_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_778_) == 0 {
                    return v_x_777_;
                } else {
                    v_head_779_ = crate::leanh::lean_ctor_get(v_x_778_, 0);
                    crate::leanh::lean_inc(v_head_779_);
                    v_tail_780_ = crate::leanh::lean_ctor_get(v_x_778_, 1);
                    crate::leanh::lean_inc(v_tail_780_);
                    crate::leanh::lean_dec_ref_known(v_x_778_, 2);
                    v___x_781_ = l_Lean_CollectLevelMVars_visitLevel(v_head_779_, v_x_777_);
                    v_x_777_ = v___x_781_;
                    v_x_778_ = v_tail_780_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_CollectLevelMVars_main(
    mut v_x_783_: *mut crate::leanh::LeanObject,
    mut v_a_784_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_d_786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_783_) {
                11 => {
                    v_struct_791_ = crate::leanh::lean_ctor_get(v_x_783_, 2);
                    crate::leanh::lean_inc_ref(v_struct_791_);
                    crate::leanh::lean_dec_ref_known(v_x_783_, 3);
                    v___x_792_ = l_Lean_CollectLevelMVars_visitExpr(v_struct_791_, v_a_784_);
                    return v___x_792_;
                }
                7 => {
                    v_binderType_793_ = crate::leanh::lean_ctor_get(v_x_783_, 1);
                    crate::leanh::lean_inc_ref(v_binderType_793_);
                    v_body_794_ = crate::leanh::lean_ctor_get(v_x_783_, 2);
                    crate::leanh::lean_inc_ref(v_body_794_);
                    crate::leanh::lean_dec_ref_known(v_x_783_, 3);
                    v_d_786_ = v_binderType_793_;
                    v_b_787_ = v_body_794_;
                    v___y_788_ = v_a_784_;
                    state = 1;
                    continue;
                }
                6 => {
                    v_binderType_795_ = crate::leanh::lean_ctor_get(v_x_783_, 1);
                    crate::leanh::lean_inc_ref(v_binderType_795_);
                    v_body_796_ = crate::leanh::lean_ctor_get(v_x_783_, 2);
                    crate::leanh::lean_inc_ref(v_body_796_);
                    crate::leanh::lean_dec_ref_known(v_x_783_, 3);
                    v_d_786_ = v_binderType_795_;
                    v_b_787_ = v_body_796_;
                    v___y_788_ = v_a_784_;
                    state = 1;
                    continue;
                }
                8 => {
                    v_type_797_ = crate::leanh::lean_ctor_get(v_x_783_, 1);
                    crate::leanh::lean_inc_ref(v_type_797_);
                    v_value_798_ = crate::leanh::lean_ctor_get(v_x_783_, 2);
                    crate::leanh::lean_inc_ref(v_value_798_);
                    v_body_799_ = crate::leanh::lean_ctor_get(v_x_783_, 3);
                    crate::leanh::lean_inc_ref(v_body_799_);
                    crate::leanh::lean_dec_ref_known(v_x_783_, 4);
                    v___x_800_ = l_Lean_CollectLevelMVars_visitExpr(v_type_797_, v_a_784_);
                    v___x_801_ = l_Lean_CollectLevelMVars_visitExpr(v_value_798_, v___x_800_);
                    v___x_802_ = l_Lean_CollectLevelMVars_visitExpr(v_body_799_, v___x_801_);
                    return v___x_802_;
                }
                5 => {
                    v_fn_803_ = crate::leanh::lean_ctor_get(v_x_783_, 0);
                    crate::leanh::lean_inc_ref(v_fn_803_);
                    v_arg_804_ = crate::leanh::lean_ctor_get(v_x_783_, 1);
                    crate::leanh::lean_inc_ref(v_arg_804_);
                    crate::leanh::lean_dec_ref_known(v_x_783_, 2);
                    v___x_805_ = l_Lean_CollectLevelMVars_visitExpr(v_fn_803_, v_a_784_);
                    v___x_806_ = l_Lean_CollectLevelMVars_visitExpr(v_arg_804_, v___x_805_);
                    return v___x_806_;
                }
                10 => {
                    v_expr_807_ = crate::leanh::lean_ctor_get(v_x_783_, 1);
                    crate::leanh::lean_inc_ref(v_expr_807_);
                    crate::leanh::lean_dec_ref_known(v_x_783_, 2);
                    v___x_808_ = l_Lean_CollectLevelMVars_visitExpr(v_expr_807_, v_a_784_);
                    return v___x_808_;
                }
                4 => {
                    v_us_809_ = crate::leanh::lean_ctor_get(v_x_783_, 1);
                    crate::leanh::lean_inc(v_us_809_);
                    crate::leanh::lean_dec_ref_known(v_x_783_, 2);
                    v___x_810_ = l_List_foldl___at___00Lean_CollectLevelMVars_main_spec__3(
                        v_a_784_, v_us_809_,
                    );
                    return v___x_810_;
                }
                3 => {
                    v_u_811_ = crate::leanh::lean_ctor_get(v_x_783_, 0);
                    crate::leanh::lean_inc(v_u_811_);
                    crate::leanh::lean_dec_ref_known(v_x_783_, 1);
                    v___x_812_ = l_Lean_CollectLevelMVars_visitLevel(v_u_811_, v_a_784_);
                    return v___x_812_;
                }
                _ => {
                    crate::leanh::lean_dec_ref(v_x_783_);
                    return v_a_784_;
                }
            },
            1 => {
                v___x_789_ = l_Lean_CollectLevelMVars_visitExpr(v_d_786_, v___y_788_);
                v___x_790_ = l_Lean_CollectLevelMVars_visitExpr(v_b_787_, v___x_789_);
                return v___x_790_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_CollectLevelMVars_visitExpr(
    mut v_e_813_: *mut crate::leanh::LeanObject,
    mut v_s_814_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_815_: u8 = 0;
    let mut v_visitedLevel_816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_visitedExpr_817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_819_: u8 = 0;
    let mut v___x_821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_822_: u8 = 0;
    let mut v___x_823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_829_: u8 = 0;
    let mut v_unused_830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_815_ = l_Lean_Expr_hasMVar(v_e_813_);
                if v___x_815_ == 0 {
                    crate::leanh::lean_dec_ref(v_e_813_);
                    return v_s_814_;
                } else {
                    v_visitedLevel_816_ = crate::leanh::lean_ctor_get(v_s_814_, 0);
                    v_visitedExpr_817_ = crate::leanh::lean_ctor_get(v_s_814_, 1);
                    v_result_818_ = crate::leanh::lean_ctor_get(v_s_814_, 2);
                    v___x_819_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0___redArg(v_visitedExpr_817_, v_e_813_);
                    if v___x_819_ == 0 {
                        crate::leanh::lean_inc_ref(v_result_818_);
                        crate::leanh::lean_inc_ref(v_visitedExpr_817_);
                        crate::leanh::lean_inc_ref(v_visitedLevel_816_);
                        v_isSharedCheck_829_ = (!crate::leanh::lean_is_exclusive(v_s_814_)) as u8;
                        if v_isSharedCheck_829_ == 0 {
                            v_unused_830_ = crate::leanh::lean_ctor_get(v_s_814_, 2);
                            crate::leanh::lean_dec(v_unused_830_);
                            v_unused_831_ = crate::leanh::lean_ctor_get(v_s_814_, 1);
                            crate::leanh::lean_dec(v_unused_831_);
                            v_unused_832_ = crate::leanh::lean_ctor_get(v_s_814_, 0);
                            crate::leanh::lean_dec(v_unused_832_);
                            v___x_821_ = v_s_814_;
                            v_isShared_822_ = v_isSharedCheck_829_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_s_814_);
                            v___x_821_ = crate::leanh::lean_box(0);
                            v_isShared_822_ = v_isSharedCheck_829_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_813_);
                        return v_s_814_;
                    }
                }
            }
            1 => {
                v___x_823_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc_ref(v_e_813_);
                v___x_824_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1___redArg(v_visitedExpr_817_, v_e_813_, v___x_823_);
                if v_isShared_822_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_821_, 1, v___x_824_);
                    v___x_826_ = v___x_821_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_828_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_828_, 0, v_visitedLevel_816_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_828_, 1, v___x_824_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_828_, 2, v_result_818_);
                    v___x_826_ = v_reuseFailAlloc_828_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_827_ = l_Lean_CollectLevelMVars_main(v_e_813_, v___x_826_);
                return v___x_827_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0(
    mut v_00_u03b2_833_: *mut crate::leanh::LeanObject,
    mut v_m_834_: *mut crate::leanh::LeanObject,
    mut v_a_835_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_836_: u8 = 0;
    v___x_836_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0___redArg(v_m_834_, v_a_835_);
    return v___x_836_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0___boxed(
    mut v_00_u03b2_837_: *mut crate::leanh::LeanObject,
    mut v_m_838_: *mut crate::leanh::LeanObject,
    mut v_a_839_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_840_: u8 = 0;
    let mut v_r_841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_840_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0(v_00_u03b2_837_, v_m_838_, v_a_839_);
    crate::leanh::lean_dec_ref(v_a_839_);
    crate::leanh::lean_dec_ref(v_m_838_);
    v_r_841_ = crate::leanh::lean_box((v_res_840_) as usize);
    return v_r_841_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1(
    mut v_00_u03b2_842_: *mut crate::leanh::LeanObject,
    mut v_m_843_: *mut crate::leanh::LeanObject,
    mut v_a_844_: *mut crate::leanh::LeanObject,
    mut v_b_845_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_846_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1___redArg(v_m_843_, v_a_844_, v_b_845_);
    return v___x_846_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0_spec__0(
    mut v_00_u03b2_847_: *mut crate::leanh::LeanObject,
    mut v_a_848_: *mut crate::leanh::LeanObject,
    mut v_x_849_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_850_: u8 = 0;
    v___x_850_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0_spec__0___redArg(v_a_848_, v_x_849_);
    return v___x_850_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0_spec__0___boxed(
    mut v_00_u03b2_851_: *mut crate::leanh::LeanObject,
    mut v_a_852_: *mut crate::leanh::LeanObject,
    mut v_x_853_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_854_: u8 = 0;
    let mut v_r_855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_854_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelMVars_visitExpr_spec__0_spec__0(v_00_u03b2_851_, v_a_852_, v_x_853_);
    crate::leanh::lean_dec(v_x_853_);
    crate::leanh::lean_dec_ref(v_a_852_);
    v_r_855_ = crate::leanh::lean_box((v_res_854_) as usize);
    return v_r_855_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1_spec__2(
    mut v_00_u03b2_856_: *mut crate::leanh::LeanObject,
    mut v_data_857_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_858_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1_spec__2___redArg(v_data_857_);
    return v___x_858_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1_spec__2_spec__4(
    mut v_00_u03b2_859_: *mut crate::leanh::LeanObject,
    mut v_i_860_: *mut crate::leanh::LeanObject,
    mut v_source_861_: *mut crate::leanh::LeanObject,
    mut v_target_862_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_863_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1_spec__2_spec__4___redArg(v_i_860_, v_source_861_, v_target_862_);
    return v___x_863_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1_spec__2_spec__4_spec__6(
    mut v_00_u03b2_864_: *mut crate::leanh::LeanObject,
    mut v_x_865_: *mut crate::leanh::LeanObject,
    mut v_x_866_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_867_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelMVars_visitExpr_spec__1_spec__2_spec__4_spec__6___redArg(v_x_865_, v_x_866_);
    return v___x_867_;
}
pub unsafe fn l_Lean_collectLevelMVars(
    mut v_s_868_: *mut crate::leanh::LeanObject,
    mut v_e_869_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_870_ = l_Lean_CollectLevelMVars_main(v_e_869_, v_s_868_);
    return v___x_870_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Util_CollectLevelMVars(
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
    l_Lean_CollectLevelMVars_instInhabitedState =
        _init_l_Lean_CollectLevelMVars_instInhabitedState();
    crate::leanh::lean_mark_persistent(l_Lean_CollectLevelMVars_instInhabitedState);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Util_CollectLevelMVars(
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
pub unsafe fn initialize_Lean_Util_CollectLevelMVars(builtin: u8) -> *mut crate::leanh::LeanObject {
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
    res = runtime_initialize_Lean_Util_CollectLevelMVars(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Util_CollectLevelMVars(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Util_CollectLevelMVars(builtin);
}
