// Lean compiler output
// Module: Lean.Util.CollectLevelParams
// Imports: Lean.Expr
use crate::r#gen::Init::Meta::Defs::lean_name_append_index_after;
use crate::r#gen::Lean::Expr::{
    initialize_Lean_Expr, l_Lean_Expr_hasLevelParam, l_Lean_Expr_hash, runtime_initialize_Lean_Expr,
};
use crate::r#gen::Lean::Level::{l_Lean_Level_hasParam, l_Lean_Level_hash, l_Lean_mkLevelParam};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_of_nat, lean_usize_sub};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_get_size, lean_array_push, lean_nat_add, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_div, lean_nat_mul,
};
use crate::lean_imports_rs::Lean::Expr::lean_expr_eqv;
use crate::lean_imports_rs::Lean::Level::lean_level_eq;
static mut l_Lean_CollectLevelParams_instInhabitedState___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_CollectLevelParams_instInhabitedState___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_CollectLevelParams_instInhabitedState___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_CollectLevelParams_instInhabitedState___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_CollectLevelParams_instInhabitedState___closed__2_value:
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
static mut l_Lean_CollectLevelParams_instInhabitedState___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_CollectLevelParams_instInhabitedState___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_CollectLevelParams_instInhabitedState___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_CollectLevelParams_instInhabitedState___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_CollectLevelParams_instInhabitedState: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn _init_l_Lean_CollectLevelParams_instInhabitedState___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_466_ = crate::leanh::lean_box(0);
    v___x_467_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_468_ = lean_mk_array(v___x_467_, v___x_466_);
    return v___x_468_;
}
pub unsafe fn _init_l_Lean_CollectLevelParams_instInhabitedState___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_469_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_CollectLevelParams_instInhabitedState___closed__0),
        core::ptr::addr_of_mut!(l_Lean_CollectLevelParams_instInhabitedState___closed__0_once),
        _init_l_Lean_CollectLevelParams_instInhabitedState___closed__0,
    );
    v___x_470_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_471_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_471_, 0, v___x_470_);
    crate::leanh::lean_ctor_set(v___x_471_, 1, v___x_469_);
    return v___x_471_;
}
pub unsafe fn _init_l_Lean_CollectLevelParams_instInhabitedState___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_474_ = l_Lean_CollectLevelParams_instInhabitedState___closed__2;
    v___x_475_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_CollectLevelParams_instInhabitedState___closed__1),
        core::ptr::addr_of_mut!(l_Lean_CollectLevelParams_instInhabitedState___closed__1_once),
        _init_l_Lean_CollectLevelParams_instInhabitedState___closed__1,
    );
    v___x_476_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_476_, 0, v___x_475_);
    crate::leanh::lean_ctor_set(v___x_476_, 1, v___x_475_);
    crate::leanh::lean_ctor_set(v___x_476_, 2, v___x_474_);
    return v___x_476_;
}
pub unsafe fn _init_l_Lean_CollectLevelParams_instInhabitedState() -> *mut crate::leanh::LeanObject
{
    let mut v___x_477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_477_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_CollectLevelParams_instInhabitedState___closed__3),
        core::ptr::addr_of_mut!(l_Lean_CollectLevelParams_instInhabitedState___closed__3_once),
        _init_l_Lean_CollectLevelParams_instInhabitedState___closed__3,
    );
    return v___x_477_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__1___redArg(
    mut v_a_478_: *mut crate::leanh::LeanObject,
    mut v_x_479_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_480_: u8 = 0;
    let mut v_key_481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_483_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_479_) == 0 {
                    v___x_480_ = 0;
                    return v___x_480_;
                } else {
                    v_key_481_ = crate::leanh::lean_ctor_get(v_x_479_, 0);
                    v_tail_482_ = crate::leanh::lean_ctor_get(v_x_479_, 2);
                    v___x_483_ = lean_level_eq(v_key_481_, v_a_478_);
                    if v___x_483_ == 0 {
                        v_x_479_ = v_tail_482_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_483_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__1___redArg___boxed(
    mut v_a_485_: *mut crate::leanh::LeanObject,
    mut v_x_486_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_487_: u8 = 0;
    let mut v_r_488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_487_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__1___redArg(v_a_485_, v_x_486_);
    crate::leanh::lean_dec(v_x_486_);
    crate::leanh::lean_dec(v_a_485_);
    v_r_488_ = crate::leanh::lean_box((v_res_487_) as usize);
    return v_r_488_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0___redArg(
    mut v_m_489_: *mut crate::leanh::LeanObject,
    mut v_a_490_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_buckets_491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_493_: u64 = 0;
    let mut v___x_494_: u64 = 0;
    let mut v___x_495_: u64 = 0;
    let mut v_fold_496_: u64 = 0;
    let mut v___x_497_: u64 = 0;
    let mut v___x_498_: u64 = 0;
    let mut v___x_499_: u64 = 0;
    let mut v___x_500_: usize = 0;
    let mut v___x_501_: usize = 0;
    let mut v___x_502_: usize = 0;
    let mut v___x_503_: usize = 0;
    let mut v___x_504_: usize = 0;
    let mut v___x_505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_506_: u8 = 0;
    v_buckets_491_ = crate::leanh::lean_ctor_get(v_m_489_, 1);
    v___x_492_ = lean_array_get_size(v_buckets_491_);
    v___x_493_ = l_Lean_Level_hash(v_a_490_);
    v___x_494_ = 32u64;
    v___x_495_ = lean_uint64_shift_right(v___x_493_, v___x_494_);
    v_fold_496_ = lean_uint64_xor(v___x_493_, v___x_495_);
    v___x_497_ = 16u64;
    v___x_498_ = lean_uint64_shift_right(v_fold_496_, v___x_497_);
    v___x_499_ = lean_uint64_xor(v_fold_496_, v___x_498_);
    v___x_500_ = lean_uint64_to_usize(v___x_499_);
    v___x_501_ = lean_usize_of_nat(v___x_492_);
    v___x_502_ = 1usize;
    v___x_503_ = lean_usize_sub(v___x_501_, v___x_502_);
    v___x_504_ = lean_usize_land(v___x_500_, v___x_503_);
    v___x_505_ = lean_array_uget_borrowed(v_buckets_491_, v___x_504_);
    v___x_506_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__1___redArg(v_a_490_, v___x_505_);
    return v___x_506_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0___redArg___boxed(
    mut v_m_507_: *mut crate::leanh::LeanObject,
    mut v_a_508_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_509_: u8 = 0;
    let mut v_r_510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_509_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0___redArg(v_m_507_, v_a_508_);
    crate::leanh::lean_dec(v_a_508_);
    crate::leanh::lean_dec_ref(v_m_507_);
    v_r_510_ = crate::leanh::lean_box((v_res_509_) as usize);
    return v_r_510_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__1_spec__3_spec__4_spec__5___redArg(
    mut v_x_511_: *mut crate::leanh::LeanObject,
    mut v_x_512_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_518_: u8 = 0;
    let mut v___x_519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_520_: u64 = 0;
    let mut v___x_521_: u64 = 0;
    let mut v___x_522_: u64 = 0;
    let mut v_fold_523_: u64 = 0;
    let mut v___x_524_: u64 = 0;
    let mut v___x_525_: u64 = 0;
    let mut v___x_526_: u64 = 0;
    let mut v___x_527_: usize = 0;
    let mut v___x_528_: usize = 0;
    let mut v___x_529_: usize = 0;
    let mut v___x_530_: usize = 0;
    let mut v___x_531_: usize = 0;
    let mut v___x_532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_538_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_512_) == 0 {
                    return v_x_511_;
                } else {
                    v_key_513_ = crate::leanh::lean_ctor_get(v_x_512_, 0);
                    v_value_514_ = crate::leanh::lean_ctor_get(v_x_512_, 1);
                    v_tail_515_ = crate::leanh::lean_ctor_get(v_x_512_, 2);
                    v_isSharedCheck_538_ = (!crate::leanh::lean_is_exclusive(v_x_512_)) as u8;
                    if v_isSharedCheck_538_ == 0 {
                        v___x_517_ = v_x_512_;
                        v_isShared_518_ = v_isSharedCheck_538_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_515_);
                        crate::leanh::lean_inc(v_value_514_);
                        crate::leanh::lean_inc(v_key_513_);
                        crate::leanh::lean_dec(v_x_512_);
                        v___x_517_ = crate::leanh::lean_box(0);
                        v_isShared_518_ = v_isSharedCheck_538_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_519_ = lean_array_get_size(v_x_511_);
                v___x_520_ = l_Lean_Level_hash(v_key_513_);
                v___x_521_ = 32u64;
                v___x_522_ = lean_uint64_shift_right(v___x_520_, v___x_521_);
                v_fold_523_ = lean_uint64_xor(v___x_520_, v___x_522_);
                v___x_524_ = 16u64;
                v___x_525_ = lean_uint64_shift_right(v_fold_523_, v___x_524_);
                v___x_526_ = lean_uint64_xor(v_fold_523_, v___x_525_);
                v___x_527_ = lean_uint64_to_usize(v___x_526_);
                v___x_528_ = lean_usize_of_nat(v___x_519_);
                v___x_529_ = 1usize;
                v___x_530_ = lean_usize_sub(v___x_528_, v___x_529_);
                v___x_531_ = lean_usize_land(v___x_527_, v___x_530_);
                v___x_532_ = lean_array_uget_borrowed(v_x_511_, v___x_531_);
                crate::leanh::lean_inc(v___x_532_);
                if v_isShared_518_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_517_, 2, v___x_532_);
                    v___x_534_ = v___x_517_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_537_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_537_, 0, v_key_513_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_537_, 1, v_value_514_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_537_, 2, v___x_532_);
                    v___x_534_ = v_reuseFailAlloc_537_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_535_ = lean_array_uset(v_x_511_, v___x_531_, v___x_534_);
                v_x_511_ = v___x_535_;
                v_x_512_ = v_tail_515_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__1_spec__3_spec__4___redArg(
    mut v_i_539_: *mut crate::leanh::LeanObject,
    mut v_source_540_: *mut crate::leanh::LeanObject,
    mut v_target_541_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_543_: u8 = 0;
    let mut v_es_544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_542_ = lean_array_get_size(v_source_540_);
                v___x_543_ = lean_nat_dec_lt(v_i_539_, v___x_542_);
                if v___x_543_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_540_);
                    crate::leanh::lean_dec(v_i_539_);
                    return v_target_541_;
                } else {
                    v_es_544_ = lean_array_fget(v_source_540_, v_i_539_);
                    v___x_545_ = crate::leanh::lean_box(0);
                    v_source_546_ = lean_array_fset(v_source_540_, v_i_539_, v___x_545_);
                    v_target_547_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__1_spec__3_spec__4_spec__5___redArg(v_target_541_, v_es_544_);
                    v___x_548_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_549_ = lean_nat_add(v_i_539_, v___x_548_);
                    crate::leanh::lean_dec(v_i_539_);
                    v_i_539_ = v___x_549_;
                    v_source_540_ = v_source_546_;
                    v_target_541_ = v_target_547_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__1_spec__3___redArg(
    mut v_data_551_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_552_ = lean_array_get_size(v_data_551_);
    v___x_553_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_554_ = lean_nat_mul(v___x_552_, v___x_553_);
    v___x_555_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_556_ = crate::leanh::lean_box(0);
    v___x_557_ = lean_mk_array(v_nbuckets_554_, v___x_556_);
    v___x_558_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__1_spec__3_spec__4___redArg(v___x_555_, v_data_551_, v___x_557_);
    return v___x_558_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__1___redArg(
    mut v_m_559_: *mut crate::leanh::LeanObject,
    mut v_a_560_: *mut crate::leanh::LeanObject,
    mut v_b_561_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_565_: u64 = 0;
    let mut v___x_566_: u64 = 0;
    let mut v___x_567_: u64 = 0;
    let mut v_fold_568_: u64 = 0;
    let mut v___x_569_: u64 = 0;
    let mut v___x_570_: u64 = 0;
    let mut v___x_571_: u64 = 0;
    let mut v___x_572_: usize = 0;
    let mut v___x_573_: usize = 0;
    let mut v___x_574_: usize = 0;
    let mut v___x_575_: usize = 0;
    let mut v___x_576_: usize = 0;
    let mut v_bkt_577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_578_: u8 = 0;
    let mut v___x_580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_581_: u8 = 0;
    let mut v___x_582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_591_: u8 = 0;
    let mut v_val_592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_599_: u8 = 0;
    let mut v_unused_600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_562_ = crate::leanh::lean_ctor_get(v_m_559_, 0);
                v_buckets_563_ = crate::leanh::lean_ctor_get(v_m_559_, 1);
                v___x_564_ = lean_array_get_size(v_buckets_563_);
                v___x_565_ = l_Lean_Level_hash(v_a_560_);
                v___x_566_ = 32u64;
                v___x_567_ = lean_uint64_shift_right(v___x_565_, v___x_566_);
                v_fold_568_ = lean_uint64_xor(v___x_565_, v___x_567_);
                v___x_569_ = 16u64;
                v___x_570_ = lean_uint64_shift_right(v_fold_568_, v___x_569_);
                v___x_571_ = lean_uint64_xor(v_fold_568_, v___x_570_);
                v___x_572_ = lean_uint64_to_usize(v___x_571_);
                v___x_573_ = lean_usize_of_nat(v___x_564_);
                v___x_574_ = 1usize;
                v___x_575_ = lean_usize_sub(v___x_573_, v___x_574_);
                v___x_576_ = lean_usize_land(v___x_572_, v___x_575_);
                v_bkt_577_ = lean_array_uget_borrowed(v_buckets_563_, v___x_576_);
                v___x_578_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__1___redArg(v_a_560_, v_bkt_577_);
                if v___x_578_ == 0 {
                    crate::leanh::lean_inc_ref(v_buckets_563_);
                    crate::leanh::lean_inc(v_size_562_);
                    v_isSharedCheck_599_ = (!crate::leanh::lean_is_exclusive(v_m_559_)) as u8;
                    if v_isSharedCheck_599_ == 0 {
                        v_unused_600_ = crate::leanh::lean_ctor_get(v_m_559_, 1);
                        crate::leanh::lean_dec(v_unused_600_);
                        v_unused_601_ = crate::leanh::lean_ctor_get(v_m_559_, 0);
                        crate::leanh::lean_dec(v_unused_601_);
                        v___x_580_ = v_m_559_;
                        v_isShared_581_ = v_isSharedCheck_599_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_559_);
                        v___x_580_ = crate::leanh::lean_box(0);
                        v_isShared_581_ = v_isSharedCheck_599_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_b_561_);
                    crate::leanh::lean_dec(v_a_560_);
                    return v_m_559_;
                }
            }
            1 => {
                v___x_582_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_583_ = lean_nat_add(v_size_562_, v___x_582_);
                crate::leanh::lean_dec(v_size_562_);
                crate::leanh::lean_inc(v_bkt_577_);
                v___x_584_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_584_, 0, v_a_560_);
                crate::leanh::lean_ctor_set(v___x_584_, 1, v_b_561_);
                crate::leanh::lean_ctor_set(v___x_584_, 2, v_bkt_577_);
                v_buckets_x27_585_ = lean_array_uset(v_buckets_563_, v___x_576_, v___x_584_);
                v___x_586_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_587_ = lean_nat_mul(v_size_x27_583_, v___x_586_);
                v___x_588_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_589_ = lean_nat_div(v___x_587_, v___x_588_);
                crate::leanh::lean_dec(v___x_587_);
                v___x_590_ = lean_array_get_size(v_buckets_x27_585_);
                v___x_591_ = lean_nat_dec_le(v___x_589_, v___x_590_);
                crate::leanh::lean_dec(v___x_589_);
                if v___x_591_ == 0 {
                    v_val_592_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__1_spec__3___redArg(v_buckets_x27_585_);
                    if v_isShared_581_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_580_, 1, v_val_592_);
                        crate::leanh::lean_ctor_set(v___x_580_, 0, v_size_x27_583_);
                        v___x_594_ = v___x_580_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_595_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_595_, 0, v_size_x27_583_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_595_, 1, v_val_592_);
                        v___x_594_ = v_reuseFailAlloc_595_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_581_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_580_, 1, v_buckets_x27_585_);
                        crate::leanh::lean_ctor_set(v___x_580_, 0, v_size_x27_583_);
                        v___x_597_ = v___x_580_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_598_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_598_, 0, v_size_x27_583_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_598_, 1, v_buckets_x27_585_);
                        v___x_597_ = v_reuseFailAlloc_598_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_594_;
            }
            3 => {
                return v___x_597_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_CollectLevelParams_collect(
    mut v_x_602_: *mut crate::leanh::LeanObject,
    mut v_a_603_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_u_605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_visitedLevel_617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_visitedExpr_618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_622_: u8 = 0;
    let mut v___x_623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_627_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_602_) {
                1 => {
                    v_a_610_ = crate::leanh::lean_ctor_get(v_x_602_, 0);
                    crate::leanh::lean_inc(v_a_610_);
                    crate::leanh::lean_dec_ref_known(v_x_602_, 1);
                    v___x_611_ = l_Lean_CollectLevelParams_visitLevel(v_a_610_, v_a_603_);
                    return v___x_611_;
                }
                2 => {
                    v_a_612_ = crate::leanh::lean_ctor_get(v_x_602_, 0);
                    crate::leanh::lean_inc(v_a_612_);
                    v_a_613_ = crate::leanh::lean_ctor_get(v_x_602_, 1);
                    crate::leanh::lean_inc(v_a_613_);
                    crate::leanh::lean_dec_ref_known(v_x_602_, 2);
                    v_u_605_ = v_a_612_;
                    v_v_606_ = v_a_613_;
                    v___y_607_ = v_a_603_;
                    state = 1;
                    continue;
                }
                3 => {
                    v_a_614_ = crate::leanh::lean_ctor_get(v_x_602_, 0);
                    crate::leanh::lean_inc(v_a_614_);
                    v_a_615_ = crate::leanh::lean_ctor_get(v_x_602_, 1);
                    crate::leanh::lean_inc(v_a_615_);
                    crate::leanh::lean_dec_ref_known(v_x_602_, 2);
                    v_u_605_ = v_a_614_;
                    v_v_606_ = v_a_615_;
                    v___y_607_ = v_a_603_;
                    state = 1;
                    continue;
                }
                4 => {
                    v_a_616_ = crate::leanh::lean_ctor_get(v_x_602_, 0);
                    crate::leanh::lean_inc(v_a_616_);
                    crate::leanh::lean_dec_ref_known(v_x_602_, 1);
                    v_visitedLevel_617_ = crate::leanh::lean_ctor_get(v_a_603_, 0);
                    v_visitedExpr_618_ = crate::leanh::lean_ctor_get(v_a_603_, 1);
                    v_params_619_ = crate::leanh::lean_ctor_get(v_a_603_, 2);
                    v_isSharedCheck_627_ = (!crate::leanh::lean_is_exclusive(v_a_603_)) as u8;
                    if v_isSharedCheck_627_ == 0 {
                        v___x_621_ = v_a_603_;
                        v_isShared_622_ = v_isSharedCheck_627_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_params_619_);
                        crate::leanh::lean_inc(v_visitedExpr_618_);
                        crate::leanh::lean_inc(v_visitedLevel_617_);
                        crate::leanh::lean_dec(v_a_603_);
                        v___x_621_ = crate::leanh::lean_box(0);
                        v_isShared_622_ = v_isSharedCheck_627_;
                        state = 2;
                        continue;
                    }
                }
                _ => {
                    crate::leanh::lean_dec(v_x_602_);
                    return v_a_603_;
                }
            },
            1 => {
                v___x_608_ = l_Lean_CollectLevelParams_visitLevel(v_u_605_, v___y_607_);
                v___x_609_ = l_Lean_CollectLevelParams_visitLevel(v_v_606_, v___x_608_);
                return v___x_609_;
            }
            2 => {
                v___x_623_ = lean_array_push(v_params_619_, v_a_616_);
                if v_isShared_622_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_621_, 2, v___x_623_);
                    v___x_625_ = v___x_621_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_626_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_626_, 0, v_visitedLevel_617_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_626_, 1, v_visitedExpr_618_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_626_, 2, v___x_623_);
                    v___x_625_ = v_reuseFailAlloc_626_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_625_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_CollectLevelParams_visitLevel(
    mut v_u_628_: *mut crate::leanh::LeanObject,
    mut v_s_629_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_630_: u8 = 0;
    let mut v_visitedLevel_631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_visitedExpr_632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_634_: u8 = 0;
    let mut v___x_636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_637_: u8 = 0;
    let mut v___x_638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_644_: u8 = 0;
    let mut v_unused_645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_630_ = l_Lean_Level_hasParam(v_u_628_);
                if v___x_630_ == 0 {
                    crate::leanh::lean_dec(v_u_628_);
                    return v_s_629_;
                } else {
                    v_visitedLevel_631_ = crate::leanh::lean_ctor_get(v_s_629_, 0);
                    v_visitedExpr_632_ = crate::leanh::lean_ctor_get(v_s_629_, 1);
                    v_params_633_ = crate::leanh::lean_ctor_get(v_s_629_, 2);
                    v___x_634_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0___redArg(v_visitedLevel_631_, v_u_628_);
                    if v___x_634_ == 0 {
                        crate::leanh::lean_inc_ref(v_params_633_);
                        crate::leanh::lean_inc_ref(v_visitedExpr_632_);
                        crate::leanh::lean_inc_ref(v_visitedLevel_631_);
                        v_isSharedCheck_644_ = (!crate::leanh::lean_is_exclusive(v_s_629_)) as u8;
                        if v_isSharedCheck_644_ == 0 {
                            v_unused_645_ = crate::leanh::lean_ctor_get(v_s_629_, 2);
                            crate::leanh::lean_dec(v_unused_645_);
                            v_unused_646_ = crate::leanh::lean_ctor_get(v_s_629_, 1);
                            crate::leanh::lean_dec(v_unused_646_);
                            v_unused_647_ = crate::leanh::lean_ctor_get(v_s_629_, 0);
                            crate::leanh::lean_dec(v_unused_647_);
                            v___x_636_ = v_s_629_;
                            v_isShared_637_ = v_isSharedCheck_644_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_s_629_);
                            v___x_636_ = crate::leanh::lean_box(0);
                            v_isShared_637_ = v_isSharedCheck_644_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_u_628_);
                        return v_s_629_;
                    }
                }
            }
            1 => {
                v___x_638_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v_u_628_);
                v___x_639_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__1___redArg(v_visitedLevel_631_, v_u_628_, v___x_638_);
                if v_isShared_637_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_636_, 0, v___x_639_);
                    v___x_641_ = v___x_636_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_643_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_643_, 0, v___x_639_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_643_, 1, v_visitedExpr_632_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_643_, 2, v_params_633_);
                    v___x_641_ = v_reuseFailAlloc_643_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_642_ = l_Lean_CollectLevelParams_collect(v_u_628_, v___x_641_);
                return v___x_642_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0(
    mut v_00_u03b2_648_: *mut crate::leanh::LeanObject,
    mut v_m_649_: *mut crate::leanh::LeanObject,
    mut v_a_650_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_651_: u8 = 0;
    v___x_651_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0___redArg(v_m_649_, v_a_650_);
    return v___x_651_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0___boxed(
    mut v_00_u03b2_652_: *mut crate::leanh::LeanObject,
    mut v_m_653_: *mut crate::leanh::LeanObject,
    mut v_a_654_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_655_: u8 = 0;
    let mut v_r_656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_655_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0(v_00_u03b2_652_, v_m_653_, v_a_654_);
    crate::leanh::lean_dec(v_a_654_);
    crate::leanh::lean_dec_ref(v_m_653_);
    v_r_656_ = crate::leanh::lean_box((v_res_655_) as usize);
    return v_r_656_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__1(
    mut v_00_u03b2_657_: *mut crate::leanh::LeanObject,
    mut v_m_658_: *mut crate::leanh::LeanObject,
    mut v_a_659_: *mut crate::leanh::LeanObject,
    mut v_b_660_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_661_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__1___redArg(v_m_658_, v_a_659_, v_b_660_);
    return v___x_661_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__1(
    mut v_00_u03b2_662_: *mut crate::leanh::LeanObject,
    mut v_a_663_: *mut crate::leanh::LeanObject,
    mut v_x_664_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_665_: u8 = 0;
    v___x_665_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__1___redArg(v_a_663_, v_x_664_);
    return v___x_665_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__1___boxed(
    mut v_00_u03b2_666_: *mut crate::leanh::LeanObject,
    mut v_a_667_: *mut crate::leanh::LeanObject,
    mut v_x_668_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_669_: u8 = 0;
    let mut v_r_670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_669_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0_spec__1(v_00_u03b2_666_, v_a_667_, v_x_668_);
    crate::leanh::lean_dec(v_x_668_);
    crate::leanh::lean_dec(v_a_667_);
    v_r_670_ = crate::leanh::lean_box((v_res_669_) as usize);
    return v_r_670_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__1_spec__3(
    mut v_00_u03b2_671_: *mut crate::leanh::LeanObject,
    mut v_data_672_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_673_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__1_spec__3___redArg(v_data_672_);
    return v___x_673_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__1_spec__3_spec__4(
    mut v_00_u03b2_674_: *mut crate::leanh::LeanObject,
    mut v_i_675_: *mut crate::leanh::LeanObject,
    mut v_source_676_: *mut crate::leanh::LeanObject,
    mut v_target_677_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_678_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__1_spec__3_spec__4___redArg(v_i_675_, v_source_676_, v_target_677_);
    return v___x_678_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__1_spec__3_spec__4_spec__5(
    mut v_00_u03b2_679_: *mut crate::leanh::LeanObject,
    mut v_x_680_: *mut crate::leanh::LeanObject,
    mut v_x_681_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_682_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitLevel_spec__1_spec__3_spec__4_spec__5___redArg(v_x_680_, v_x_681_);
    return v___x_682_;
}
pub unsafe fn l_List_foldl___at___00Lean_CollectLevelParams_visitLevels_spec__0(
    mut v_x_683_: *mut crate::leanh::LeanObject,
    mut v_x_684_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_684_) == 0 {
                    return v_x_683_;
                } else {
                    v_head_685_ = crate::leanh::lean_ctor_get(v_x_684_, 0);
                    crate::leanh::lean_inc(v_head_685_);
                    v_tail_686_ = crate::leanh::lean_ctor_get(v_x_684_, 1);
                    crate::leanh::lean_inc(v_tail_686_);
                    crate::leanh::lean_dec_ref_known(v_x_684_, 2);
                    v___x_687_ = l_Lean_CollectLevelParams_visitLevel(v_head_685_, v_x_683_);
                    v_x_683_ = v___x_687_;
                    v_x_684_ = v_tail_686_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_CollectLevelParams_visitLevels(
    mut v_us_689_: *mut crate::leanh::LeanObject,
    mut v_s_690_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_691_ =
        l_List_foldl___at___00Lean_CollectLevelParams_visitLevels_spec__0(v_s_690_, v_us_689_);
    return v___x_691_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0_spec__1___redArg(
    mut v_a_692_: *mut crate::leanh::LeanObject,
    mut v_x_693_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_694_: u8 = 0;
    let mut v_key_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_697_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_693_) == 0 {
                    v___x_694_ = 0;
                    return v___x_694_;
                } else {
                    v_key_695_ = crate::leanh::lean_ctor_get(v_x_693_, 0);
                    v_tail_696_ = crate::leanh::lean_ctor_get(v_x_693_, 2);
                    v___x_697_ = lean_expr_eqv(v_key_695_, v_a_692_);
                    if v___x_697_ == 0 {
                        v_x_693_ = v_tail_696_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_697_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0_spec__1___redArg___boxed(
    mut v_a_699_: *mut crate::leanh::LeanObject,
    mut v_x_700_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_701_: u8 = 0;
    let mut v_r_702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_701_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0_spec__1___redArg(v_a_699_, v_x_700_);
    crate::leanh::lean_dec(v_x_700_);
    crate::leanh::lean_dec_ref(v_a_699_);
    v_r_702_ = crate::leanh::lean_box((v_res_701_) as usize);
    return v_r_702_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0___redArg(
    mut v_m_703_: *mut crate::leanh::LeanObject,
    mut v_a_704_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_buckets_705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_707_: u64 = 0;
    let mut v___x_708_: u64 = 0;
    let mut v___x_709_: u64 = 0;
    let mut v_fold_710_: u64 = 0;
    let mut v___x_711_: u64 = 0;
    let mut v___x_712_: u64 = 0;
    let mut v___x_713_: u64 = 0;
    let mut v___x_714_: usize = 0;
    let mut v___x_715_: usize = 0;
    let mut v___x_716_: usize = 0;
    let mut v___x_717_: usize = 0;
    let mut v___x_718_: usize = 0;
    let mut v___x_719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_720_: u8 = 0;
    v_buckets_705_ = crate::leanh::lean_ctor_get(v_m_703_, 1);
    v___x_706_ = lean_array_get_size(v_buckets_705_);
    v___x_707_ = l_Lean_Expr_hash(v_a_704_);
    v___x_708_ = 32u64;
    v___x_709_ = lean_uint64_shift_right(v___x_707_, v___x_708_);
    v_fold_710_ = lean_uint64_xor(v___x_707_, v___x_709_);
    v___x_711_ = 16u64;
    v___x_712_ = lean_uint64_shift_right(v_fold_710_, v___x_711_);
    v___x_713_ = lean_uint64_xor(v_fold_710_, v___x_712_);
    v___x_714_ = lean_uint64_to_usize(v___x_713_);
    v___x_715_ = lean_usize_of_nat(v___x_706_);
    v___x_716_ = 1usize;
    v___x_717_ = lean_usize_sub(v___x_715_, v___x_716_);
    v___x_718_ = lean_usize_land(v___x_714_, v___x_717_);
    v___x_719_ = lean_array_uget_borrowed(v_buckets_705_, v___x_718_);
    v___x_720_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0_spec__1___redArg(v_a_704_, v___x_719_);
    return v___x_720_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0___redArg___boxed(
    mut v_m_721_: *mut crate::leanh::LeanObject,
    mut v_a_722_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_723_: u8 = 0;
    let mut v_r_724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_723_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0___redArg(v_m_721_, v_a_722_);
    crate::leanh::lean_dec_ref(v_a_722_);
    crate::leanh::lean_dec_ref(v_m_721_);
    v_r_724_ = crate::leanh::lean_box((v_res_723_) as usize);
    return v_r_724_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitExpr_spec__1_spec__3_spec__4_spec__5___redArg(
    mut v_x_725_: *mut crate::leanh::LeanObject,
    mut v_x_726_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_732_: u8 = 0;
    let mut v___x_733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_734_: u64 = 0;
    let mut v___x_735_: u64 = 0;
    let mut v___x_736_: u64 = 0;
    let mut v_fold_737_: u64 = 0;
    let mut v___x_738_: u64 = 0;
    let mut v___x_739_: u64 = 0;
    let mut v___x_740_: u64 = 0;
    let mut v___x_741_: usize = 0;
    let mut v___x_742_: usize = 0;
    let mut v___x_743_: usize = 0;
    let mut v___x_744_: usize = 0;
    let mut v___x_745_: usize = 0;
    let mut v___x_746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_752_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_726_) == 0 {
                    return v_x_725_;
                } else {
                    v_key_727_ = crate::leanh::lean_ctor_get(v_x_726_, 0);
                    v_value_728_ = crate::leanh::lean_ctor_get(v_x_726_, 1);
                    v_tail_729_ = crate::leanh::lean_ctor_get(v_x_726_, 2);
                    v_isSharedCheck_752_ = (!crate::leanh::lean_is_exclusive(v_x_726_)) as u8;
                    if v_isSharedCheck_752_ == 0 {
                        v___x_731_ = v_x_726_;
                        v_isShared_732_ = v_isSharedCheck_752_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_729_);
                        crate::leanh::lean_inc(v_value_728_);
                        crate::leanh::lean_inc(v_key_727_);
                        crate::leanh::lean_dec(v_x_726_);
                        v___x_731_ = crate::leanh::lean_box(0);
                        v_isShared_732_ = v_isSharedCheck_752_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_733_ = lean_array_get_size(v_x_725_);
                v___x_734_ = l_Lean_Expr_hash(v_key_727_);
                v___x_735_ = 32u64;
                v___x_736_ = lean_uint64_shift_right(v___x_734_, v___x_735_);
                v_fold_737_ = lean_uint64_xor(v___x_734_, v___x_736_);
                v___x_738_ = 16u64;
                v___x_739_ = lean_uint64_shift_right(v_fold_737_, v___x_738_);
                v___x_740_ = lean_uint64_xor(v_fold_737_, v___x_739_);
                v___x_741_ = lean_uint64_to_usize(v___x_740_);
                v___x_742_ = lean_usize_of_nat(v___x_733_);
                v___x_743_ = 1usize;
                v___x_744_ = lean_usize_sub(v___x_742_, v___x_743_);
                v___x_745_ = lean_usize_land(v___x_741_, v___x_744_);
                v___x_746_ = lean_array_uget_borrowed(v_x_725_, v___x_745_);
                crate::leanh::lean_inc(v___x_746_);
                if v_isShared_732_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_731_, 2, v___x_746_);
                    v___x_748_ = v___x_731_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_751_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_751_, 0, v_key_727_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_751_, 1, v_value_728_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_751_, 2, v___x_746_);
                    v___x_748_ = v_reuseFailAlloc_751_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_749_ = lean_array_uset(v_x_725_, v___x_745_, v___x_748_);
                v_x_725_ = v___x_749_;
                v_x_726_ = v_tail_729_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitExpr_spec__1_spec__3_spec__4___redArg(
    mut v_i_753_: *mut crate::leanh::LeanObject,
    mut v_source_754_: *mut crate::leanh::LeanObject,
    mut v_target_755_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_757_: u8 = 0;
    let mut v_es_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_756_ = lean_array_get_size(v_source_754_);
                v___x_757_ = lean_nat_dec_lt(v_i_753_, v___x_756_);
                if v___x_757_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_754_);
                    crate::leanh::lean_dec(v_i_753_);
                    return v_target_755_;
                } else {
                    v_es_758_ = lean_array_fget(v_source_754_, v_i_753_);
                    v___x_759_ = crate::leanh::lean_box(0);
                    v_source_760_ = lean_array_fset(v_source_754_, v_i_753_, v___x_759_);
                    v_target_761_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitExpr_spec__1_spec__3_spec__4_spec__5___redArg(v_target_755_, v_es_758_);
                    v___x_762_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_763_ = lean_nat_add(v_i_753_, v___x_762_);
                    crate::leanh::lean_dec(v_i_753_);
                    v_i_753_ = v___x_763_;
                    v_source_754_ = v_source_760_;
                    v_target_755_ = v_target_761_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitExpr_spec__1_spec__3___redArg(
    mut v_data_765_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_766_ = lean_array_get_size(v_data_765_);
    v___x_767_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_768_ = lean_nat_mul(v___x_766_, v___x_767_);
    v___x_769_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_770_ = crate::leanh::lean_box(0);
    v___x_771_ = lean_mk_array(v_nbuckets_768_, v___x_770_);
    v___x_772_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitExpr_spec__1_spec__3_spec__4___redArg(v___x_769_, v_data_765_, v___x_771_);
    return v___x_772_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitExpr_spec__1___redArg(
    mut v_m_773_: *mut crate::leanh::LeanObject,
    mut v_a_774_: *mut crate::leanh::LeanObject,
    mut v_b_775_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_779_: u64 = 0;
    let mut v___x_780_: u64 = 0;
    let mut v___x_781_: u64 = 0;
    let mut v_fold_782_: u64 = 0;
    let mut v___x_783_: u64 = 0;
    let mut v___x_784_: u64 = 0;
    let mut v___x_785_: u64 = 0;
    let mut v___x_786_: usize = 0;
    let mut v___x_787_: usize = 0;
    let mut v___x_788_: usize = 0;
    let mut v___x_789_: usize = 0;
    let mut v___x_790_: usize = 0;
    let mut v_bkt_791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_792_: u8 = 0;
    let mut v___x_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_795_: u8 = 0;
    let mut v___x_796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_805_: u8 = 0;
    let mut v_val_806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_813_: u8 = 0;
    let mut v_unused_814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_776_ = crate::leanh::lean_ctor_get(v_m_773_, 0);
                v_buckets_777_ = crate::leanh::lean_ctor_get(v_m_773_, 1);
                v___x_778_ = lean_array_get_size(v_buckets_777_);
                v___x_779_ = l_Lean_Expr_hash(v_a_774_);
                v___x_780_ = 32u64;
                v___x_781_ = lean_uint64_shift_right(v___x_779_, v___x_780_);
                v_fold_782_ = lean_uint64_xor(v___x_779_, v___x_781_);
                v___x_783_ = 16u64;
                v___x_784_ = lean_uint64_shift_right(v_fold_782_, v___x_783_);
                v___x_785_ = lean_uint64_xor(v_fold_782_, v___x_784_);
                v___x_786_ = lean_uint64_to_usize(v___x_785_);
                v___x_787_ = lean_usize_of_nat(v___x_778_);
                v___x_788_ = 1usize;
                v___x_789_ = lean_usize_sub(v___x_787_, v___x_788_);
                v___x_790_ = lean_usize_land(v___x_786_, v___x_789_);
                v_bkt_791_ = lean_array_uget_borrowed(v_buckets_777_, v___x_790_);
                v___x_792_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0_spec__1___redArg(v_a_774_, v_bkt_791_);
                if v___x_792_ == 0 {
                    crate::leanh::lean_inc_ref(v_buckets_777_);
                    crate::leanh::lean_inc(v_size_776_);
                    v_isSharedCheck_813_ = (!crate::leanh::lean_is_exclusive(v_m_773_)) as u8;
                    if v_isSharedCheck_813_ == 0 {
                        v_unused_814_ = crate::leanh::lean_ctor_get(v_m_773_, 1);
                        crate::leanh::lean_dec(v_unused_814_);
                        v_unused_815_ = crate::leanh::lean_ctor_get(v_m_773_, 0);
                        crate::leanh::lean_dec(v_unused_815_);
                        v___x_794_ = v_m_773_;
                        v_isShared_795_ = v_isSharedCheck_813_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_773_);
                        v___x_794_ = crate::leanh::lean_box(0);
                        v_isShared_795_ = v_isSharedCheck_813_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_b_775_);
                    crate::leanh::lean_dec_ref(v_a_774_);
                    return v_m_773_;
                }
            }
            1 => {
                v___x_796_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_797_ = lean_nat_add(v_size_776_, v___x_796_);
                crate::leanh::lean_dec(v_size_776_);
                crate::leanh::lean_inc(v_bkt_791_);
                v___x_798_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_798_, 0, v_a_774_);
                crate::leanh::lean_ctor_set(v___x_798_, 1, v_b_775_);
                crate::leanh::lean_ctor_set(v___x_798_, 2, v_bkt_791_);
                v_buckets_x27_799_ = lean_array_uset(v_buckets_777_, v___x_790_, v___x_798_);
                v___x_800_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_801_ = lean_nat_mul(v_size_x27_797_, v___x_800_);
                v___x_802_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_803_ = lean_nat_div(v___x_801_, v___x_802_);
                crate::leanh::lean_dec(v___x_801_);
                v___x_804_ = lean_array_get_size(v_buckets_x27_799_);
                v___x_805_ = lean_nat_dec_le(v___x_803_, v___x_804_);
                crate::leanh::lean_dec(v___x_803_);
                if v___x_805_ == 0 {
                    v_val_806_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitExpr_spec__1_spec__3___redArg(v_buckets_x27_799_);
                    if v_isShared_795_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_794_, 1, v_val_806_);
                        crate::leanh::lean_ctor_set(v___x_794_, 0, v_size_x27_797_);
                        v___x_808_ = v___x_794_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_809_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_809_, 0, v_size_x27_797_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_809_, 1, v_val_806_);
                        v___x_808_ = v_reuseFailAlloc_809_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_795_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_794_, 1, v_buckets_x27_799_);
                        crate::leanh::lean_ctor_set(v___x_794_, 0, v_size_x27_797_);
                        v___x_811_ = v___x_794_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_812_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_812_, 0, v_size_x27_797_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_812_, 1, v_buckets_x27_799_);
                        v___x_811_ = v_reuseFailAlloc_812_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_808_;
            }
            3 => {
                return v___x_811_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_CollectLevelParams_main(
    mut v_x_816_: *mut crate::leanh::LeanObject,
    mut v_a_817_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_d_819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_816_) {
                11 => {
                    v_struct_824_ = crate::leanh::lean_ctor_get(v_x_816_, 2);
                    crate::leanh::lean_inc_ref(v_struct_824_);
                    crate::leanh::lean_dec_ref_known(v_x_816_, 3);
                    v___x_825_ = l_Lean_CollectLevelParams_visitExpr(v_struct_824_, v_a_817_);
                    return v___x_825_;
                }
                7 => {
                    v_binderType_826_ = crate::leanh::lean_ctor_get(v_x_816_, 1);
                    crate::leanh::lean_inc_ref(v_binderType_826_);
                    v_body_827_ = crate::leanh::lean_ctor_get(v_x_816_, 2);
                    crate::leanh::lean_inc_ref(v_body_827_);
                    crate::leanh::lean_dec_ref_known(v_x_816_, 3);
                    v_d_819_ = v_binderType_826_;
                    v_b_820_ = v_body_827_;
                    v___y_821_ = v_a_817_;
                    state = 1;
                    continue;
                }
                6 => {
                    v_binderType_828_ = crate::leanh::lean_ctor_get(v_x_816_, 1);
                    crate::leanh::lean_inc_ref(v_binderType_828_);
                    v_body_829_ = crate::leanh::lean_ctor_get(v_x_816_, 2);
                    crate::leanh::lean_inc_ref(v_body_829_);
                    crate::leanh::lean_dec_ref_known(v_x_816_, 3);
                    v_d_819_ = v_binderType_828_;
                    v_b_820_ = v_body_829_;
                    v___y_821_ = v_a_817_;
                    state = 1;
                    continue;
                }
                8 => {
                    v_type_830_ = crate::leanh::lean_ctor_get(v_x_816_, 1);
                    crate::leanh::lean_inc_ref(v_type_830_);
                    v_value_831_ = crate::leanh::lean_ctor_get(v_x_816_, 2);
                    crate::leanh::lean_inc_ref(v_value_831_);
                    v_body_832_ = crate::leanh::lean_ctor_get(v_x_816_, 3);
                    crate::leanh::lean_inc_ref(v_body_832_);
                    crate::leanh::lean_dec_ref_known(v_x_816_, 4);
                    v___x_833_ = l_Lean_CollectLevelParams_visitExpr(v_type_830_, v_a_817_);
                    v___x_834_ = l_Lean_CollectLevelParams_visitExpr(v_value_831_, v___x_833_);
                    v___x_835_ = l_Lean_CollectLevelParams_visitExpr(v_body_832_, v___x_834_);
                    return v___x_835_;
                }
                5 => {
                    v_fn_836_ = crate::leanh::lean_ctor_get(v_x_816_, 0);
                    crate::leanh::lean_inc_ref(v_fn_836_);
                    v_arg_837_ = crate::leanh::lean_ctor_get(v_x_816_, 1);
                    crate::leanh::lean_inc_ref(v_arg_837_);
                    crate::leanh::lean_dec_ref_known(v_x_816_, 2);
                    v___x_838_ = l_Lean_CollectLevelParams_visitExpr(v_fn_836_, v_a_817_);
                    v___x_839_ = l_Lean_CollectLevelParams_visitExpr(v_arg_837_, v___x_838_);
                    return v___x_839_;
                }
                10 => {
                    v_expr_840_ = crate::leanh::lean_ctor_get(v_x_816_, 1);
                    crate::leanh::lean_inc_ref(v_expr_840_);
                    crate::leanh::lean_dec_ref_known(v_x_816_, 2);
                    v___x_841_ = l_Lean_CollectLevelParams_visitExpr(v_expr_840_, v_a_817_);
                    return v___x_841_;
                }
                4 => {
                    v_us_842_ = crate::leanh::lean_ctor_get(v_x_816_, 1);
                    crate::leanh::lean_inc(v_us_842_);
                    crate::leanh::lean_dec_ref_known(v_x_816_, 2);
                    v___x_843_ = l_List_foldl___at___00Lean_CollectLevelParams_visitLevels_spec__0(
                        v_a_817_, v_us_842_,
                    );
                    return v___x_843_;
                }
                3 => {
                    v_u_844_ = crate::leanh::lean_ctor_get(v_x_816_, 0);
                    crate::leanh::lean_inc(v_u_844_);
                    crate::leanh::lean_dec_ref_known(v_x_816_, 1);
                    v___x_845_ = l_Lean_CollectLevelParams_visitLevel(v_u_844_, v_a_817_);
                    return v___x_845_;
                }
                _ => {
                    crate::leanh::lean_dec_ref(v_x_816_);
                    return v_a_817_;
                }
            },
            1 => {
                v___x_822_ = l_Lean_CollectLevelParams_visitExpr(v_d_819_, v___y_821_);
                v___x_823_ = l_Lean_CollectLevelParams_visitExpr(v_b_820_, v___x_822_);
                return v___x_823_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_CollectLevelParams_visitExpr(
    mut v_e_846_: *mut crate::leanh::LeanObject,
    mut v_s_847_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_848_: u8 = 0;
    let mut v_visitedLevel_849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_visitedExpr_850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_852_: u8 = 0;
    let mut v___x_854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_855_: u8 = 0;
    let mut v___x_856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_862_: u8 = 0;
    let mut v_unused_863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_848_ = l_Lean_Expr_hasLevelParam(v_e_846_);
                if v___x_848_ == 0 {
                    crate::leanh::lean_dec_ref(v_e_846_);
                    return v_s_847_;
                } else {
                    v_visitedLevel_849_ = crate::leanh::lean_ctor_get(v_s_847_, 0);
                    v_visitedExpr_850_ = crate::leanh::lean_ctor_get(v_s_847_, 1);
                    v_params_851_ = crate::leanh::lean_ctor_get(v_s_847_, 2);
                    v___x_852_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0___redArg(v_visitedExpr_850_, v_e_846_);
                    if v___x_852_ == 0 {
                        crate::leanh::lean_inc_ref(v_params_851_);
                        crate::leanh::lean_inc_ref(v_visitedExpr_850_);
                        crate::leanh::lean_inc_ref(v_visitedLevel_849_);
                        v_isSharedCheck_862_ = (!crate::leanh::lean_is_exclusive(v_s_847_)) as u8;
                        if v_isSharedCheck_862_ == 0 {
                            v_unused_863_ = crate::leanh::lean_ctor_get(v_s_847_, 2);
                            crate::leanh::lean_dec(v_unused_863_);
                            v_unused_864_ = crate::leanh::lean_ctor_get(v_s_847_, 1);
                            crate::leanh::lean_dec(v_unused_864_);
                            v_unused_865_ = crate::leanh::lean_ctor_get(v_s_847_, 0);
                            crate::leanh::lean_dec(v_unused_865_);
                            v___x_854_ = v_s_847_;
                            v_isShared_855_ = v_isSharedCheck_862_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_s_847_);
                            v___x_854_ = crate::leanh::lean_box(0);
                            v_isShared_855_ = v_isSharedCheck_862_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_846_);
                        return v_s_847_;
                    }
                }
            }
            1 => {
                v___x_856_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc_ref(v_e_846_);
                v___x_857_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitExpr_spec__1___redArg(v_visitedExpr_850_, v_e_846_, v___x_856_);
                if v_isShared_855_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_854_, 1, v___x_857_);
                    v___x_859_ = v___x_854_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_861_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_861_, 0, v_visitedLevel_849_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_861_, 1, v___x_857_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_861_, 2, v_params_851_);
                    v___x_859_ = v_reuseFailAlloc_861_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_860_ = l_Lean_CollectLevelParams_main(v_e_846_, v___x_859_);
                return v___x_860_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0(
    mut v_00_u03b2_866_: *mut crate::leanh::LeanObject,
    mut v_m_867_: *mut crate::leanh::LeanObject,
    mut v_a_868_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_869_: u8 = 0;
    v___x_869_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0___redArg(v_m_867_, v_a_868_);
    return v___x_869_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0___boxed(
    mut v_00_u03b2_870_: *mut crate::leanh::LeanObject,
    mut v_m_871_: *mut crate::leanh::LeanObject,
    mut v_a_872_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_873_: u8 = 0;
    let mut v_r_874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_873_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0(v_00_u03b2_870_, v_m_871_, v_a_872_);
    crate::leanh::lean_dec_ref(v_a_872_);
    crate::leanh::lean_dec_ref(v_m_871_);
    v_r_874_ = crate::leanh::lean_box((v_res_873_) as usize);
    return v_r_874_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitExpr_spec__1(
    mut v_00_u03b2_875_: *mut crate::leanh::LeanObject,
    mut v_m_876_: *mut crate::leanh::LeanObject,
    mut v_a_877_: *mut crate::leanh::LeanObject,
    mut v_b_878_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_879_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitExpr_spec__1___redArg(v_m_876_, v_a_877_, v_b_878_);
    return v___x_879_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0_spec__1(
    mut v_00_u03b2_880_: *mut crate::leanh::LeanObject,
    mut v_a_881_: *mut crate::leanh::LeanObject,
    mut v_x_882_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_883_: u8 = 0;
    v___x_883_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0_spec__1___redArg(v_a_881_, v_x_882_);
    return v___x_883_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0_spec__1___boxed(
    mut v_00_u03b2_884_: *mut crate::leanh::LeanObject,
    mut v_a_885_: *mut crate::leanh::LeanObject,
    mut v_x_886_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_887_: u8 = 0;
    let mut v_r_888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_887_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitExpr_spec__0_spec__1(v_00_u03b2_884_, v_a_885_, v_x_886_);
    crate::leanh::lean_dec(v_x_886_);
    crate::leanh::lean_dec_ref(v_a_885_);
    v_r_888_ = crate::leanh::lean_box((v_res_887_) as usize);
    return v_r_888_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitExpr_spec__1_spec__3(
    mut v_00_u03b2_889_: *mut crate::leanh::LeanObject,
    mut v_data_890_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_891_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitExpr_spec__1_spec__3___redArg(v_data_890_);
    return v___x_891_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitExpr_spec__1_spec__3_spec__4(
    mut v_00_u03b2_892_: *mut crate::leanh::LeanObject,
    mut v_i_893_: *mut crate::leanh::LeanObject,
    mut v_source_894_: *mut crate::leanh::LeanObject,
    mut v_target_895_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_896_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitExpr_spec__1_spec__3_spec__4___redArg(v_i_893_, v_source_894_, v_target_895_);
    return v___x_896_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitExpr_spec__1_spec__3_spec__4_spec__5(
    mut v_00_u03b2_897_: *mut crate::leanh::LeanObject,
    mut v_x_898_: *mut crate::leanh::LeanObject,
    mut v_x_899_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_900_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_CollectLevelParams_visitExpr_spec__1_spec__3_spec__4_spec__5___redArg(v_x_898_, v_x_899_);
    return v___x_900_;
}
pub unsafe fn l___private_Lean_Util_CollectLevelParams_0__Lean_CollectLevelParams_State_getUnusedLevelParam_loop(
    mut v_s_901_: *mut crate::leanh::LeanObject,
    mut v_pre_902_: *mut crate::leanh::LeanObject,
    mut v_i_903_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_visitedLevel_904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_907_: u8 = 0;
    let mut v___x_908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_visitedLevel_904_ = crate::leanh::lean_ctor_get(v_s_901_, 0);
                crate::leanh::lean_inc(v_i_903_);
                crate::leanh::lean_inc(v_pre_902_);
                v___x_905_ = lean_name_append_index_after(v_pre_902_, v_i_903_);
                v_v_906_ = l_Lean_mkLevelParam(v___x_905_);
                v___x_907_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0___redArg(v_visitedLevel_904_, v_v_906_);
                if v___x_907_ == 0 {
                    crate::leanh::lean_dec(v_i_903_);
                    crate::leanh::lean_dec(v_pre_902_);
                    return v_v_906_;
                } else {
                    crate::leanh::lean_dec(v_v_906_);
                    v___x_908_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_909_ = lean_nat_add(v_i_903_, v___x_908_);
                    crate::leanh::lean_dec(v_i_903_);
                    v_i_903_ = v___x_909_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_CollectLevelParams_0__Lean_CollectLevelParams_State_getUnusedLevelParam_loop___boxed(
    mut v_s_911_: *mut crate::leanh::LeanObject,
    mut v_pre_912_: *mut crate::leanh::LeanObject,
    mut v_i_913_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_914_ = l___private_Lean_Util_CollectLevelParams_0__Lean_CollectLevelParams_State_getUnusedLevelParam_loop(v_s_911_, v_pre_912_, v_i_913_);
    crate::leanh::lean_dec_ref(v_s_911_);
    return v_res_914_;
}
pub unsafe fn l_Lean_CollectLevelParams_State_getUnusedLevelParam(
    mut v_s_915_: *mut crate::leanh::LeanObject,
    mut v_pre_916_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_visitedLevel_917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_919_: u8 = 0;
    v_visitedLevel_917_ = crate::leanh::lean_ctor_get(v_s_915_, 0);
    crate::leanh::lean_inc(v_pre_916_);
    v_v_918_ = l_Lean_mkLevelParam(v_pre_916_);
    v___x_919_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_CollectLevelParams_visitLevel_spec__0___redArg(v_visitedLevel_917_, v_v_918_);
    if v___x_919_ == 0 {
        crate::leanh::lean_dec(v_pre_916_);
        return v_v_918_;
    } else {
        let mut v___x_920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_v_918_);
        v___x_920_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_921_ = l___private_Lean_Util_CollectLevelParams_0__Lean_CollectLevelParams_State_getUnusedLevelParam_loop(v_s_915_, v_pre_916_, v___x_920_);
        return v___x_921_;
    }
}
pub unsafe fn l_Lean_CollectLevelParams_State_getUnusedLevelParam___boxed(
    mut v_s_922_: *mut crate::leanh::LeanObject,
    mut v_pre_923_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_924_ = l_Lean_CollectLevelParams_State_getUnusedLevelParam(v_s_922_, v_pre_923_);
    crate::leanh::lean_dec_ref(v_s_922_);
    return v_res_924_;
}
pub unsafe fn l_Lean_collectLevelParams(
    mut v_s_925_: *mut crate::leanh::LeanObject,
    mut v_e_926_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_927_ = l_Lean_CollectLevelParams_main(v_e_926_, v_s_925_);
    return v___x_927_;
}
pub unsafe fn l_Lean_CollectLevelParams_State_collect(
    mut v_s_928_: *mut crate::leanh::LeanObject,
    mut v_e_929_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_930_ = l_Lean_CollectLevelParams_main(v_e_929_, v_s_928_);
    return v___x_930_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Util_CollectLevelParams(
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
    l_Lean_CollectLevelParams_instInhabitedState =
        _init_l_Lean_CollectLevelParams_instInhabitedState();
    crate::leanh::lean_mark_persistent(l_Lean_CollectLevelParams_instInhabitedState);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Util_CollectLevelParams(
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
pub unsafe fn initialize_Lean_Util_CollectLevelParams(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
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
    res = runtime_initialize_Lean_Util_CollectLevelParams(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Util_CollectLevelParams(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Util_CollectLevelParams(builtin);
}
