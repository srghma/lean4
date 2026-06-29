// Lean compiler output
// Module: Lean.Util.NumApps
// Imports: Lean.Expr Lean.Util.PtrSet
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg,
};
use crate::r#gen::Lean::Expr::{
    initialize_Lean_Expr, l_Lean_Expr_getAppNumArgs, l_Lean_Expr_sort___override,
    runtime_initialize_Lean_Expr,
};
use crate::r#gen::Lean::Util::PtrSet::{
    initialize_Lean_Util_PtrSet, l_Lean_mkPtrSet___redArg, runtime_initialize_Lean_Util_PtrSet,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_fswap, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::{lean_array_fset, lean_array_set};
use crate::lean_imports_rs::Init::Data::Nat::Bitwise::Basic::lean_nat_shiftr;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
    lean_usize_to_uint64,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_of_nat, lean_usize_sub,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_size, lean_array_push, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_sub,
    lean_uint64_mix_hash, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::Util::lean_ptr_addr;
static mut l_Lean_Expr_NumApps_visit___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Expr_NumApps_visit___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Expr_NumApps_main___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Expr_NumApps_main___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Expr_NumApps_main___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Expr_NumApps_main___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Expr_numApps___closed__0_value: crate::leanh::LeanArrayObject<0> =
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
static mut l_Lean_Expr_numApps___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_numApps___closed__0_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumApps_visit_spec__2_spec__3_spec__4_spec__6___redArg(
    mut v_x_498_: *mut crate::leanh::LeanObject,
    mut v_x_499_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_505_: u8 = 0;
    let mut v___x_506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_507_: usize = 0;
    let mut v___x_508_: u64 = 0;
    let mut v___x_509_: u64 = 0;
    let mut v___x_510_: u64 = 0;
    let mut v___x_511_: u64 = 0;
    let mut v___x_512_: u64 = 0;
    let mut v_fold_513_: u64 = 0;
    let mut v___x_514_: u64 = 0;
    let mut v___x_515_: u64 = 0;
    let mut v___x_516_: u64 = 0;
    let mut v___x_517_: usize = 0;
    let mut v___x_518_: usize = 0;
    let mut v___x_519_: usize = 0;
    let mut v___x_520_: usize = 0;
    let mut v___x_521_: usize = 0;
    let mut v___x_522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_528_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_499_) == 0 {
                    return v_x_498_;
                } else {
                    v_key_500_ = crate::leanh::lean_ctor_get(v_x_499_, 0);
                    v_value_501_ = crate::leanh::lean_ctor_get(v_x_499_, 1);
                    v_tail_502_ = crate::leanh::lean_ctor_get(v_x_499_, 2);
                    v_isSharedCheck_528_ = (!crate::leanh::lean_is_exclusive(v_x_499_)) as u8;
                    if v_isSharedCheck_528_ == 0 {
                        v___x_504_ = v_x_499_;
                        v_isShared_505_ = v_isSharedCheck_528_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_502_);
                        crate::leanh::lean_inc(v_value_501_);
                        crate::leanh::lean_inc(v_key_500_);
                        crate::leanh::lean_dec(v_x_499_);
                        v___x_504_ = crate::leanh::lean_box(0);
                        v_isShared_505_ = v_isSharedCheck_528_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_506_ = lean_array_get_size(v_x_498_);
                v___x_507_ = lean_ptr_addr(v_key_500_);
                v___x_508_ = lean_usize_to_uint64(v___x_507_);
                v___x_509_ = 11u64;
                v___x_510_ = lean_uint64_mix_hash(v___x_508_, v___x_509_);
                v___x_511_ = 32u64;
                v___x_512_ = lean_uint64_shift_right(v___x_510_, v___x_511_);
                v_fold_513_ = lean_uint64_xor(v___x_510_, v___x_512_);
                v___x_514_ = 16u64;
                v___x_515_ = lean_uint64_shift_right(v_fold_513_, v___x_514_);
                v___x_516_ = lean_uint64_xor(v_fold_513_, v___x_515_);
                v___x_517_ = lean_uint64_to_usize(v___x_516_);
                v___x_518_ = lean_usize_of_nat(v___x_506_);
                v___x_519_ = 1usize;
                v___x_520_ = lean_usize_sub(v___x_518_, v___x_519_);
                v___x_521_ = lean_usize_land(v___x_517_, v___x_520_);
                v___x_522_ = lean_array_uget_borrowed(v_x_498_, v___x_521_);
                crate::leanh::lean_inc(v___x_522_);
                if v_isShared_505_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_504_, 2, v___x_522_);
                    v___x_524_ = v___x_504_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_527_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_527_, 0, v_key_500_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_527_, 1, v_value_501_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_527_, 2, v___x_522_);
                    v___x_524_ = v_reuseFailAlloc_527_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_525_ = lean_array_uset(v_x_498_, v___x_521_, v___x_524_);
                v_x_498_ = v___x_525_;
                v_x_499_ = v_tail_502_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumApps_visit_spec__2_spec__3_spec__4___redArg(
    mut v_i_529_: *mut crate::leanh::LeanObject,
    mut v_source_530_: *mut crate::leanh::LeanObject,
    mut v_target_531_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_533_: u8 = 0;
    let mut v_es_534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_532_ = lean_array_get_size(v_source_530_);
                v___x_533_ = lean_nat_dec_lt(v_i_529_, v___x_532_);
                if v___x_533_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_530_);
                    crate::leanh::lean_dec(v_i_529_);
                    return v_target_531_;
                } else {
                    v_es_534_ = lean_array_fget(v_source_530_, v_i_529_);
                    v___x_535_ = crate::leanh::lean_box(0);
                    v_source_536_ = lean_array_fset(v_source_530_, v_i_529_, v___x_535_);
                    v_target_537_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumApps_visit_spec__2_spec__3_spec__4_spec__6___redArg(v_target_531_, v_es_534_);
                    v___x_538_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_539_ = lean_nat_add(v_i_529_, v___x_538_);
                    crate::leanh::lean_dec(v_i_529_);
                    v_i_529_ = v___x_539_;
                    v_source_530_ = v_source_536_;
                    v_target_531_ = v_target_537_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumApps_visit_spec__2_spec__3___redArg(
    mut v_data_541_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_542_ = lean_array_get_size(v_data_541_);
    v___x_543_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_544_ = lean_nat_mul(v___x_542_, v___x_543_);
    v___x_545_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_546_ = crate::leanh::lean_box(0);
    v___x_547_ = lean_mk_array(v_nbuckets_544_, v___x_546_);
    v___x_548_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumApps_visit_spec__2_spec__3_spec__4___redArg(v___x_545_, v_data_541_, v___x_547_);
    return v___x_548_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1_spec__1___redArg(
    mut v_a_549_: *mut crate::leanh::LeanObject,
    mut v_x_550_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_551_: u8 = 0;
    let mut v_key_552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_554_: usize = 0;
    let mut v___x_555_: usize = 0;
    let mut v___x_556_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_550_) == 0 {
                    v___x_551_ = 0;
                    return v___x_551_;
                } else {
                    v_key_552_ = crate::leanh::lean_ctor_get(v_x_550_, 0);
                    v_tail_553_ = crate::leanh::lean_ctor_get(v_x_550_, 2);
                    v___x_554_ = lean_ptr_addr(v_key_552_);
                    v___x_555_ = lean_ptr_addr(v_a_549_);
                    v___x_556_ = lean_usize_dec_eq(v___x_554_, v___x_555_);
                    if v___x_556_ == 0 {
                        v_x_550_ = v_tail_553_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_556_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1_spec__1___redArg___boxed(
    mut v_a_558_: *mut crate::leanh::LeanObject,
    mut v_x_559_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_560_: u8 = 0;
    let mut v_r_561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_560_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1_spec__1___redArg(v_a_558_, v_x_559_);
    crate::leanh::lean_dec(v_x_559_);
    crate::leanh::lean_dec_ref(v_a_558_);
    v_r_561_ = crate::leanh::lean_box((v_res_560_) as usize);
    return v_r_561_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumApps_visit_spec__2___redArg(
    mut v_m_562_: *mut crate::leanh::LeanObject,
    mut v_a_563_: *mut crate::leanh::LeanObject,
    mut v_b_564_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_568_: usize = 0;
    let mut v___x_569_: u64 = 0;
    let mut v___x_570_: u64 = 0;
    let mut v___x_571_: u64 = 0;
    let mut v___x_572_: u64 = 0;
    let mut v___x_573_: u64 = 0;
    let mut v_fold_574_: u64 = 0;
    let mut v___x_575_: u64 = 0;
    let mut v___x_576_: u64 = 0;
    let mut v___x_577_: u64 = 0;
    let mut v___x_578_: usize = 0;
    let mut v___x_579_: usize = 0;
    let mut v___x_580_: usize = 0;
    let mut v___x_581_: usize = 0;
    let mut v___x_582_: usize = 0;
    let mut v_bkt_583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_584_: u8 = 0;
    let mut v___x_586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_587_: u8 = 0;
    let mut v___x_588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_597_: u8 = 0;
    let mut v_val_598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_605_: u8 = 0;
    let mut v_unused_606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_565_ = crate::leanh::lean_ctor_get(v_m_562_, 0);
                v_buckets_566_ = crate::leanh::lean_ctor_get(v_m_562_, 1);
                v___x_567_ = lean_array_get_size(v_buckets_566_);
                v___x_568_ = lean_ptr_addr(v_a_563_);
                v___x_569_ = lean_usize_to_uint64(v___x_568_);
                v___x_570_ = 11u64;
                v___x_571_ = lean_uint64_mix_hash(v___x_569_, v___x_570_);
                v___x_572_ = 32u64;
                v___x_573_ = lean_uint64_shift_right(v___x_571_, v___x_572_);
                v_fold_574_ = lean_uint64_xor(v___x_571_, v___x_573_);
                v___x_575_ = 16u64;
                v___x_576_ = lean_uint64_shift_right(v_fold_574_, v___x_575_);
                v___x_577_ = lean_uint64_xor(v_fold_574_, v___x_576_);
                v___x_578_ = lean_uint64_to_usize(v___x_577_);
                v___x_579_ = lean_usize_of_nat(v___x_567_);
                v___x_580_ = 1usize;
                v___x_581_ = lean_usize_sub(v___x_579_, v___x_580_);
                v___x_582_ = lean_usize_land(v___x_578_, v___x_581_);
                v_bkt_583_ = lean_array_uget_borrowed(v_buckets_566_, v___x_582_);
                v___x_584_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1_spec__1___redArg(v_a_563_, v_bkt_583_);
                if v___x_584_ == 0 {
                    crate::leanh::lean_inc_ref(v_buckets_566_);
                    crate::leanh::lean_inc(v_size_565_);
                    v_isSharedCheck_605_ = (!crate::leanh::lean_is_exclusive(v_m_562_)) as u8;
                    if v_isSharedCheck_605_ == 0 {
                        v_unused_606_ = crate::leanh::lean_ctor_get(v_m_562_, 1);
                        crate::leanh::lean_dec(v_unused_606_);
                        v_unused_607_ = crate::leanh::lean_ctor_get(v_m_562_, 0);
                        crate::leanh::lean_dec(v_unused_607_);
                        v___x_586_ = v_m_562_;
                        v_isShared_587_ = v_isSharedCheck_605_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_562_);
                        v___x_586_ = crate::leanh::lean_box(0);
                        v_isShared_587_ = v_isSharedCheck_605_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_b_564_);
                    crate::leanh::lean_dec_ref(v_a_563_);
                    return v_m_562_;
                }
            }
            1 => {
                v___x_588_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_589_ = lean_nat_add(v_size_565_, v___x_588_);
                crate::leanh::lean_dec(v_size_565_);
                crate::leanh::lean_inc(v_bkt_583_);
                v___x_590_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_590_, 0, v_a_563_);
                crate::leanh::lean_ctor_set(v___x_590_, 1, v_b_564_);
                crate::leanh::lean_ctor_set(v___x_590_, 2, v_bkt_583_);
                v_buckets_x27_591_ = lean_array_uset(v_buckets_566_, v___x_582_, v___x_590_);
                v___x_592_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_593_ = lean_nat_mul(v_size_x27_589_, v___x_592_);
                v___x_594_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_595_ = lean_nat_div(v___x_593_, v___x_594_);
                crate::leanh::lean_dec(v___x_593_);
                v___x_596_ = lean_array_get_size(v_buckets_x27_591_);
                v___x_597_ = lean_nat_dec_le(v___x_595_, v___x_596_);
                crate::leanh::lean_dec(v___x_595_);
                if v___x_597_ == 0 {
                    v_val_598_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumApps_visit_spec__2_spec__3___redArg(v_buckets_x27_591_);
                    if v_isShared_587_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_586_, 1, v_val_598_);
                        crate::leanh::lean_ctor_set(v___x_586_, 0, v_size_x27_589_);
                        v___x_600_ = v___x_586_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_601_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_601_, 0, v_size_x27_589_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_601_, 1, v_val_598_);
                        v___x_600_ = v_reuseFailAlloc_601_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_587_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_586_, 1, v_buckets_x27_591_);
                        crate::leanh::lean_ctor_set(v___x_586_, 0, v_size_x27_589_);
                        v___x_603_ = v___x_586_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_604_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_604_, 0, v_size_x27_589_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_604_, 1, v_buckets_x27_591_);
                        v___x_603_ = v_reuseFailAlloc_604_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_600_;
            }
            3 => {
                return v___x_603_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1___redArg(
    mut v_m_608_: *mut crate::leanh::LeanObject,
    mut v_a_609_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_buckets_610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_612_: usize = 0;
    let mut v___x_613_: u64 = 0;
    let mut v___x_614_: u64 = 0;
    let mut v___x_615_: u64 = 0;
    let mut v___x_616_: u64 = 0;
    let mut v___x_617_: u64 = 0;
    let mut v_fold_618_: u64 = 0;
    let mut v___x_619_: u64 = 0;
    let mut v___x_620_: u64 = 0;
    let mut v___x_621_: u64 = 0;
    let mut v___x_622_: usize = 0;
    let mut v___x_623_: usize = 0;
    let mut v___x_624_: usize = 0;
    let mut v___x_625_: usize = 0;
    let mut v___x_626_: usize = 0;
    let mut v___x_627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_628_: u8 = 0;
    v_buckets_610_ = crate::leanh::lean_ctor_get(v_m_608_, 1);
    v___x_611_ = lean_array_get_size(v_buckets_610_);
    v___x_612_ = lean_ptr_addr(v_a_609_);
    v___x_613_ = lean_usize_to_uint64(v___x_612_);
    v___x_614_ = 11u64;
    v___x_615_ = lean_uint64_mix_hash(v___x_613_, v___x_614_);
    v___x_616_ = 32u64;
    v___x_617_ = lean_uint64_shift_right(v___x_615_, v___x_616_);
    v_fold_618_ = lean_uint64_xor(v___x_615_, v___x_617_);
    v___x_619_ = 16u64;
    v___x_620_ = lean_uint64_shift_right(v_fold_618_, v___x_619_);
    v___x_621_ = lean_uint64_xor(v_fold_618_, v___x_620_);
    v___x_622_ = lean_uint64_to_usize(v___x_621_);
    v___x_623_ = lean_usize_of_nat(v___x_611_);
    v___x_624_ = 1usize;
    v___x_625_ = lean_usize_sub(v___x_623_, v___x_624_);
    v___x_626_ = lean_usize_land(v___x_622_, v___x_625_);
    v___x_627_ = lean_array_uget_borrowed(v_buckets_610_, v___x_626_);
    v___x_628_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1_spec__1___redArg(v_a_609_, v___x_627_);
    return v___x_628_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1___redArg___boxed(
    mut v_m_629_: *mut crate::leanh::LeanObject,
    mut v_a_630_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_631_: u8 = 0;
    let mut v_r_632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_631_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1___redArg(v_m_629_, v_a_630_);
    crate::leanh::lean_dec_ref(v_a_630_);
    crate::leanh::lean_dec_ref(v_m_629_);
    v_r_632_ = crate::leanh::lean_box((v_res_631_) as usize);
    return v_r_632_;
}
pub unsafe fn _init_l_Lean_Expr_NumApps_visit___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_633_ = crate::leanh::lean_box(0);
    v_dummy_634_ = l_Lean_Expr_sort___override(v___x_633_);
    return v_dummy_634_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Expr_NumApps_visit_spec__3(
    mut v_x_635_: *mut crate::leanh::LeanObject,
    mut v_x_636_: *mut crate::leanh::LeanObject,
    mut v_x_637_: *mut crate::leanh::LeanObject,
    mut v___y_638_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_645_: u8 = 0;
    let mut v___x_646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_649_: u8 = 0;
    let mut v___x_651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_653_: u8 = 0;
    let mut v___x_655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_657_: usize = 0;
    let mut v___x_658_: usize = 0;
    let mut v___x_659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_660_: usize = 0;
    let mut v___x_661_: usize = 0;
    let mut v___x_662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_663_: u8 = 0;
    let mut v_unused_664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_visited_672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_counters_673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_676_: u8 = 0;
    let mut v___y_678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_688_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_635_) == 5 {
                    v_fn_665_ = crate::leanh::lean_ctor_get(v_x_635_, 0);
                    crate::leanh::lean_inc_ref(v_fn_665_);
                    v_arg_666_ = crate::leanh::lean_ctor_get(v_x_635_, 1);
                    crate::leanh::lean_inc_ref(v_arg_666_);
                    crate::leanh::lean_dec_ref_known(v_x_635_, 2);
                    v___x_667_ = lean_array_set(v_x_636_, v_x_637_, v_arg_666_);
                    v___x_668_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_669_ = lean_nat_sub(v_x_637_, v___x_668_);
                    crate::leanh::lean_dec(v_x_637_);
                    v_x_635_ = v_fn_665_;
                    v_x_636_ = v___x_667_;
                    v_x_637_ = v___x_669_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_x_637_);
                    if crate::leanh::lean_obj_tag(v_x_635_) == 4 {
                        v_declName_671_ = crate::leanh::lean_ctor_get(v_x_635_, 0);
                        v_visited_672_ = crate::leanh::lean_ctor_get(v___y_638_, 0);
                        v_counters_673_ = crate::leanh::lean_ctor_get(v___y_638_, 1);
                        v_isSharedCheck_688_ = (!crate::leanh::lean_is_exclusive(v___y_638_)) as u8;
                        if v_isSharedCheck_688_ == 0 {
                            v___x_675_ = v___y_638_;
                            v_isShared_676_ = v_isSharedCheck_688_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_counters_673_);
                            crate::leanh::lean_inc(v_visited_672_);
                            crate::leanh::lean_dec(v___y_638_);
                            v___x_675_ = crate::leanh::lean_box(0);
                            v_isShared_676_ = v_isSharedCheck_688_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v___y_640_ = v___y_638_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_641_ = l_Lean_Expr_NumApps_visit(v_x_635_, v___y_640_);
                v_snd_642_ = crate::leanh::lean_ctor_get(v___x_641_, 1);
                v_isSharedCheck_663_ = (!crate::leanh::lean_is_exclusive(v___x_641_)) as u8;
                if v_isSharedCheck_663_ == 0 {
                    v_unused_664_ = crate::leanh::lean_ctor_get(v___x_641_, 0);
                    crate::leanh::lean_dec(v_unused_664_);
                    v___x_644_ = v___x_641_;
                    v_isShared_645_ = v_isSharedCheck_663_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_642_);
                    crate::leanh::lean_dec(v___x_641_);
                    v___x_644_ = crate::leanh::lean_box(0);
                    v_isShared_645_ = v_isSharedCheck_663_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_646_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_647_ = lean_array_get_size(v_x_636_);
                v___x_648_ = crate::leanh::lean_box(0);
                v___x_649_ = lean_nat_dec_lt(v___x_646_, v___x_647_);
                if v___x_649_ == 0 {
                    crate::leanh::lean_dec_ref(v_x_636_);
                    if v_isShared_645_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_644_, 0, v___x_648_);
                        v___x_651_ = v___x_644_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_652_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_652_, 0, v___x_648_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_652_, 1, v_snd_642_);
                        v___x_651_ = v_reuseFailAlloc_652_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___x_653_ = lean_nat_dec_le(v___x_647_, v___x_647_);
                    if v___x_653_ == 0 {
                        if v___x_649_ == 0 {
                            crate::leanh::lean_dec_ref(v_x_636_);
                            if v_isShared_645_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_644_, 0, v___x_648_);
                                v___x_655_ = v___x_644_;
                                state = 4;
                                continue;
                            } else {
                                v_reuseFailAlloc_656_ =
                                    crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_656_, 0, v___x_648_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_656_, 1, v_snd_642_);
                                v___x_655_ = v_reuseFailAlloc_656_;
                                state = 4;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_644_);
                            v___x_657_ = 0usize;
                            v___x_658_ = lean_usize_of_nat(v___x_647_);
                            v___x_659_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Expr_NumApps_visit_spec__0(v_x_636_, v___x_657_, v___x_658_, v___x_648_, v_snd_642_);
                            crate::leanh::lean_dec_ref(v_x_636_);
                            return v___x_659_;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_644_);
                        v___x_660_ = 0usize;
                        v___x_661_ = lean_usize_of_nat(v___x_647_);
                        v___x_662_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Expr_NumApps_visit_spec__0(v_x_636_, v___x_660_, v___x_661_, v___x_648_, v_snd_642_);
                        crate::leanh::lean_dec_ref(v_x_636_);
                        return v___x_662_;
                    }
                }
            }
            3 => {
                return v___x_651_;
            }
            4 => {
                return v___x_655_;
            }
            5 => {
                v___x_685_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_counters_673_, v_declName_671_);
                if crate::leanh::lean_obj_tag(v___x_685_) == 0 {
                    v___x_686_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_678_ = v___x_686_;
                    state = 6;
                    continue;
                } else {
                    v_val_687_ = crate::leanh::lean_ctor_get(v___x_685_, 0);
                    crate::leanh::lean_inc(v_val_687_);
                    crate::leanh::lean_dec_ref_known(v___x_685_, 1);
                    v___y_678_ = v_val_687_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_679_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_680_ = lean_nat_add(v___y_678_, v___x_679_);
                crate::leanh::lean_dec(v___y_678_);
                crate::leanh::lean_inc(v_declName_671_);
                v___x_681_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_declName_671_, v___x_680_, v_counters_673_);
                if v_isShared_676_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_675_, 1, v___x_681_);
                    v___x_683_ = v___x_675_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_684_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_684_, 0, v_visited_672_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_684_, 1, v___x_681_);
                    v___x_683_ = v_reuseFailAlloc_684_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_640_ = v___x_683_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_NumApps_visit(
    mut v_e_689_: *mut crate::leanh::LeanObject,
    mut v_a_690_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_d_692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_visited_698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_counters_699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_700_: u8 = 0;
    let mut v___x_702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_703_: u8 = 0;
    let mut v___x_704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_732_: u8 = 0;
    let mut v_unused_733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_visited_698_ = crate::leanh::lean_ctor_get(v_a_690_, 0);
                v_counters_699_ = crate::leanh::lean_ctor_get(v_a_690_, 1);
                v___x_700_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1___redArg(v_visited_698_, v_e_689_);
                if v___x_700_ == 0 {
                    crate::leanh::lean_inc(v_counters_699_);
                    crate::leanh::lean_inc_ref(v_visited_698_);
                    v_isSharedCheck_732_ = (!crate::leanh::lean_is_exclusive(v_a_690_)) as u8;
                    if v_isSharedCheck_732_ == 0 {
                        v_unused_733_ = crate::leanh::lean_ctor_get(v_a_690_, 1);
                        crate::leanh::lean_dec(v_unused_733_);
                        v_unused_734_ = crate::leanh::lean_ctor_get(v_a_690_, 0);
                        crate::leanh::lean_dec(v_unused_734_);
                        v___x_702_ = v_a_690_;
                        v_isShared_703_ = v_isSharedCheck_732_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_a_690_);
                        v___x_702_ = crate::leanh::lean_box(0);
                        v_isShared_703_ = v_isSharedCheck_732_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_689_);
                    v___x_735_ = crate::leanh::lean_box(0);
                    v___x_736_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_736_, 0, v___x_735_);
                    crate::leanh::lean_ctor_set(v___x_736_, 1, v_a_690_);
                    return v___x_736_;
                }
            }
            1 => {
                v___x_695_ = l_Lean_Expr_NumApps_visit(v_d_692_, v___y_694_);
                v_snd_696_ = crate::leanh::lean_ctor_get(v___x_695_, 1);
                crate::leanh::lean_inc(v_snd_696_);
                crate::leanh::lean_dec_ref(v___x_695_);
                v_e_689_ = v_b_693_;
                v_a_690_ = v_snd_696_;
                state = 0;
                continue;
            }
            2 => {
                v___x_704_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc_ref(v_e_689_);
                v___x_705_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumApps_visit_spec__2___redArg(v_visited_698_, v_e_689_, v___x_704_);
                if v_isShared_703_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_702_, 0, v___x_705_);
                    v___x_707_ = v___x_702_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_731_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_731_, 0, v___x_705_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_731_, 1, v_counters_699_);
                    v___x_707_ = v_reuseFailAlloc_731_;
                    state = 3;
                    continue;
                }
            }
            3 => match crate::leanh::lean_obj_tag(v_e_689_) {
                7 => {
                    v_binderType_708_ = crate::leanh::lean_ctor_get(v_e_689_, 1);
                    crate::leanh::lean_inc_ref(v_binderType_708_);
                    v_body_709_ = crate::leanh::lean_ctor_get(v_e_689_, 2);
                    crate::leanh::lean_inc_ref(v_body_709_);
                    crate::leanh::lean_dec_ref_known(v_e_689_, 3);
                    v_d_692_ = v_binderType_708_;
                    v_b_693_ = v_body_709_;
                    v___y_694_ = v___x_707_;
                    state = 1;
                    continue;
                }
                6 => {
                    v_binderType_710_ = crate::leanh::lean_ctor_get(v_e_689_, 1);
                    crate::leanh::lean_inc_ref(v_binderType_710_);
                    v_body_711_ = crate::leanh::lean_ctor_get(v_e_689_, 2);
                    crate::leanh::lean_inc_ref(v_body_711_);
                    crate::leanh::lean_dec_ref_known(v_e_689_, 3);
                    v_d_692_ = v_binderType_710_;
                    v_b_693_ = v_body_711_;
                    v___y_694_ = v___x_707_;
                    state = 1;
                    continue;
                }
                10 => {
                    v_expr_712_ = crate::leanh::lean_ctor_get(v_e_689_, 1);
                    crate::leanh::lean_inc_ref(v_expr_712_);
                    crate::leanh::lean_dec_ref_known(v_e_689_, 2);
                    v_e_689_ = v_expr_712_;
                    v_a_690_ = v___x_707_;
                    state = 0;
                    continue;
                }
                8 => {
                    v_type_714_ = crate::leanh::lean_ctor_get(v_e_689_, 1);
                    crate::leanh::lean_inc_ref(v_type_714_);
                    v_value_715_ = crate::leanh::lean_ctor_get(v_e_689_, 2);
                    crate::leanh::lean_inc_ref(v_value_715_);
                    v_body_716_ = crate::leanh::lean_ctor_get(v_e_689_, 3);
                    crate::leanh::lean_inc_ref(v_body_716_);
                    crate::leanh::lean_dec_ref_known(v_e_689_, 4);
                    v___x_717_ = l_Lean_Expr_NumApps_visit(v_type_714_, v___x_707_);
                    v_snd_718_ = crate::leanh::lean_ctor_get(v___x_717_, 1);
                    crate::leanh::lean_inc(v_snd_718_);
                    crate::leanh::lean_dec_ref(v___x_717_);
                    v___x_719_ = l_Lean_Expr_NumApps_visit(v_value_715_, v_snd_718_);
                    v_snd_720_ = crate::leanh::lean_ctor_get(v___x_719_, 1);
                    crate::leanh::lean_inc(v_snd_720_);
                    crate::leanh::lean_dec_ref(v___x_719_);
                    v_e_689_ = v_body_716_;
                    v_a_690_ = v_snd_720_;
                    state = 0;
                    continue;
                }
                5 => {
                    v_dummy_722_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Expr_NumApps_visit___closed__0),
                        core::ptr::addr_of_mut!(l_Lean_Expr_NumApps_visit___closed__0_once),
                        _init_l_Lean_Expr_NumApps_visit___closed__0,
                    );
                    v_nargs_723_ = l_Lean_Expr_getAppNumArgs(v_e_689_);
                    crate::leanh::lean_inc(v_nargs_723_);
                    v___x_724_ = lean_mk_array(v_nargs_723_, v_dummy_722_);
                    v___x_725_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_726_ = lean_nat_sub(v_nargs_723_, v___x_725_);
                    crate::leanh::lean_dec(v_nargs_723_);
                    v___x_727_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_NumApps_visit_spec__3(
                        v_e_689_, v___x_724_, v___x_726_, v___x_707_,
                    );
                    return v___x_727_;
                }
                11 => {
                    v_struct_728_ = crate::leanh::lean_ctor_get(v_e_689_, 2);
                    crate::leanh::lean_inc_ref(v_struct_728_);
                    crate::leanh::lean_dec_ref_known(v_e_689_, 3);
                    v_e_689_ = v_struct_728_;
                    v_a_690_ = v___x_707_;
                    state = 0;
                    continue;
                }
                _ => {
                    crate::leanh::lean_dec_ref(v_e_689_);
                    v___x_730_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_730_, 0, v___x_704_);
                    crate::leanh::lean_ctor_set(v___x_730_, 1, v___x_707_);
                    return v___x_730_;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Expr_NumApps_visit_spec__0(
    mut v_as_737_: *mut crate::leanh::LeanObject,
    mut v_i_738_: usize,
    mut v_stop_739_: usize,
    mut v_b_740_: *mut crate::leanh::LeanObject,
    mut v___y_741_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_742_: u8 = 0;
    let mut v___x_743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_747_: usize = 0;
    let mut v___x_748_: usize = 0;
    let mut v___x_750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_742_ = lean_usize_dec_eq(v_i_738_, v_stop_739_);
                if v___x_742_ == 0 {
                    v___x_743_ = lean_array_uget_borrowed(v_as_737_, v_i_738_);
                    crate::leanh::lean_inc(v___x_743_);
                    v___x_744_ = l_Lean_Expr_NumApps_visit(v___x_743_, v___y_741_);
                    v_fst_745_ = crate::leanh::lean_ctor_get(v___x_744_, 0);
                    crate::leanh::lean_inc(v_fst_745_);
                    v_snd_746_ = crate::leanh::lean_ctor_get(v___x_744_, 1);
                    crate::leanh::lean_inc(v_snd_746_);
                    crate::leanh::lean_dec_ref(v___x_744_);
                    v___x_747_ = 1usize;
                    v___x_748_ = lean_usize_add(v_i_738_, v___x_747_);
                    v_i_738_ = v___x_748_;
                    v_b_740_ = v_fst_745_;
                    v___y_741_ = v_snd_746_;
                    state = 0;
                    continue;
                } else {
                    v___x_750_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_750_, 0, v_b_740_);
                    crate::leanh::lean_ctor_set(v___x_750_, 1, v___y_741_);
                    return v___x_750_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Expr_NumApps_visit_spec__0___boxed(
    mut v_as_751_: *mut crate::leanh::LeanObject,
    mut v_i_752_: *mut crate::leanh::LeanObject,
    mut v_stop_753_: *mut crate::leanh::LeanObject,
    mut v_b_754_: *mut crate::leanh::LeanObject,
    mut v___y_755_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_756_: usize = 0;
    let mut v_stop_boxed_757_: usize = 0;
    let mut v_res_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_756_ = crate::leanh::lean_unbox_usize(v_i_752_);
    crate::leanh::lean_dec(v_i_752_);
    v_stop_boxed_757_ = crate::leanh::lean_unbox_usize(v_stop_753_);
    crate::leanh::lean_dec(v_stop_753_);
    v_res_758_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Expr_NumApps_visit_spec__0(v_as_751_, v_i_boxed_756_, v_stop_boxed_757_, v_b_754_, v___y_755_);
    crate::leanh::lean_dec_ref(v_as_751_);
    return v_res_758_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1(
    mut v_00_u03b2_759_: *mut crate::leanh::LeanObject,
    mut v_m_760_: *mut crate::leanh::LeanObject,
    mut v_a_761_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_762_: u8 = 0;
    v___x_762_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1___redArg(v_m_760_, v_a_761_);
    return v___x_762_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1___boxed(
    mut v_00_u03b2_763_: *mut crate::leanh::LeanObject,
    mut v_m_764_: *mut crate::leanh::LeanObject,
    mut v_a_765_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_766_: u8 = 0;
    let mut v_r_767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_766_ =
        l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1(
            v_00_u03b2_763_,
            v_m_764_,
            v_a_765_,
        );
    crate::leanh::lean_dec_ref(v_a_765_);
    crate::leanh::lean_dec_ref(v_m_764_);
    v_r_767_ = crate::leanh::lean_box((v_res_766_) as usize);
    return v_r_767_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumApps_visit_spec__2(
    mut v_00_u03b2_768_: *mut crate::leanh::LeanObject,
    mut v_m_769_: *mut crate::leanh::LeanObject,
    mut v_a_770_: *mut crate::leanh::LeanObject,
    mut v_b_771_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_772_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumApps_visit_spec__2___redArg(v_m_769_, v_a_770_, v_b_771_);
    return v___x_772_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1_spec__1(
    mut v_00_u03b2_773_: *mut crate::leanh::LeanObject,
    mut v_a_774_: *mut crate::leanh::LeanObject,
    mut v_x_775_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_776_: u8 = 0;
    v___x_776_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1_spec__1___redArg(v_a_774_, v_x_775_);
    return v___x_776_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1_spec__1___boxed(
    mut v_00_u03b2_777_: *mut crate::leanh::LeanObject,
    mut v_a_778_: *mut crate::leanh::LeanObject,
    mut v_x_779_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_780_: u8 = 0;
    let mut v_r_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_780_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_NumApps_visit_spec__1_spec__1(v_00_u03b2_777_, v_a_778_, v_x_779_);
    crate::leanh::lean_dec(v_x_779_);
    crate::leanh::lean_dec_ref(v_a_778_);
    v_r_781_ = crate::leanh::lean_box((v_res_780_) as usize);
    return v_r_781_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumApps_visit_spec__2_spec__3(
    mut v_00_u03b2_782_: *mut crate::leanh::LeanObject,
    mut v_data_783_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_784_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumApps_visit_spec__2_spec__3___redArg(v_data_783_);
    return v___x_784_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumApps_visit_spec__2_spec__3_spec__4(
    mut v_00_u03b2_785_: *mut crate::leanh::LeanObject,
    mut v_i_786_: *mut crate::leanh::LeanObject,
    mut v_source_787_: *mut crate::leanh::LeanObject,
    mut v_target_788_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_789_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumApps_visit_spec__2_spec__3_spec__4___redArg(v_i_786_, v_source_787_, v_target_788_);
    return v___x_789_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumApps_visit_spec__2_spec__3_spec__4_spec__6(
    mut v_00_u03b2_790_: *mut crate::leanh::LeanObject,
    mut v_x_791_: *mut crate::leanh::LeanObject,
    mut v_x_792_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_793_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Expr_NumApps_visit_spec__2_spec__3_spec__4_spec__6___redArg(v_x_791_, v_x_792_);
    return v___x_793_;
}
pub unsafe fn _init_l_Lean_Expr_NumApps_main___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_794_ = crate::leanh::lean_unsigned_to_nat(64);
    v___x_795_ = l_Lean_mkPtrSet___redArg(v___x_794_);
    return v___x_795_;
}
pub unsafe fn _init_l_Lean_Expr_NumApps_main___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_796_ = crate::leanh::lean_box(1);
    v___x_797_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Expr_NumApps_main___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Expr_NumApps_main___closed__0_once),
        _init_l_Lean_Expr_NumApps_main___closed__0,
    );
    v___x_798_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_798_, 0, v___x_797_);
    crate::leanh::lean_ctor_set(v___x_798_, 1, v___x_796_);
    return v___x_798_;
}
pub unsafe fn l_Lean_Expr_NumApps_main(
    mut v_e_799_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_counters_803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_800_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Expr_NumApps_main___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Expr_NumApps_main___closed__1_once),
        _init_l_Lean_Expr_NumApps_main___closed__1,
    );
    v___x_801_ = l_Lean_Expr_NumApps_visit(v_e_799_, v___x_800_);
    v_snd_802_ = crate::leanh::lean_ctor_get(v___x_801_, 1);
    crate::leanh::lean_inc(v_snd_802_);
    crate::leanh::lean_dec_ref(v___x_801_);
    v_counters_803_ = crate::leanh::lean_ctor_get(v_snd_802_, 1);
    crate::leanh::lean_inc(v_counters_803_);
    crate::leanh::lean_dec(v_snd_802_);
    return v_counters_803_;
}
pub unsafe fn l___private_Lean_Util_NumApps_0__Lean_Expr_numApps_unsafe__1(
    mut v_e_804_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_805_ = l_Lean_Expr_NumApps_main(v_e_804_);
    return v___x_805_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Expr_numApps_spec__1(
    mut v_threshold_806_: *mut crate::leanh::LeanObject,
    mut v_init_807_: *mut crate::leanh::LeanObject,
    mut v_x_808_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_d_811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_822_: u8 = 0;
    let mut v_a_823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_808_) == 0 {
                    v_k_814_ = crate::leanh::lean_ctor_get(v_x_808_, 1);
                    v_v_815_ = crate::leanh::lean_ctor_get(v_x_808_, 2);
                    v_l_816_ = crate::leanh::lean_ctor_get(v_x_808_, 3);
                    v_r_817_ = crate::leanh::lean_ctor_get(v_x_808_, 4);
                    v___x_818_ =
                        l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Expr_numApps_spec__1(
                            v_threshold_806_,
                            v_init_807_,
                            v_l_816_,
                        );
                    v_a_819_ = crate::leanh::lean_ctor_get(v___x_818_, 0);
                    crate::leanh::lean_inc(v_a_819_);
                    if crate::leanh::lean_obj_tag(v_a_819_) == 0 {
                        crate::leanh::lean_dec_ref(v___x_818_);
                        v_a_820_ = crate::leanh::lean_ctor_get(v_a_819_, 0);
                        crate::leanh::lean_inc(v_a_820_);
                        crate::leanh::lean_dec_ref_known(v_a_819_, 1);
                        v_d_811_ = v_a_820_;
                        state = 1;
                        continue;
                    } else {
                        v_a_821_ = crate::leanh::lean_ctor_get(v_a_819_, 0);
                        crate::leanh::lean_inc(v_a_821_);
                        crate::leanh::lean_dec_ref_known(v_a_819_, 1);
                        v___x_822_ = lean_nat_dec_lt(v_threshold_806_, v_v_815_);
                        if v___x_822_ == 0 {
                            crate::leanh::lean_dec(v_a_821_);
                            v_a_823_ = crate::leanh::lean_ctor_get(v___x_818_, 0);
                            crate::leanh::lean_inc(v_a_823_);
                            crate::leanh::lean_dec_ref(v___x_818_);
                            if crate::leanh::lean_obj_tag(v_a_823_) == 0 {
                                v_a_824_ = crate::leanh::lean_ctor_get(v_a_823_, 0);
                                crate::leanh::lean_inc(v_a_824_);
                                crate::leanh::lean_dec_ref_known(v_a_823_, 1);
                                v_d_811_ = v_a_824_;
                                state = 1;
                                continue;
                            } else {
                                v_a_825_ = crate::leanh::lean_ctor_get(v_a_823_, 0);
                                crate::leanh::lean_inc(v_a_825_);
                                crate::leanh::lean_dec_ref_known(v_a_823_, 1);
                                v_init_807_ = v_a_825_;
                                v_x_808_ = v_r_817_;
                                state = 0;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_818_);
                            crate::leanh::lean_inc(v_v_815_);
                            crate::leanh::lean_inc(v_k_814_);
                            v___x_827_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_827_, 0, v_k_814_);
                            crate::leanh::lean_ctor_set(v___x_827_, 1, v_v_815_);
                            v___x_828_ = lean_array_push(v_a_821_, v___x_827_);
                            v_init_807_ = v___x_828_;
                            v_x_808_ = v_r_817_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_830_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_830_, 0, v_init_807_);
                    v___x_831_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_831_, 0, v___x_830_);
                    return v___x_831_;
                }
            }
            1 => {
                v___x_812_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_812_, 0, v_d_811_);
                v___x_813_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_813_, 0, v___x_812_);
                return v___x_813_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Expr_numApps_spec__1___boxed(
    mut v_threshold_832_: *mut crate::leanh::LeanObject,
    mut v_init_833_: *mut crate::leanh::LeanObject,
    mut v_x_834_: *mut crate::leanh::LeanObject,
    mut v___y_835_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_836_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Expr_numApps_spec__1(
        v_threshold_832_,
        v_init_833_,
        v_x_834_,
    );
    crate::leanh::lean_dec(v_x_834_);
    crate::leanh::lean_dec(v_threshold_832_);
    return v_res_836_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0_spec__0___redArg(
    mut v_hi_837_: *mut crate::leanh::LeanObject,
    mut v_pivot_838_: *mut crate::leanh::LeanObject,
    mut v_as_839_: *mut crate::leanh::LeanObject,
    mut v_i_840_: *mut crate::leanh::LeanObject,
    mut v_k_841_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_842_: u8 = 0;
    let mut v___x_843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_848_: u8 = 0;
    let mut v___x_849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_842_ = lean_nat_dec_lt(v_k_841_, v_hi_837_);
                if v___x_842_ == 0 {
                    crate::leanh::lean_dec(v_k_841_);
                    v___x_843_ = lean_array_fswap(v_as_839_, v_i_840_, v_hi_837_);
                    v___x_844_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_844_, 0, v_i_840_);
                    crate::leanh::lean_ctor_set(v___x_844_, 1, v___x_843_);
                    return v___x_844_;
                } else {
                    v_snd_845_ = crate::leanh::lean_ctor_get(v_pivot_838_, 1);
                    v___x_846_ = lean_array_fget_borrowed(v_as_839_, v_k_841_);
                    v_snd_847_ = crate::leanh::lean_ctor_get(v___x_846_, 1);
                    v___x_848_ = lean_nat_dec_lt(v_snd_845_, v_snd_847_);
                    if v___x_848_ == 0 {
                        v___x_849_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_850_ = lean_nat_add(v_k_841_, v___x_849_);
                        crate::leanh::lean_dec(v_k_841_);
                        v_k_841_ = v___x_850_;
                        state = 0;
                        continue;
                    } else {
                        v___x_852_ = lean_array_fswap(v_as_839_, v_i_840_, v_k_841_);
                        v___x_853_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_854_ = lean_nat_add(v_i_840_, v___x_853_);
                        crate::leanh::lean_dec(v_i_840_);
                        v___x_855_ = lean_nat_add(v_k_841_, v___x_853_);
                        crate::leanh::lean_dec(v_k_841_);
                        v_as_839_ = v___x_852_;
                        v_i_840_ = v___x_854_;
                        v_k_841_ = v___x_855_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0_spec__0___redArg___boxed(
    mut v_hi_857_: *mut crate::leanh::LeanObject,
    mut v_pivot_858_: *mut crate::leanh::LeanObject,
    mut v_as_859_: *mut crate::leanh::LeanObject,
    mut v_i_860_: *mut crate::leanh::LeanObject,
    mut v_k_861_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_862_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0_spec__0___redArg(v_hi_857_, v_pivot_858_, v_as_859_, v_i_860_, v_k_861_);
    crate::leanh::lean_dec_ref(v_pivot_858_);
    crate::leanh::lean_dec(v_hi_857_);
    return v_res_862_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg___lam__0(
    mut v_a_863_: *mut crate::leanh::LeanObject,
    mut v_b_864_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_snd_865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_867_: u8 = 0;
    v_snd_865_ = crate::leanh::lean_ctor_get(v_b_864_, 1);
    v_snd_866_ = crate::leanh::lean_ctor_get(v_a_863_, 1);
    v___x_867_ = lean_nat_dec_lt(v_snd_865_, v_snd_866_);
    return v___x_867_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg___lam__0___boxed(
    mut v_a_868_: *mut crate::leanh::LeanObject,
    mut v_b_869_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_870_: u8 = 0;
    let mut v_r_871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_870_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg___lam__0(v_a_868_, v_b_869_);
    crate::leanh::lean_dec_ref(v_b_869_);
    crate::leanh::lean_dec_ref(v_a_868_);
    v_r_871_ = crate::leanh::lean_box((v_res_870_) as usize);
    return v_r_871_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg(
    mut v_n_872_: *mut crate::leanh::LeanObject,
    mut v_as_873_: *mut crate::leanh::LeanObject,
    mut v_lo_874_: *mut crate::leanh::LeanObject,
    mut v_hi_875_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pivot_878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_882_: u8 = 0;
    let mut v___x_883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_887_: u8 = 0;
    let mut v___x_888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mid_890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_895_: u8 = 0;
    let mut v___x_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_901_: u8 = 0;
    let mut v___x_902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_905_: u8 = 0;
    let mut v___x_906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_887_ = lean_nat_dec_lt(v_lo_874_, v_hi_875_);
                if v___x_887_ == 0 {
                    crate::leanh::lean_dec(v_lo_874_);
                    return v_as_873_;
                } else {
                    v___x_888_ = lean_nat_add(v_lo_874_, v_hi_875_);
                    v___x_889_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_mid_890_ = lean_nat_shiftr(v___x_888_, v___x_889_);
                    crate::leanh::lean_dec(v___x_888_);
                    v___x_903_ = lean_array_fget_borrowed(v_as_873_, v_mid_890_);
                    v___x_904_ = lean_array_fget_borrowed(v_as_873_, v_lo_874_);
                    v___x_905_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg___lam__0(v___x_903_, v___x_904_);
                    if v___x_905_ == 0 {
                        v___y_898_ = v_as_873_;
                        state = 3;
                        continue;
                    } else {
                        v___x_906_ = lean_array_fswap(v_as_873_, v_lo_874_, v_mid_890_);
                        v___y_898_ = v___x_906_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_pivot_878_ = lean_array_fget(v___y_877_, v_hi_875_);
                crate::leanh::lean_inc_n(v_lo_874_, 2);
                v___x_879_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0_spec__0___redArg(v_hi_875_, v_pivot_878_, v___y_877_, v_lo_874_, v_lo_874_);
                crate::leanh::lean_dec(v_pivot_878_);
                v_fst_880_ = crate::leanh::lean_ctor_get(v___x_879_, 0);
                crate::leanh::lean_inc(v_fst_880_);
                v_snd_881_ = crate::leanh::lean_ctor_get(v___x_879_, 1);
                crate::leanh::lean_inc(v_snd_881_);
                crate::leanh::lean_dec_ref(v___x_879_);
                v___x_882_ = lean_nat_dec_le(v_hi_875_, v_fst_880_);
                if v___x_882_ == 0 {
                    v___x_883_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg(v_n_872_, v_snd_881_, v_lo_874_, v_fst_880_);
                    v___x_884_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_885_ = lean_nat_add(v_fst_880_, v___x_884_);
                    crate::leanh::lean_dec(v_fst_880_);
                    v_as_873_ = v___x_883_;
                    v_lo_874_ = v___x_885_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_fst_880_);
                    crate::leanh::lean_dec(v_lo_874_);
                    return v_snd_881_;
                }
            }
            2 => {
                v___x_893_ = lean_array_fget_borrowed(v___y_892_, v_mid_890_);
                v___x_894_ = lean_array_fget_borrowed(v___y_892_, v_hi_875_);
                v___x_895_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg___lam__0(v___x_893_, v___x_894_);
                if v___x_895_ == 0 {
                    crate::leanh::lean_dec(v_mid_890_);
                    v___y_877_ = v___y_892_;
                    state = 1;
                    continue;
                } else {
                    v___x_896_ = lean_array_fswap(v___y_892_, v_mid_890_, v_hi_875_);
                    crate::leanh::lean_dec(v_mid_890_);
                    v___y_877_ = v___x_896_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_899_ = lean_array_fget_borrowed(v___y_898_, v_hi_875_);
                v___x_900_ = lean_array_fget_borrowed(v___y_898_, v_lo_874_);
                v___x_901_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg___lam__0(v___x_899_, v___x_900_);
                if v___x_901_ == 0 {
                    v___y_892_ = v___y_898_;
                    state = 2;
                    continue;
                } else {
                    v___x_902_ = lean_array_fswap(v___y_898_, v_lo_874_, v_hi_875_);
                    v___y_892_ = v___x_902_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg___boxed(
    mut v_n_907_: *mut crate::leanh::LeanObject,
    mut v_as_908_: *mut crate::leanh::LeanObject,
    mut v_lo_909_: *mut crate::leanh::LeanObject,
    mut v_hi_910_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_911_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg(v_n_907_, v_as_908_, v_lo_909_, v_hi_910_);
    crate::leanh::lean_dec(v_hi_910_);
    crate::leanh::lean_dec(v_n_907_);
    return v_res_911_;
}
pub unsafe fn l_Lean_Expr_numApps(
    mut v_e_914_: *mut crate::leanh::LeanObject,
    mut v_threshold_915_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_929_: u8 = 0;
    let mut v_counters_930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_937_: u8 = 0;
    let mut v___y_939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_942_: u8 = 0;
    let mut v___x_943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_945_: u8 = 0;
    let mut v_a_946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_950_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_counters_930_ = l_Lean_Expr_NumApps_main(v_e_914_);
                v___x_931_ = crate::leanh::lean_unsigned_to_nat(0);
                v_result_932_ = l_Lean_Expr_numApps___closed__0;
                v___x_933_ =
                    l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Expr_numApps_spec__1(
                        v_threshold_915_,
                        v_result_932_,
                        v_counters_930_,
                    );
                crate::leanh::lean_dec(v_counters_930_);
                v_a_934_ = crate::leanh::lean_ctor_get(v___x_933_, 0);
                v_isSharedCheck_950_ = (!crate::leanh::lean_is_exclusive(v___x_933_)) as u8;
                if v_isSharedCheck_950_ == 0 {
                    v___x_936_ = v___x_933_;
                    v_isShared_937_ = v_isSharedCheck_950_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_934_);
                    crate::leanh::lean_dec(v___x_933_);
                    v___x_936_ = crate::leanh::lean_box(0);
                    v_isShared_937_ = v_isSharedCheck_950_;
                    state = 3;
                    continue;
                }
            }
            1 => {
                v___x_922_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg(v___y_919_, v___y_918_, v___y_920_, v___y_921_);
                crate::leanh::lean_dec(v___y_921_);
                crate::leanh::lean_dec(v___y_919_);
                v___x_923_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_923_, 0, v___x_922_);
                return v___x_923_;
            }
            2 => {
                v___x_929_ = lean_nat_dec_le(v___y_928_, v___y_925_);
                if v___x_929_ == 0 {
                    crate::leanh::lean_dec(v___y_925_);
                    crate::leanh::lean_inc(v___y_928_);
                    v___y_918_ = v___y_926_;
                    v___y_919_ = v___y_927_;
                    v___y_920_ = v___y_928_;
                    v___y_921_ = v___y_928_;
                    state = 1;
                    continue;
                } else {
                    v___y_918_ = v___y_926_;
                    v___y_919_ = v___y_927_;
                    v___y_920_ = v___y_928_;
                    v___y_921_ = v___y_925_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v_a_946_ = crate::leanh::lean_ctor_get(v_a_934_, 0);
                crate::leanh::lean_inc_n(v_a_946_, 2);
                crate::leanh::lean_dec(v_a_934_);
                if v_isShared_937_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_936_, 0, v_a_946_);
                    v___x_948_ = v___x_936_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_949_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_949_, 0, v_a_946_);
                    v___x_948_ = v_reuseFailAlloc_949_;
                    state = 5;
                    continue;
                }
            }
            4 => {
                v___x_941_ = lean_array_get_size(v_a_940_);
                v___x_942_ = lean_nat_dec_eq(v___x_941_, v___x_931_);
                if v___x_942_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_939_);
                    v___x_943_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_944_ = lean_nat_sub(v___x_941_, v___x_943_);
                    v___x_945_ = lean_nat_dec_le(v___x_931_, v___x_944_);
                    if v___x_945_ == 0 {
                        crate::leanh::lean_inc(v___x_944_);
                        v___y_925_ = v___x_944_;
                        v___y_926_ = v_a_940_;
                        v___y_927_ = v___x_941_;
                        v___y_928_ = v___x_944_;
                        state = 2;
                        continue;
                    } else {
                        v___y_925_ = v___x_944_;
                        v___y_926_ = v_a_940_;
                        v___y_927_ = v___x_941_;
                        v___y_928_ = v___x_931_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_a_940_);
                    return v___y_939_;
                }
            }
            5 => {
                v___y_939_ = v___x_948_;
                v_a_940_ = v_a_946_;
                state = 4;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_numApps___boxed(
    mut v_e_951_: *mut crate::leanh::LeanObject,
    mut v_threshold_952_: *mut crate::leanh::LeanObject,
    mut v_a_953_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_954_ = l_Lean_Expr_numApps(v_e_951_, v_threshold_952_);
    crate::leanh::lean_dec(v_threshold_952_);
    return v_res_954_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0(
    mut v_n_955_: *mut crate::leanh::LeanObject,
    mut v_as_956_: *mut crate::leanh::LeanObject,
    mut v_lo_957_: *mut crate::leanh::LeanObject,
    mut v_hi_958_: *mut crate::leanh::LeanObject,
    mut v_w_959_: *mut crate::leanh::LeanObject,
    mut v_hlo_960_: *mut crate::leanh::LeanObject,
    mut v_hhi_961_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_962_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___redArg(v_n_955_, v_as_956_, v_lo_957_, v_hi_958_);
    return v___x_962_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0___boxed(
    mut v_n_963_: *mut crate::leanh::LeanObject,
    mut v_as_964_: *mut crate::leanh::LeanObject,
    mut v_lo_965_: *mut crate::leanh::LeanObject,
    mut v_hi_966_: *mut crate::leanh::LeanObject,
    mut v_w_967_: *mut crate::leanh::LeanObject,
    mut v_hlo_968_: *mut crate::leanh::LeanObject,
    mut v_hhi_969_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_970_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0(v_n_963_, v_as_964_, v_lo_965_, v_hi_966_, v_w_967_, v_hlo_968_, v_hhi_969_);
    crate::leanh::lean_dec(v_hi_966_);
    crate::leanh::lean_dec(v_n_963_);
    return v_res_970_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0_spec__0(
    mut v_n_971_: *mut crate::leanh::LeanObject,
    mut v_lo_972_: *mut crate::leanh::LeanObject,
    mut v_hi_973_: *mut crate::leanh::LeanObject,
    mut v_hhi_974_: *mut crate::leanh::LeanObject,
    mut v_pivot_975_: *mut crate::leanh::LeanObject,
    mut v_as_976_: *mut crate::leanh::LeanObject,
    mut v_i_977_: *mut crate::leanh::LeanObject,
    mut v_k_978_: *mut crate::leanh::LeanObject,
    mut v_ilo_979_: *mut crate::leanh::LeanObject,
    mut v_ik_980_: *mut crate::leanh::LeanObject,
    mut v_w_981_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_982_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0_spec__0___redArg(v_hi_973_, v_pivot_975_, v_as_976_, v_i_977_, v_k_978_);
    return v___x_982_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0_spec__0___boxed(
    mut v_n_983_: *mut crate::leanh::LeanObject,
    mut v_lo_984_: *mut crate::leanh::LeanObject,
    mut v_hi_985_: *mut crate::leanh::LeanObject,
    mut v_hhi_986_: *mut crate::leanh::LeanObject,
    mut v_pivot_987_: *mut crate::leanh::LeanObject,
    mut v_as_988_: *mut crate::leanh::LeanObject,
    mut v_i_989_: *mut crate::leanh::LeanObject,
    mut v_k_990_: *mut crate::leanh::LeanObject,
    mut v_ilo_991_: *mut crate::leanh::LeanObject,
    mut v_ik_992_: *mut crate::leanh::LeanObject,
    mut v_w_993_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_994_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Expr_numApps_spec__0_spec__0(v_n_983_, v_lo_984_, v_hi_985_, v_hhi_986_, v_pivot_987_, v_as_988_, v_i_989_, v_k_990_, v_ilo_991_, v_ik_992_, v_w_993_);
    crate::leanh::lean_dec_ref(v_pivot_987_);
    crate::leanh::lean_dec(v_hi_985_);
    crate::leanh::lean_dec(v_lo_984_);
    crate::leanh::lean_dec(v_n_983_);
    return v_res_994_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Util_NumApps(builtin: u8) -> *mut crate::leanh::LeanObject {
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
    res = runtime_initialize_Lean_Util_PtrSet(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Util_NumApps(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Util_NumApps(builtin: u8) -> *mut crate::leanh::LeanObject {
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
    res = initialize_Lean_Util_PtrSet(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_NumApps(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Util_NumApps(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Util_NumApps(builtin);
}
