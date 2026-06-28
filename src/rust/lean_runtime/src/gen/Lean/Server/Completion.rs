// Lean compiler output
// Module: Lean.Server.Completion
// Imports: Lean.Server.Completion.CompletionCollectors Std.Data.HashMap
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Lean::Data::Lsp::LanguageFeatures::{
    l_Lean_Lsp_instBEqInsertReplaceEdit_beq, l_Lean_Lsp_instHashableInsertReplaceEdit_hash,
};
use crate::r#gen::Lean::Server::Completion::CompletionCollectors::{
    initialize_Lean_Server_Completion_CompletionCollectors, l_Lean_Server_Completion_dotCompletion,
    l_Lean_Server_Completion_dotIdCompletion, l_Lean_Server_Completion_endSectionCompletion,
    l_Lean_Server_Completion_errorNameCompletion, l_Lean_Server_Completion_fieldIdCompletion,
    l_Lean_Server_Completion_idCompletion, l_Lean_Server_Completion_optionCompletion,
    l_Lean_Server_Completion_tacticCompletion,
    runtime_initialize_Lean_Server_Completion_CompletionCollectors,
};
use crate::r#gen::Lean::Server::Completion::CompletionInfoSelection::l_Lean_Server_Completion_findPrioritizedCompletionPartitionsAt;
use crate::r#gen::Lean::Server::RequestCancellation::l_Lean_Server_CancellableM_checkCancelled;
use crate::r#gen::Std::Data::HashMap::{
    initialize_Std_Data_HashMap, runtime_initialize_Std_Data_HashMap,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul,
    lean_string_dec_eq, lean_string_hash, lean_uint64_mix_hash,
};
pub static l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__0(
    mut v_x_453_: *mut crate::leanh::LeanObject,
    mut v_x_454_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_453_) == 0 {
        if crate::leanh::lean_obj_tag(v_x_454_) == 0 {
            let mut v___x_455_: u8 = 0;
            v___x_455_ = 1;
            return v___x_455_;
        } else {
            let mut v___x_456_: u8 = 0;
            v___x_456_ = 0;
            return v___x_456_;
        }
    } else {
        if crate::leanh::lean_obj_tag(v_x_454_) == 0 {
            let mut v___x_457_: u8 = 0;
            v___x_457_ = 0;
            return v___x_457_;
        } else {
            let mut v_val_458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_460_: u8 = 0;
            v_val_458_ = crate::leanh::lean_ctor_get(v_x_453_, 0);
            v_val_459_ = crate::leanh::lean_ctor_get(v_x_454_, 0);
            v___x_460_ = l_Lean_Lsp_instBEqInsertReplaceEdit_beq(v_val_458_, v_val_459_);
            return v___x_460_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__0___boxed(
    mut v_x_461_: *mut crate::leanh::LeanObject,
    mut v_x_462_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_463_: u8 = 0;
    let mut v_r_464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_463_ = l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__0(v_x_461_, v_x_462_);
    crate::leanh::lean_dec(v_x_462_);
    crate::leanh::lean_dec(v_x_461_);
    v_r_464_ = crate::leanh::lean_box((v_res_463_) as usize);
    return v_r_464_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0___redArg(
    mut v_a_465_: *mut crate::leanh::LeanObject,
    mut v_x_466_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_467_: u8 = 0;
    let mut v_key_468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_471_: u8 = 0;
    let mut v_fst_473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_477_: u8 = 0;
    let mut v___x_478_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_466_) == 0 {
                    v___x_467_ = 0;
                    return v___x_467_;
                } else {
                    v_key_468_ = crate::leanh::lean_ctor_get(v_x_466_, 0);
                    v_tail_469_ = crate::leanh::lean_ctor_get(v_x_466_, 2);
                    v_fst_473_ = crate::leanh::lean_ctor_get(v_key_468_, 0);
                    v_snd_474_ = crate::leanh::lean_ctor_get(v_key_468_, 1);
                    v_fst_475_ = crate::leanh::lean_ctor_get(v_a_465_, 0);
                    v_snd_476_ = crate::leanh::lean_ctor_get(v_a_465_, 1);
                    v___x_477_ = lean_string_dec_eq(v_fst_473_, v_fst_475_);
                    if v___x_477_ == 0 {
                        v___y_471_ = v___x_477_;
                        state = 1;
                        continue;
                    } else {
                        v___x_478_ = l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__0(v_snd_474_, v_snd_476_);
                        v___y_471_ = v___x_478_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_471_ == 0 {
                    v_x_466_ = v_tail_469_;
                    state = 0;
                    continue;
                } else {
                    return v___y_471_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0___redArg___boxed(
    mut v_a_479_: *mut crate::leanh::LeanObject,
    mut v_x_480_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_481_: u8 = 0;
    let mut v_r_482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_481_ = l_Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0___redArg(v_a_479_, v_x_480_);
    crate::leanh::lean_dec(v_x_480_);
    crate::leanh::lean_dec_ref(v_a_479_);
    v_r_482_ = crate::leanh::lean_box((v_res_481_) as usize);
    return v_r_482_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2_spec__3___redArg(
    mut v_x_483_: *mut crate::leanh::LeanObject,
    mut v_x_484_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_490_: u8 = 0;
    let mut v_fst_491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_494_: u64 = 0;
    let mut v___y_496_: u64 = 0;
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
    let mut v___x_509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_515_: u64 = 0;
    let mut v_val_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_517_: u64 = 0;
    let mut v___x_518_: u64 = 0;
    let mut v___x_519_: u64 = 0;
    let mut v_isSharedCheck_520_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_484_) == 0 {
                    return v_x_483_;
                } else {
                    v_key_485_ = crate::leanh::lean_ctor_get(v_x_484_, 0);
                    v_value_486_ = crate::leanh::lean_ctor_get(v_x_484_, 1);
                    v_tail_487_ = crate::leanh::lean_ctor_get(v_x_484_, 2);
                    v_isSharedCheck_520_ = (!crate::leanh::lean_is_exclusive(v_x_484_)) as u8;
                    if v_isSharedCheck_520_ == 0 {
                        v___x_489_ = v_x_484_;
                        v_isShared_490_ = v_isSharedCheck_520_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_487_);
                        crate::leanh::lean_inc(v_value_486_);
                        crate::leanh::lean_inc(v_key_485_);
                        crate::leanh::lean_dec(v_x_484_);
                        v___x_489_ = crate::leanh::lean_box(0);
                        v_isShared_490_ = v_isSharedCheck_520_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_491_ = crate::leanh::lean_ctor_get(v_key_485_, 0);
                v_snd_492_ = crate::leanh::lean_ctor_get(v_key_485_, 1);
                v___x_493_ = lean_array_get_size(v_x_483_);
                v___x_494_ = lean_string_hash(v_fst_491_);
                if crate::leanh::lean_obj_tag(v_snd_492_) == 0 {
                    v___x_515_ = 11u64;
                    v___y_496_ = v___x_515_;
                    state = 2;
                    continue;
                } else {
                    v_val_516_ = crate::leanh::lean_ctor_get(v_snd_492_, 0);
                    v___x_517_ = l_Lean_Lsp_instHashableInsertReplaceEdit_hash(v_val_516_);
                    v___x_518_ = 13u64;
                    v___x_519_ = lean_uint64_mix_hash(v___x_517_, v___x_518_);
                    v___y_496_ = v___x_519_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_497_ = lean_uint64_mix_hash(v___x_494_, v___y_496_);
                v___x_498_ = 32u64;
                v___x_499_ = lean_uint64_shift_right(v___x_497_, v___x_498_);
                v_fold_500_ = lean_uint64_xor(v___x_497_, v___x_499_);
                v___x_501_ = 16u64;
                v___x_502_ = lean_uint64_shift_right(v_fold_500_, v___x_501_);
                v___x_503_ = lean_uint64_xor(v_fold_500_, v___x_502_);
                v___x_504_ = lean_uint64_to_usize(v___x_503_);
                v___x_505_ = lean_usize_of_nat(v___x_493_);
                v___x_506_ = 1usize;
                v___x_507_ = lean_usize_sub(v___x_505_, v___x_506_);
                v___x_508_ = lean_usize_land(v___x_504_, v___x_507_);
                v___x_509_ = lean_array_uget_borrowed(v_x_483_, v___x_508_);
                crate::leanh::lean_inc(v___x_509_);
                if v_isShared_490_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_489_, 2, v___x_509_);
                    v___x_511_ = v___x_489_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_514_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_514_, 0, v_key_485_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_514_, 1, v_value_486_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_514_, 2, v___x_509_);
                    v___x_511_ = v_reuseFailAlloc_514_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_512_ = lean_array_uset(v_x_483_, v___x_508_, v___x_511_);
                v_x_483_ = v___x_512_;
                v_x_484_ = v_tail_487_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2___redArg(
    mut v_i_521_: *mut crate::leanh::LeanObject,
    mut v_source_522_: *mut crate::leanh::LeanObject,
    mut v_target_523_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_525_: u8 = 0;
    let mut v_es_526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_524_ = lean_array_get_size(v_source_522_);
                v___x_525_ = lean_nat_dec_lt(v_i_521_, v___x_524_);
                if v___x_525_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_522_);
                    crate::leanh::lean_dec(v_i_521_);
                    return v_target_523_;
                } else {
                    v_es_526_ = lean_array_fget(v_source_522_, v_i_521_);
                    v___x_527_ = crate::leanh::lean_box(0);
                    v_source_528_ = lean_array_fset(v_source_522_, v_i_521_, v___x_527_);
                    v_target_529_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2_spec__3___redArg(v_target_523_, v_es_526_);
                    v___x_530_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_531_ = lean_nat_add(v_i_521_, v___x_530_);
                    crate::leanh::lean_dec(v_i_521_);
                    v_i_521_ = v___x_531_;
                    v_source_522_ = v_source_528_;
                    v_target_523_ = v_target_529_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg(
    mut v_data_533_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_534_ = lean_array_get_size(v_data_533_);
    v___x_535_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_536_ = lean_nat_mul(v___x_534_, v___x_535_);
    v___x_537_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_538_ = crate::leanh::lean_box(0);
    v___x_539_ = lean_mk_array(v_nbuckets_536_, v___x_538_);
    v___x_540_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2___redArg(v___x_537_, v_data_533_, v___x_539_);
    return v___x_540_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__2(
    mut v_as_541_: *mut crate::leanh::LeanObject,
    mut v_sz_542_: usize,
    mut v_i_543_: usize,
    mut v_b_544_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_547_: usize = 0;
    let mut v___x_548_: usize = 0;
    let mut v___x_550_: u8 = 0;
    let mut v_snd_551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_555_: u8 = 0;
    let mut v_size_556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_562_: u8 = 0;
    let mut v___x_563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_label_570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_textEdit_x3f_571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_574_: u64 = 0;
    let mut v___y_576_: u64 = 0;
    let mut v___x_577_: u64 = 0;
    let mut v___x_578_: u64 = 0;
    let mut v___x_579_: u64 = 0;
    let mut v_fold_580_: u64 = 0;
    let mut v___x_581_: u64 = 0;
    let mut v___x_582_: u64 = 0;
    let mut v___x_583_: u64 = 0;
    let mut v___x_584_: usize = 0;
    let mut v___x_585_: usize = 0;
    let mut v___x_586_: usize = 0;
    let mut v___x_587_: usize = 0;
    let mut v___x_588_: usize = 0;
    let mut v_bkt_589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_590_: u8 = 0;
    let mut v___x_592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_593_: u8 = 0;
    let mut v___x_594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_604_: u8 = 0;
    let mut v_val_605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_614_: u8 = 0;
    let mut v_unused_615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_618_: u64 = 0;
    let mut v_val_619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_620_: u64 = 0;
    let mut v___x_621_: u64 = 0;
    let mut v___x_622_: u64 = 0;
    let mut v_isSharedCheck_623_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_550_ = lean_usize_dec_lt(v_i_543_, v_sz_542_);
                if v___x_550_ == 0 {
                    return v_b_544_;
                } else {
                    v_snd_551_ = crate::leanh::lean_ctor_get(v_b_544_, 1);
                    v_fst_552_ = crate::leanh::lean_ctor_get(v_b_544_, 0);
                    v_isSharedCheck_623_ = (!crate::leanh::lean_is_exclusive(v_b_544_)) as u8;
                    if v_isSharedCheck_623_ == 0 {
                        v___x_554_ = v_b_544_;
                        v_isShared_555_ = v_isSharedCheck_623_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_551_);
                        crate::leanh::lean_inc(v_fst_552_);
                        crate::leanh::lean_dec(v_b_544_);
                        v___x_554_ = crate::leanh::lean_box(0);
                        v_isShared_555_ = v_isSharedCheck_623_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_547_ = 1usize;
                v___x_548_ = lean_usize_add(v_i_543_, v___x_547_);
                v_i_543_ = v___x_548_;
                v_b_544_ = v_a_546_;
                state = 0;
                continue;
            }
            2 => {
                v_size_556_ = crate::leanh::lean_ctor_get(v_snd_551_, 0);
                v_buckets_557_ = crate::leanh::lean_ctor_get(v_snd_551_, 1);
                v_a_558_ = lean_array_uget_borrowed(v_as_541_, v_i_543_);
                v_label_570_ = crate::leanh::lean_ctor_get(v_a_558_, 0);
                v_textEdit_x3f_571_ = crate::leanh::lean_ctor_get(v_a_558_, 4);
                crate::leanh::lean_inc(v_textEdit_x3f_571_);
                crate::leanh::lean_inc_ref(v_label_570_);
                v___x_572_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_572_, 0, v_label_570_);
                crate::leanh::lean_ctor_set(v___x_572_, 1, v_textEdit_x3f_571_);
                v___x_573_ = lean_array_get_size(v_buckets_557_);
                v___x_574_ = lean_string_hash(v_label_570_);
                if crate::leanh::lean_obj_tag(v_textEdit_x3f_571_) == 0 {
                    v___x_618_ = 11u64;
                    v___y_576_ = v___x_618_;
                    state = 6;
                    continue;
                } else {
                    v_val_619_ = crate::leanh::lean_ctor_get(v_textEdit_x3f_571_, 0);
                    v___x_620_ = l_Lean_Lsp_instHashableInsertReplaceEdit_hash(v_val_619_);
                    v___x_621_ = 13u64;
                    v___x_622_ = lean_uint64_mix_hash(v___x_620_, v___x_621_);
                    v___y_576_ = v___x_622_;
                    state = 6;
                    continue;
                }
            }
            3 => {
                v___x_562_ = (crate::leanh::lean_unbox(v_fst_560_) as u8);
                crate::leanh::lean_dec(v_fst_560_);
                if v___x_562_ == 0 {
                    crate::leanh::lean_inc(v_a_558_);
                    v___x_563_ = lean_array_push(v_fst_552_, v_a_558_);
                    if v_isShared_555_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_554_, 1, v_snd_561_);
                        crate::leanh::lean_ctor_set(v___x_554_, 0, v___x_563_);
                        v___x_565_ = v___x_554_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_566_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_566_, 0, v___x_563_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_566_, 1, v_snd_561_);
                        v___x_565_ = v_reuseFailAlloc_566_;
                        state = 4;
                        continue;
                    }
                } else {
                    if v_isShared_555_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_554_, 1, v_snd_561_);
                        v___x_568_ = v___x_554_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_569_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_569_, 0, v_fst_552_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_569_, 1, v_snd_561_);
                        v___x_568_ = v_reuseFailAlloc_569_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                v_a_546_ = v___x_565_;
                state = 1;
                continue;
            }
            5 => {
                v_a_546_ = v___x_568_;
                state = 1;
                continue;
            }
            6 => {
                v___x_577_ = lean_uint64_mix_hash(v___x_574_, v___y_576_);
                v___x_578_ = 32u64;
                v___x_579_ = lean_uint64_shift_right(v___x_577_, v___x_578_);
                v_fold_580_ = lean_uint64_xor(v___x_577_, v___x_579_);
                v___x_581_ = 16u64;
                v___x_582_ = lean_uint64_shift_right(v_fold_580_, v___x_581_);
                v___x_583_ = lean_uint64_xor(v_fold_580_, v___x_582_);
                v___x_584_ = lean_uint64_to_usize(v___x_583_);
                v___x_585_ = lean_usize_of_nat(v___x_573_);
                v___x_586_ = 1usize;
                v___x_587_ = lean_usize_sub(v___x_585_, v___x_586_);
                v___x_588_ = lean_usize_land(v___x_584_, v___x_587_);
                v_bkt_589_ = lean_array_uget_borrowed(v_buckets_557_, v___x_588_);
                v___x_590_ = l_Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0___redArg(v___x_572_, v_bkt_589_);
                if v___x_590_ == 0 {
                    crate::leanh::lean_inc_ref(v_buckets_557_);
                    crate::leanh::lean_inc(v_size_556_);
                    v_isSharedCheck_614_ = (!crate::leanh::lean_is_exclusive(v_snd_551_)) as u8;
                    if v_isSharedCheck_614_ == 0 {
                        v_unused_615_ = crate::leanh::lean_ctor_get(v_snd_551_, 1);
                        crate::leanh::lean_dec(v_unused_615_);
                        v_unused_616_ = crate::leanh::lean_ctor_get(v_snd_551_, 0);
                        crate::leanh::lean_dec(v_unused_616_);
                        v___x_592_ = v_snd_551_;
                        v_isShared_593_ = v_isSharedCheck_614_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_snd_551_);
                        v___x_592_ = crate::leanh::lean_box(0);
                        v_isShared_593_ = v_isSharedCheck_614_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_572_, 2);
                    v___x_617_ = crate::leanh::lean_box((v___x_590_) as usize);
                    v_fst_560_ = v___x_617_;
                    v_snd_561_ = v_snd_551_;
                    state = 3;
                    continue;
                }
            }
            7 => {
                v___x_594_ = crate::leanh::lean_box(0);
                v___x_595_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_596_ = lean_nat_add(v_size_556_, v___x_595_);
                crate::leanh::lean_dec(v_size_556_);
                crate::leanh::lean_inc(v_bkt_589_);
                v___x_597_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_597_, 0, v___x_572_);
                crate::leanh::lean_ctor_set(v___x_597_, 1, v___x_594_);
                crate::leanh::lean_ctor_set(v___x_597_, 2, v_bkt_589_);
                v_buckets_x27_598_ = lean_array_uset(v_buckets_557_, v___x_588_, v___x_597_);
                v___x_599_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_600_ = lean_nat_mul(v_size_x27_596_, v___x_599_);
                v___x_601_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_602_ = lean_nat_div(v___x_600_, v___x_601_);
                crate::leanh::lean_dec(v___x_600_);
                v___x_603_ = lean_array_get_size(v_buckets_x27_598_);
                v___x_604_ = lean_nat_dec_le(v___x_602_, v___x_603_);
                crate::leanh::lean_dec(v___x_602_);
                if v___x_604_ == 0 {
                    v_val_605_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg(v_buckets_x27_598_);
                    if v_isShared_593_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_592_, 1, v_val_605_);
                        crate::leanh::lean_ctor_set(v___x_592_, 0, v_size_x27_596_);
                        v___x_607_ = v___x_592_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_609_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_609_, 0, v_size_x27_596_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_609_, 1, v_val_605_);
                        v___x_607_ = v_reuseFailAlloc_609_;
                        state = 8;
                        continue;
                    }
                } else {
                    if v_isShared_593_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_592_, 1, v_buckets_x27_598_);
                        crate::leanh::lean_ctor_set(v___x_592_, 0, v_size_x27_596_);
                        v___x_611_ = v___x_592_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_613_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_613_, 0, v_size_x27_596_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_613_, 1, v_buckets_x27_598_);
                        v___x_611_ = v_reuseFailAlloc_613_;
                        state = 9;
                        continue;
                    }
                }
            }
            8 => {
                v___x_608_ = crate::leanh::lean_box((v___x_590_) as usize);
                v_fst_560_ = v___x_608_;
                v_snd_561_ = v___x_607_;
                state = 3;
                continue;
            }
            9 => {
                v___x_612_ = crate::leanh::lean_box((v___x_590_) as usize);
                v_fst_560_ = v___x_612_;
                v_snd_561_ = v___x_611_;
                state = 3;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__2___boxed(
    mut v_as_624_: *mut crate::leanh::LeanObject,
    mut v_sz_625_: *mut crate::leanh::LeanObject,
    mut v_i_626_: *mut crate::leanh::LeanObject,
    mut v_b_627_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_628_: usize = 0;
    let mut v_i_boxed_629_: usize = 0;
    let mut v_res_630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_628_ = crate::leanh::lean_unbox_usize(v_sz_625_);
    crate::leanh::lean_dec(v_sz_625_);
    v_i_boxed_629_ = crate::leanh::lean_unbox_usize(v_i_626_);
    crate::leanh::lean_dec(v_i_626_);
    v_res_630_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__2(v_as_624_, v_sz_boxed_628_, v_i_boxed_629_, v_b_627_);
    crate::leanh::lean_dec_ref(v_as_624_);
    return v_res_630_;
}
pub unsafe fn _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_633_ = crate::leanh::lean_box(0);
    v___x_634_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_635_ = lean_mk_array(v___x_634_, v___x_633_);
    return v___x_635_;
}
pub unsafe fn _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_index_638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_636_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__1_once), _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__1);
    v___x_637_ = crate::leanh::lean_unsigned_to_nat(0);
    v_index_638_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v_index_638_, 0, v___x_637_);
    crate::leanh::lean_ctor_set(v_index_638_, 1, v___x_636_);
    return v_index_638_;
}
pub unsafe fn _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v_index_639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_index_639_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__2_once), _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__2);
    v_r_640_ = l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__0;
    v___x_641_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_641_, 0, v_r_640_);
    crate::leanh::lean_ctor_set(v___x_641_, 1, v_index_639_);
    return v___x_641_;
}
pub unsafe fn l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems(
    mut v_items_642_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_644_: usize = 0;
    let mut v___x_645_: usize = 0;
    let mut v___x_646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_643_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__3_once), _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__3);
    v_sz_644_ = lean_array_size(v_items_642_);
    v___x_645_ = 0usize;
    v___x_646_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__2(v_items_642_, v_sz_644_, v___x_645_, v___x_643_);
    v_fst_647_ = crate::leanh::lean_ctor_get(v___x_646_, 0);
    crate::leanh::lean_inc(v_fst_647_);
    crate::leanh::lean_dec_ref(v___x_646_);
    return v_fst_647_;
}
pub unsafe fn l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___boxed(
    mut v_items_648_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_649_ =
        l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems(
            v_items_648_,
        );
    crate::leanh::lean_dec_ref(v_items_648_);
    return v_res_649_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0(
    mut v_00_u03b2_650_: *mut crate::leanh::LeanObject,
    mut v_a_651_: *mut crate::leanh::LeanObject,
    mut v_x_652_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_653_: u8 = 0;
    v___x_653_ = l_Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0___redArg(v_a_651_, v_x_652_);
    return v___x_653_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0___boxed(
    mut v_00_u03b2_654_: *mut crate::leanh::LeanObject,
    mut v_a_655_: *mut crate::leanh::LeanObject,
    mut v_x_656_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_657_: u8 = 0;
    let mut v_r_658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_657_ = l_Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0(v_00_u03b2_654_, v_a_655_, v_x_656_);
    crate::leanh::lean_dec(v_x_656_);
    crate::leanh::lean_dec_ref(v_a_655_);
    v_r_658_ = crate::leanh::lean_box((v_res_657_) as usize);
    return v_r_658_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1(
    mut v_00_u03b2_659_: *mut crate::leanh::LeanObject,
    mut v_data_660_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_661_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg(v_data_660_);
    return v___x_661_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2(
    mut v_00_u03b2_662_: *mut crate::leanh::LeanObject,
    mut v_i_663_: *mut crate::leanh::LeanObject,
    mut v_source_664_: *mut crate::leanh::LeanObject,
    mut v_target_665_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_666_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2___redArg(v_i_663_, v_source_664_, v_target_665_);
    return v___x_666_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2_spec__3(
    mut v_00_u03b2_667_: *mut crate::leanh::LeanObject,
    mut v_x_668_: *mut crate::leanh::LeanObject,
    mut v_x_669_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_670_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2_spec__3___redArg(v_x_668_, v_x_669_);
    return v___x_670_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__0(
    mut v_uri_671_: *mut crate::leanh::LeanObject,
    mut v_pos_672_: *mut crate::leanh::LeanObject,
    mut v_caps_673_: *mut crate::leanh::LeanObject,
    mut v_as_674_: *mut crate::leanh::LeanObject,
    mut v_sz_675_: usize,
    mut v_i_676_: usize,
    mut v_b_677_: *mut crate::leanh::LeanObject,
    mut v___y_678_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_completions_685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_687_: usize = 0;
    let mut v___x_688_: usize = 0;
    let mut v___x_690_: u8 = 0;
    let mut v___x_691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_info_699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hoverInfo_700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctx_701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_danglingDot_704_: u8 = 0;
    let mut v_lctx_705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctx_710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_termInfo_711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctx_716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expectedType_x3f_719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctx_724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_structName_727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctx_732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_739_: u8 = 0;
    let mut v___x_741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_743_: u8 = 0;
    let mut v_ctx_744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_partialId_745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_751_: u8 = 0;
    let mut v___x_753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_755_: u8 = 0;
    let mut v_id_x3f_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_danglingDot_757_: u8 = 0;
    let mut v_scopeNames_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_764_: u8 = 0;
    let mut v___x_766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_768_: u8 = 0;
    let mut v_ctx_769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_775_: u8 = 0;
    let mut v___x_777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_779_: u8 = 0;
    let mut v_allCompletions_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_784_: u8 = 0;
    let mut v___x_786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_788_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_690_ = lean_usize_dec_lt(v_i_676_, v_sz_675_);
                if v___x_690_ == 0 {
                    crate::leanh::lean_dec_ref(v_caps_673_);
                    crate::leanh::lean_dec_ref(v_pos_672_);
                    crate::leanh::lean_dec_ref(v_uri_671_);
                    v___x_691_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_691_, 0, v_b_677_);
                    v___x_692_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_692_, 0, v___x_691_);
                    return v___x_692_;
                } else {
                    v_a_693_ = lean_array_uget_borrowed(v_as_674_, v_i_676_);
                    v_fst_694_ = crate::leanh::lean_ctor_get(v_a_693_, 0);
                    v_snd_695_ = crate::leanh::lean_ctor_get(v_a_693_, 1);
                    v___x_696_ = l_Lean_Server_CancellableM_checkCancelled(v___y_678_);
                    if crate::leanh::lean_obj_tag(v___x_696_) == 0 {
                        v_a_697_ = crate::leanh::lean_ctor_get(v___x_696_, 0);
                        crate::leanh::lean_inc(v_a_697_);
                        crate::leanh::lean_dec_ref_known(v___x_696_, 1);
                        if crate::leanh::lean_obj_tag(v_a_697_) == 0 {
                            crate::leanh::lean_dec_ref(v_b_677_);
                            crate::leanh::lean_dec_ref(v_caps_673_);
                            crate::leanh::lean_dec_ref(v_pos_672_);
                            crate::leanh::lean_dec_ref(v_uri_671_);
                            v_a_698_ = crate::leanh::lean_ctor_get(v_a_697_, 0);
                            crate::leanh::lean_inc(v_a_698_);
                            crate::leanh::lean_dec_ref_known(v_a_697_, 1);
                            v_a_681_ = v_a_698_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref_known(v_a_697_, 1);
                            v_info_699_ = crate::leanh::lean_ctor_get(v_fst_694_, 2);
                            match crate::leanh::lean_obj_tag(v_info_699_) {
                                1 => {
                                    v_hoverInfo_700_ = crate::leanh::lean_ctor_get(v_fst_694_, 0);
                                    v_ctx_701_ = crate::leanh::lean_ctor_get(v_fst_694_, 1);
                                    v_stx_702_ = crate::leanh::lean_ctor_get(v_info_699_, 0);
                                    v_id_703_ = crate::leanh::lean_ctor_get(v_info_699_, 1);
                                    v_danglingDot_704_ = crate::leanh::lean_ctor_get_uint8(
                                        v_info_699_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4)
                                            as u32,
                                    );
                                    v_lctx_705_ = crate::leanh::lean_ctor_get(v_info_699_, 2);
                                    crate::leanh::lean_inc(v_hoverInfo_700_);
                                    crate::leanh::lean_inc(v_id_703_);
                                    crate::leanh::lean_inc(v_stx_702_);
                                    crate::leanh::lean_inc_ref(v_lctx_705_);
                                    crate::leanh::lean_inc_ref(v_ctx_701_);
                                    crate::leanh::lean_inc(v_snd_695_);
                                    crate::leanh::lean_inc_ref(v_pos_672_);
                                    crate::leanh::lean_inc_ref(v_uri_671_);
                                    v___x_706_ = l_Lean_Server_Completion_idCompletion(
                                        v_uri_671_,
                                        v_pos_672_,
                                        v_snd_695_,
                                        v_ctx_701_,
                                        v_lctx_705_,
                                        v_stx_702_,
                                        v_id_703_,
                                        v_hoverInfo_700_,
                                        v_danglingDot_704_,
                                        v___y_678_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_706_) == 0 {
                                        v_a_707_ = crate::leanh::lean_ctor_get(v___x_706_, 0);
                                        crate::leanh::lean_inc(v_a_707_);
                                        crate::leanh::lean_dec_ref_known(v___x_706_, 1);
                                        if crate::leanh::lean_obj_tag(v_a_707_) == 0 {
                                            crate::leanh::lean_dec_ref(v_b_677_);
                                            crate::leanh::lean_dec_ref(v_caps_673_);
                                            crate::leanh::lean_dec_ref(v_pos_672_);
                                            crate::leanh::lean_dec_ref(v_uri_671_);
                                            v_a_708_ = crate::leanh::lean_ctor_get(v_a_707_, 0);
                                            crate::leanh::lean_inc(v_a_708_);
                                            crate::leanh::lean_dec_ref_known(v_a_707_, 1);
                                            v_a_681_ = v_a_708_;
                                            state = 1;
                                            continue;
                                        } else {
                                            v_a_709_ = crate::leanh::lean_ctor_get(v_a_707_, 0);
                                            crate::leanh::lean_inc(v_a_709_);
                                            crate::leanh::lean_dec_ref_known(v_a_707_, 1);
                                            v_completions_685_ = v_a_709_;
                                            state = 2;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref(v_b_677_);
                                        crate::leanh::lean_dec_ref(v_caps_673_);
                                        crate::leanh::lean_dec_ref(v_pos_672_);
                                        crate::leanh::lean_dec_ref(v_uri_671_);
                                        return v___x_706_;
                                    }
                                }
                                0 => {
                                    v_ctx_710_ = crate::leanh::lean_ctor_get(v_fst_694_, 1);
                                    v_termInfo_711_ = crate::leanh::lean_ctor_get(v_info_699_, 0);
                                    crate::leanh::lean_inc_ref(v_termInfo_711_);
                                    crate::leanh::lean_inc_ref(v_ctx_710_);
                                    crate::leanh::lean_inc(v_snd_695_);
                                    crate::leanh::lean_inc_ref(v_pos_672_);
                                    crate::leanh::lean_inc_ref(v_uri_671_);
                                    v___x_712_ = l_Lean_Server_Completion_dotCompletion(
                                        v_uri_671_,
                                        v_pos_672_,
                                        v_snd_695_,
                                        v_ctx_710_,
                                        v_termInfo_711_,
                                        v___y_678_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_712_) == 0 {
                                        v_a_713_ = crate::leanh::lean_ctor_get(v___x_712_, 0);
                                        crate::leanh::lean_inc(v_a_713_);
                                        crate::leanh::lean_dec_ref_known(v___x_712_, 1);
                                        if crate::leanh::lean_obj_tag(v_a_713_) == 0 {
                                            crate::leanh::lean_dec_ref(v_b_677_);
                                            crate::leanh::lean_dec_ref(v_caps_673_);
                                            crate::leanh::lean_dec_ref(v_pos_672_);
                                            crate::leanh::lean_dec_ref(v_uri_671_);
                                            v_a_714_ = crate::leanh::lean_ctor_get(v_a_713_, 0);
                                            crate::leanh::lean_inc(v_a_714_);
                                            crate::leanh::lean_dec_ref_known(v_a_713_, 1);
                                            v_a_681_ = v_a_714_;
                                            state = 1;
                                            continue;
                                        } else {
                                            v_a_715_ = crate::leanh::lean_ctor_get(v_a_713_, 0);
                                            crate::leanh::lean_inc(v_a_715_);
                                            crate::leanh::lean_dec_ref_known(v_a_713_, 1);
                                            v_completions_685_ = v_a_715_;
                                            state = 2;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref(v_b_677_);
                                        crate::leanh::lean_dec_ref(v_caps_673_);
                                        crate::leanh::lean_dec_ref(v_pos_672_);
                                        crate::leanh::lean_dec_ref(v_uri_671_);
                                        return v___x_712_;
                                    }
                                }
                                2 => {
                                    v_ctx_716_ = crate::leanh::lean_ctor_get(v_fst_694_, 1);
                                    v_id_717_ = crate::leanh::lean_ctor_get(v_info_699_, 1);
                                    v_lctx_718_ = crate::leanh::lean_ctor_get(v_info_699_, 2);
                                    v_expectedType_x3f_719_ =
                                        crate::leanh::lean_ctor_get(v_info_699_, 3);
                                    crate::leanh::lean_inc(v_expectedType_x3f_719_);
                                    crate::leanh::lean_inc(v_id_717_);
                                    crate::leanh::lean_inc_ref(v_lctx_718_);
                                    crate::leanh::lean_inc_ref(v_ctx_716_);
                                    crate::leanh::lean_inc(v_snd_695_);
                                    crate::leanh::lean_inc_ref(v_pos_672_);
                                    crate::leanh::lean_inc_ref(v_uri_671_);
                                    v___x_720_ = l_Lean_Server_Completion_dotIdCompletion(
                                        v_uri_671_,
                                        v_pos_672_,
                                        v_snd_695_,
                                        v_ctx_716_,
                                        v_lctx_718_,
                                        v_id_717_,
                                        v_expectedType_x3f_719_,
                                        v___y_678_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_720_) == 0 {
                                        v_a_721_ = crate::leanh::lean_ctor_get(v___x_720_, 0);
                                        crate::leanh::lean_inc(v_a_721_);
                                        crate::leanh::lean_dec_ref_known(v___x_720_, 1);
                                        if crate::leanh::lean_obj_tag(v_a_721_) == 0 {
                                            crate::leanh::lean_dec_ref(v_b_677_);
                                            crate::leanh::lean_dec_ref(v_caps_673_);
                                            crate::leanh::lean_dec_ref(v_pos_672_);
                                            crate::leanh::lean_dec_ref(v_uri_671_);
                                            v_a_722_ = crate::leanh::lean_ctor_get(v_a_721_, 0);
                                            crate::leanh::lean_inc(v_a_722_);
                                            crate::leanh::lean_dec_ref_known(v_a_721_, 1);
                                            v_a_681_ = v_a_722_;
                                            state = 1;
                                            continue;
                                        } else {
                                            v_a_723_ = crate::leanh::lean_ctor_get(v_a_721_, 0);
                                            crate::leanh::lean_inc(v_a_723_);
                                            crate::leanh::lean_dec_ref_known(v_a_721_, 1);
                                            v_completions_685_ = v_a_723_;
                                            state = 2;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref(v_b_677_);
                                        crate::leanh::lean_dec_ref(v_caps_673_);
                                        crate::leanh::lean_dec_ref(v_pos_672_);
                                        crate::leanh::lean_dec_ref(v_uri_671_);
                                        return v___x_720_;
                                    }
                                }
                                3 => {
                                    v_ctx_724_ = crate::leanh::lean_ctor_get(v_fst_694_, 1);
                                    v_id_725_ = crate::leanh::lean_ctor_get(v_info_699_, 1);
                                    v_lctx_726_ = crate::leanh::lean_ctor_get(v_info_699_, 2);
                                    v_structName_727_ = crate::leanh::lean_ctor_get(v_info_699_, 3);
                                    crate::leanh::lean_inc(v_structName_727_);
                                    crate::leanh::lean_inc(v_id_725_);
                                    crate::leanh::lean_inc_ref(v_lctx_726_);
                                    crate::leanh::lean_inc_ref(v_ctx_724_);
                                    crate::leanh::lean_inc(v_snd_695_);
                                    crate::leanh::lean_inc_ref(v_pos_672_);
                                    crate::leanh::lean_inc_ref(v_uri_671_);
                                    v___x_728_ = l_Lean_Server_Completion_fieldIdCompletion(
                                        v_uri_671_,
                                        v_pos_672_,
                                        v_snd_695_,
                                        v_ctx_724_,
                                        v_lctx_726_,
                                        v_id_725_,
                                        v_structName_727_,
                                        v___y_678_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_728_) == 0 {
                                        v_a_729_ = crate::leanh::lean_ctor_get(v___x_728_, 0);
                                        crate::leanh::lean_inc(v_a_729_);
                                        crate::leanh::lean_dec_ref_known(v___x_728_, 1);
                                        if crate::leanh::lean_obj_tag(v_a_729_) == 0 {
                                            crate::leanh::lean_dec_ref(v_b_677_);
                                            crate::leanh::lean_dec_ref(v_caps_673_);
                                            crate::leanh::lean_dec_ref(v_pos_672_);
                                            crate::leanh::lean_dec_ref(v_uri_671_);
                                            v_a_730_ = crate::leanh::lean_ctor_get(v_a_729_, 0);
                                            crate::leanh::lean_inc(v_a_730_);
                                            crate::leanh::lean_dec_ref_known(v_a_729_, 1);
                                            v_a_681_ = v_a_730_;
                                            state = 1;
                                            continue;
                                        } else {
                                            v_a_731_ = crate::leanh::lean_ctor_get(v_a_729_, 0);
                                            crate::leanh::lean_inc(v_a_731_);
                                            crate::leanh::lean_dec_ref_known(v_a_729_, 1);
                                            v_completions_685_ = v_a_731_;
                                            state = 2;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref(v_b_677_);
                                        crate::leanh::lean_dec_ref(v_caps_673_);
                                        crate::leanh::lean_dec_ref(v_pos_672_);
                                        crate::leanh::lean_dec_ref(v_uri_671_);
                                        return v___x_728_;
                                    }
                                }
                                5 => {
                                    v_ctx_732_ = crate::leanh::lean_ctor_get(v_fst_694_, 1);
                                    v_stx_733_ = crate::leanh::lean_ctor_get(v_info_699_, 0);
                                    crate::leanh::lean_inc_ref(v_caps_673_);
                                    crate::leanh::lean_inc(v_stx_733_);
                                    crate::leanh::lean_inc_ref(v_ctx_732_);
                                    crate::leanh::lean_inc(v_snd_695_);
                                    crate::leanh::lean_inc_ref(v_pos_672_);
                                    crate::leanh::lean_inc_ref(v_uri_671_);
                                    v___x_734_ = l_Lean_Server_Completion_optionCompletion(
                                        v_uri_671_,
                                        v_pos_672_,
                                        v_snd_695_,
                                        v_ctx_732_,
                                        v_stx_733_,
                                        v_caps_673_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_734_) == 0 {
                                        v_a_735_ = crate::leanh::lean_ctor_get(v___x_734_, 0);
                                        crate::leanh::lean_inc(v_a_735_);
                                        crate::leanh::lean_dec_ref_known(v___x_734_, 1);
                                        v_completions_685_ = v_a_735_;
                                        state = 2;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec_ref(v_b_677_);
                                        crate::leanh::lean_dec_ref(v_caps_673_);
                                        crate::leanh::lean_dec_ref(v_pos_672_);
                                        crate::leanh::lean_dec_ref(v_uri_671_);
                                        v_a_736_ = crate::leanh::lean_ctor_get(v___x_734_, 0);
                                        v_isSharedCheck_743_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_734_)) as u8;
                                        if v_isSharedCheck_743_ == 0 {
                                            v___x_738_ = v___x_734_;
                                            v_isShared_739_ = v_isSharedCheck_743_;
                                            state = 3;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_736_);
                                            crate::leanh::lean_dec(v___x_734_);
                                            v___x_738_ = crate::leanh::lean_box(0);
                                            v_isShared_739_ = v_isSharedCheck_743_;
                                            state = 3;
                                            continue;
                                        }
                                    }
                                }
                                6 => {
                                    v_ctx_744_ = crate::leanh::lean_ctor_get(v_fst_694_, 1);
                                    v_partialId_745_ = crate::leanh::lean_ctor_get(v_info_699_, 1);
                                    crate::leanh::lean_inc_ref(v_caps_673_);
                                    crate::leanh::lean_inc(v_partialId_745_);
                                    crate::leanh::lean_inc_ref(v_ctx_744_);
                                    crate::leanh::lean_inc(v_snd_695_);
                                    crate::leanh::lean_inc_ref(v_pos_672_);
                                    crate::leanh::lean_inc_ref(v_uri_671_);
                                    v___x_746_ = l_Lean_Server_Completion_errorNameCompletion(
                                        v_uri_671_,
                                        v_pos_672_,
                                        v_snd_695_,
                                        v_ctx_744_,
                                        v_partialId_745_,
                                        v_caps_673_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_746_) == 0 {
                                        v_a_747_ = crate::leanh::lean_ctor_get(v___x_746_, 0);
                                        crate::leanh::lean_inc(v_a_747_);
                                        crate::leanh::lean_dec_ref_known(v___x_746_, 1);
                                        v_completions_685_ = v_a_747_;
                                        state = 2;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec_ref(v_b_677_);
                                        crate::leanh::lean_dec_ref(v_caps_673_);
                                        crate::leanh::lean_dec_ref(v_pos_672_);
                                        crate::leanh::lean_dec_ref(v_uri_671_);
                                        v_a_748_ = crate::leanh::lean_ctor_get(v___x_746_, 0);
                                        v_isSharedCheck_755_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_746_)) as u8;
                                        if v_isSharedCheck_755_ == 0 {
                                            v___x_750_ = v___x_746_;
                                            v_isShared_751_ = v_isSharedCheck_755_;
                                            state = 5;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_748_);
                                            crate::leanh::lean_dec(v___x_746_);
                                            v___x_750_ = crate::leanh::lean_box(0);
                                            v_isShared_751_ = v_isSharedCheck_755_;
                                            state = 5;
                                            continue;
                                        }
                                    }
                                }
                                7 => {
                                    v_id_x3f_756_ = crate::leanh::lean_ctor_get(v_info_699_, 1);
                                    v_danglingDot_757_ = crate::leanh::lean_ctor_get_uint8(
                                        v_info_699_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3)
                                            as u32,
                                    );
                                    v_scopeNames_758_ = crate::leanh::lean_ctor_get(v_info_699_, 2);
                                    crate::leanh::lean_inc(v_scopeNames_758_);
                                    crate::leanh::lean_inc(v_id_x3f_756_);
                                    crate::leanh::lean_inc(v_snd_695_);
                                    crate::leanh::lean_inc_ref(v_pos_672_);
                                    crate::leanh::lean_inc_ref(v_uri_671_);
                                    v___x_759_ = l_Lean_Server_Completion_endSectionCompletion(
                                        v_uri_671_,
                                        v_pos_672_,
                                        v_snd_695_,
                                        v_id_x3f_756_,
                                        v_danglingDot_757_,
                                        v_scopeNames_758_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_759_) == 0 {
                                        v_a_760_ = crate::leanh::lean_ctor_get(v___x_759_, 0);
                                        crate::leanh::lean_inc(v_a_760_);
                                        crate::leanh::lean_dec_ref_known(v___x_759_, 1);
                                        v_completions_685_ = v_a_760_;
                                        state = 2;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec_ref(v_b_677_);
                                        crate::leanh::lean_dec_ref(v_caps_673_);
                                        crate::leanh::lean_dec_ref(v_pos_672_);
                                        crate::leanh::lean_dec_ref(v_uri_671_);
                                        v_a_761_ = crate::leanh::lean_ctor_get(v___x_759_, 0);
                                        v_isSharedCheck_768_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_759_)) as u8;
                                        if v_isSharedCheck_768_ == 0 {
                                            v___x_763_ = v___x_759_;
                                            v_isShared_764_ = v_isSharedCheck_768_;
                                            state = 7;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_761_);
                                            crate::leanh::lean_dec(v___x_759_);
                                            v___x_763_ = crate::leanh::lean_box(0);
                                            v_isShared_764_ = v_isSharedCheck_768_;
                                            state = 7;
                                            continue;
                                        }
                                    }
                                }
                                8 => {
                                    v_ctx_769_ = crate::leanh::lean_ctor_get(v_fst_694_, 1);
                                    crate::leanh::lean_inc_ref(v_ctx_769_);
                                    crate::leanh::lean_inc(v_snd_695_);
                                    crate::leanh::lean_inc_ref(v_pos_672_);
                                    crate::leanh::lean_inc_ref(v_uri_671_);
                                    v___x_770_ = l_Lean_Server_Completion_tacticCompletion(
                                        v_uri_671_, v_pos_672_, v_snd_695_, v_ctx_769_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_770_) == 0 {
                                        v_a_771_ = crate::leanh::lean_ctor_get(v___x_770_, 0);
                                        crate::leanh::lean_inc(v_a_771_);
                                        crate::leanh::lean_dec_ref_known(v___x_770_, 1);
                                        v_completions_685_ = v_a_771_;
                                        state = 2;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec_ref(v_b_677_);
                                        crate::leanh::lean_dec_ref(v_caps_673_);
                                        crate::leanh::lean_dec_ref(v_pos_672_);
                                        crate::leanh::lean_dec_ref(v_uri_671_);
                                        v_a_772_ = crate::leanh::lean_ctor_get(v___x_770_, 0);
                                        v_isSharedCheck_779_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_770_)) as u8;
                                        if v_isSharedCheck_779_ == 0 {
                                            v___x_774_ = v___x_770_;
                                            v_isShared_775_ = v_isSharedCheck_779_;
                                            state = 9;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_772_);
                                            crate::leanh::lean_dec(v___x_770_);
                                            v___x_774_ = crate::leanh::lean_box(0);
                                            v_isShared_775_ = v_isSharedCheck_779_;
                                            state = 9;
                                            continue;
                                        }
                                    }
                                }
                                _ => {
                                    v_allCompletions_780_ = l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__0;
                                    v_completions_685_ = v_allCompletions_780_;
                                    state = 2;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_b_677_);
                        crate::leanh::lean_dec_ref(v_caps_673_);
                        crate::leanh::lean_dec_ref(v_pos_672_);
                        crate::leanh::lean_dec_ref(v_uri_671_);
                        v_a_781_ = crate::leanh::lean_ctor_get(v___x_696_, 0);
                        v_isSharedCheck_788_ = (!crate::leanh::lean_is_exclusive(v___x_696_)) as u8;
                        if v_isSharedCheck_788_ == 0 {
                            v___x_783_ = v___x_696_;
                            v_isShared_784_ = v_isSharedCheck_788_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_781_);
                            crate::leanh::lean_dec(v___x_696_);
                            v___x_783_ = crate::leanh::lean_box(0);
                            v_isShared_784_ = v_isSharedCheck_788_;
                            state = 11;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_682_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_682_, 0, v_a_681_);
                v___x_683_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_683_, 0, v___x_682_);
                return v___x_683_;
            }
            2 => {
                v___x_686_ = l_Array_append___redArg(v_b_677_, v_completions_685_);
                crate::leanh::lean_dec_ref(v_completions_685_);
                v___x_687_ = 1usize;
                v___x_688_ = lean_usize_add(v_i_676_, v___x_687_);
                v_i_676_ = v___x_688_;
                v_b_677_ = v___x_686_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_739_ == 0 {
                    v___x_741_ = v___x_738_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_742_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_742_, 0, v_a_736_);
                    v___x_741_ = v_reuseFailAlloc_742_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_741_;
            }
            5 => {
                if v_isShared_751_ == 0 {
                    v___x_753_ = v___x_750_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_754_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_754_, 0, v_a_748_);
                    v___x_753_ = v_reuseFailAlloc_754_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_753_;
            }
            7 => {
                if v_isShared_764_ == 0 {
                    v___x_766_ = v___x_763_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_767_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_767_, 0, v_a_761_);
                    v___x_766_ = v_reuseFailAlloc_767_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_766_;
            }
            9 => {
                if v_isShared_775_ == 0 {
                    v___x_777_ = v___x_774_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_778_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_778_, 0, v_a_772_);
                    v___x_777_ = v_reuseFailAlloc_778_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_777_;
            }
            11 => {
                if v_isShared_784_ == 0 {
                    v___x_786_ = v___x_783_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_787_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_787_, 0, v_a_781_);
                    v___x_786_ = v_reuseFailAlloc_787_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_786_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__0___boxed(
    mut v_uri_789_: *mut crate::leanh::LeanObject,
    mut v_pos_790_: *mut crate::leanh::LeanObject,
    mut v_caps_791_: *mut crate::leanh::LeanObject,
    mut v_as_792_: *mut crate::leanh::LeanObject,
    mut v_sz_793_: *mut crate::leanh::LeanObject,
    mut v_i_794_: *mut crate::leanh::LeanObject,
    mut v_b_795_: *mut crate::leanh::LeanObject,
    mut v___y_796_: *mut crate::leanh::LeanObject,
    mut v___y_797_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_798_: usize = 0;
    let mut v_i_boxed_799_: usize = 0;
    let mut v_res_800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_798_ = crate::leanh::lean_unbox_usize(v_sz_793_);
    crate::leanh::lean_dec(v_sz_793_);
    v_i_boxed_799_ = crate::leanh::lean_unbox_usize(v_i_794_);
    crate::leanh::lean_dec(v_i_794_);
    v_res_800_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__0(v_uri_789_, v_pos_790_, v_caps_791_, v_as_792_, v_sz_boxed_798_, v_i_boxed_799_, v_b_795_, v___y_796_);
    crate::leanh::lean_dec_ref(v___y_796_);
    crate::leanh::lean_dec_ref(v_as_792_);
    return v_res_800_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__1(
    mut v_uri_801_: *mut crate::leanh::LeanObject,
    mut v_pos_802_: *mut crate::leanh::LeanObject,
    mut v_caps_803_: *mut crate::leanh::LeanObject,
    mut v_as_804_: *mut crate::leanh::LeanObject,
    mut v_sz_805_: usize,
    mut v_i_806_: usize,
    mut v_b_807_: *mut crate::leanh::LeanObject,
    mut v___y_808_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_810_: u8 = 0;
    let mut v___x_811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_814_: usize = 0;
    let mut v___x_815_: usize = 0;
    let mut v___x_816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_821_: u8 = 0;
    let mut v___x_822_: usize = 0;
    let mut v___x_823_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_810_ = lean_usize_dec_lt(v_i_806_, v_sz_805_);
                if v___x_810_ == 0 {
                    crate::leanh::lean_dec_ref(v_caps_803_);
                    crate::leanh::lean_dec_ref(v_pos_802_);
                    crate::leanh::lean_dec_ref(v_uri_801_);
                    v___x_811_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_811_, 0, v_b_807_);
                    v___x_812_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_812_, 0, v___x_811_);
                    return v___x_812_;
                } else {
                    v_a_813_ = lean_array_uget_borrowed(v_as_804_, v_i_806_);
                    v_sz_814_ = lean_array_size(v_a_813_);
                    v___x_815_ = 0usize;
                    crate::leanh::lean_inc_ref(v_caps_803_);
                    crate::leanh::lean_inc_ref(v_pos_802_);
                    crate::leanh::lean_inc_ref(v_uri_801_);
                    v___x_816_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__0(v_uri_801_, v_pos_802_, v_caps_803_, v_a_813_, v_sz_814_, v___x_815_, v_b_807_, v___y_808_);
                    if crate::leanh::lean_obj_tag(v___x_816_) == 0 {
                        v_a_817_ = crate::leanh::lean_ctor_get(v___x_816_, 0);
                        crate::leanh::lean_inc(v_a_817_);
                        if crate::leanh::lean_obj_tag(v_a_817_) == 0 {
                            crate::leanh::lean_dec_ref_known(v_a_817_, 1);
                            crate::leanh::lean_dec_ref(v_caps_803_);
                            crate::leanh::lean_dec_ref(v_pos_802_);
                            crate::leanh::lean_dec_ref(v_uri_801_);
                            return v___x_816_;
                        } else {
                            v_a_818_ = crate::leanh::lean_ctor_get(v_a_817_, 0);
                            crate::leanh::lean_inc(v_a_818_);
                            crate::leanh::lean_dec_ref_known(v_a_817_, 1);
                            v___x_819_ = lean_array_get_size(v_a_818_);
                            v___x_820_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___x_821_ = lean_nat_dec_eq(v___x_819_, v___x_820_);
                            if v___x_821_ == 0 {
                                crate::leanh::lean_dec(v_a_818_);
                                crate::leanh::lean_dec_ref(v_caps_803_);
                                crate::leanh::lean_dec_ref(v_pos_802_);
                                crate::leanh::lean_dec_ref(v_uri_801_);
                                return v___x_816_;
                            } else {
                                crate::leanh::lean_dec_ref_known(v___x_816_, 1);
                                v___x_822_ = 1usize;
                                v___x_823_ = lean_usize_add(v_i_806_, v___x_822_);
                                v_i_806_ = v___x_823_;
                                v_b_807_ = v_a_818_;
                                state = 0;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_caps_803_);
                        crate::leanh::lean_dec_ref(v_pos_802_);
                        crate::leanh::lean_dec_ref(v_uri_801_);
                        return v___x_816_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__1___boxed(
    mut v_uri_825_: *mut crate::leanh::LeanObject,
    mut v_pos_826_: *mut crate::leanh::LeanObject,
    mut v_caps_827_: *mut crate::leanh::LeanObject,
    mut v_as_828_: *mut crate::leanh::LeanObject,
    mut v_sz_829_: *mut crate::leanh::LeanObject,
    mut v_i_830_: *mut crate::leanh::LeanObject,
    mut v_b_831_: *mut crate::leanh::LeanObject,
    mut v___y_832_: *mut crate::leanh::LeanObject,
    mut v___y_833_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_834_: usize = 0;
    let mut v_i_boxed_835_: usize = 0;
    let mut v_res_836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_834_ = crate::leanh::lean_unbox_usize(v_sz_829_);
    crate::leanh::lean_dec(v_sz_829_);
    v_i_boxed_835_ = crate::leanh::lean_unbox_usize(v_i_830_);
    crate::leanh::lean_dec(v_i_830_);
    v_res_836_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__1(v_uri_825_, v_pos_826_, v_caps_827_, v_as_828_, v_sz_boxed_834_, v_i_boxed_835_, v_b_831_, v___y_832_);
    crate::leanh::lean_dec_ref(v___y_832_);
    crate::leanh::lean_dec_ref(v_as_828_);
    return v_res_836_;
}
pub unsafe fn l_Lean_Server_Completion_find_x3f(
    mut v_uri_837_: *mut crate::leanh::LeanObject,
    mut v_pos_838_: *mut crate::leanh::LeanObject,
    mut v_fileMap_839_: *mut crate::leanh::LeanObject,
    mut v_hoverPos_840_: *mut crate::leanh::LeanObject,
    mut v_cmdStx_841_: *mut crate::leanh::LeanObject,
    mut v_infoTree_842_: *mut crate::leanh::LeanObject,
    mut v_caps_843_: *mut crate::leanh::LeanObject,
    mut v_a_844_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_allCompletions_849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_850_: usize = 0;
    let mut v___x_851_: usize = 0;
    let mut v___x_852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_856_: u8 = 0;
    let mut v_a_857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_860_: u8 = 0;
    let mut v___x_862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_867_: u8 = 0;
    let mut v_a_868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_871_: u8 = 0;
    let mut v___x_872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_874_: u8 = 0;
    let mut v___x_875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_882_: u8 = 0;
    let mut v___x_883_: u8 = 0;
    let mut v___x_884_: u8 = 0;
    let mut v_isSharedCheck_885_: u8 = 0;
    let mut v_isSharedCheck_886_: u8 = 0;
    let mut v_a_887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_890_: u8 = 0;
    let mut v___x_892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_894_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_846_ = l_Lean_Server_Completion_findPrioritizedCompletionPartitionsAt(
                    v_fileMap_839_,
                    v_hoverPos_840_,
                    v_cmdStx_841_,
                    v_infoTree_842_,
                );
                v_fst_847_ = crate::leanh::lean_ctor_get(v___x_846_, 0);
                crate::leanh::lean_inc(v_fst_847_);
                v_snd_848_ = crate::leanh::lean_ctor_get(v___x_846_, 1);
                crate::leanh::lean_inc(v_snd_848_);
                crate::leanh::lean_dec_ref(v___x_846_);
                v_allCompletions_849_ = l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__0;
                v_sz_850_ = lean_array_size(v_fst_847_);
                v___x_851_ = 0usize;
                v___x_852_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__1(v_uri_837_, v_pos_838_, v_caps_843_, v_fst_847_, v_sz_850_, v___x_851_, v_allCompletions_849_, v_a_844_);
                crate::leanh::lean_dec(v_fst_847_);
                if crate::leanh::lean_obj_tag(v___x_852_) == 0 {
                    v_a_853_ = crate::leanh::lean_ctor_get(v___x_852_, 0);
                    v_isSharedCheck_886_ = (!crate::leanh::lean_is_exclusive(v___x_852_)) as u8;
                    if v_isSharedCheck_886_ == 0 {
                        v___x_855_ = v___x_852_;
                        v_isShared_856_ = v_isSharedCheck_886_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_853_);
                        crate::leanh::lean_dec(v___x_852_);
                        v___x_855_ = crate::leanh::lean_box(0);
                        v_isShared_856_ = v_isSharedCheck_886_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_snd_848_);
                    v_a_887_ = crate::leanh::lean_ctor_get(v___x_852_, 0);
                    v_isSharedCheck_894_ = (!crate::leanh::lean_is_exclusive(v___x_852_)) as u8;
                    if v_isSharedCheck_894_ == 0 {
                        v___x_889_ = v___x_852_;
                        v_isShared_890_ = v_isSharedCheck_894_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_887_);
                        crate::leanh::lean_dec(v___x_852_);
                        v___x_889_ = crate::leanh::lean_box(0);
                        v_isShared_890_ = v_isSharedCheck_894_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_853_) == 0 {
                    crate::leanh::lean_dec(v_snd_848_);
                    v_a_857_ = crate::leanh::lean_ctor_get(v_a_853_, 0);
                    v_isSharedCheck_867_ = (!crate::leanh::lean_is_exclusive(v_a_853_)) as u8;
                    if v_isSharedCheck_867_ == 0 {
                        v___x_859_ = v_a_853_;
                        v_isShared_860_ = v_isSharedCheck_867_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_857_);
                        crate::leanh::lean_dec(v_a_853_);
                        v___x_859_ = crate::leanh::lean_box(0);
                        v_isShared_860_ = v_isSharedCheck_867_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_868_ = crate::leanh::lean_ctor_get(v_a_853_, 0);
                    v_isSharedCheck_885_ = (!crate::leanh::lean_is_exclusive(v_a_853_)) as u8;
                    if v_isSharedCheck_885_ == 0 {
                        v___x_870_ = v_a_853_;
                        v_isShared_871_ = v_isSharedCheck_885_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_868_);
                        crate::leanh::lean_dec(v_a_853_);
                        v___x_870_ = crate::leanh::lean_box(0);
                        v_isShared_871_ = v_isSharedCheck_885_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_860_ == 0 {
                    v___x_862_ = v___x_859_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_866_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_866_, 0, v_a_857_);
                    v___x_862_ = v_reuseFailAlloc_866_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_856_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_855_, 0, v___x_862_);
                    v___x_864_ = v___x_855_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_865_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_865_, 0, v___x_862_);
                    v___x_864_ = v_reuseFailAlloc_865_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_864_;
            }
            5 => {
                v___x_872_ = l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems(v_a_868_);
                crate::leanh::lean_dec(v_a_868_);
                v___x_882_ = (crate::leanh::lean_unbox(v_snd_848_) as u8);
                crate::leanh::lean_dec(v_snd_848_);
                if v___x_882_ == 0 {
                    v___x_883_ = 1;
                    v___y_874_ = v___x_883_;
                    state = 6;
                    continue;
                } else {
                    v___x_884_ = 0;
                    v___y_874_ = v___x_884_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_875_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_875_, 0, v___x_872_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_875_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___y_874_,
                );
                if v_isShared_871_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_870_, 0, v___x_875_);
                    v___x_877_ = v___x_870_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_881_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_881_, 0, v___x_875_);
                    v___x_877_ = v_reuseFailAlloc_881_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_856_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_855_, 0, v___x_877_);
                    v___x_879_ = v___x_855_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_880_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_880_, 0, v___x_877_);
                    v___x_879_ = v_reuseFailAlloc_880_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_879_;
            }
            9 => {
                if v_isShared_890_ == 0 {
                    v___x_892_ = v___x_889_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_893_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_893_, 0, v_a_887_);
                    v___x_892_ = v_reuseFailAlloc_893_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_892_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_Completion_find_x3f___boxed(
    mut v_uri_895_: *mut crate::leanh::LeanObject,
    mut v_pos_896_: *mut crate::leanh::LeanObject,
    mut v_fileMap_897_: *mut crate::leanh::LeanObject,
    mut v_hoverPos_898_: *mut crate::leanh::LeanObject,
    mut v_cmdStx_899_: *mut crate::leanh::LeanObject,
    mut v_infoTree_900_: *mut crate::leanh::LeanObject,
    mut v_caps_901_: *mut crate::leanh::LeanObject,
    mut v_a_902_: *mut crate::leanh::LeanObject,
    mut v_a_903_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_904_ = l_Lean_Server_Completion_find_x3f(
        v_uri_895_,
        v_pos_896_,
        v_fileMap_897_,
        v_hoverPos_898_,
        v_cmdStx_899_,
        v_infoTree_900_,
        v_caps_901_,
        v_a_902_,
    );
    crate::leanh::lean_dec_ref(v_a_902_);
    return v_res_904_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Server_Completion(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Server_Completion_CompletionCollectors(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_HashMap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Server_Completion(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Server_Completion(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Server_Completion_CompletionCollectors(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Data_HashMap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Server_Completion(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Server_Completion(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Server_Completion(builtin);
}
