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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_set, lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc,
    lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once,
    lean_obj_tag, lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__3: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__0(
    mut v_x_453_: *mut LeanObject,
    mut v_x_454_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_453_) == 0 {
        if lean_obj_tag(v_x_454_) == 0 {
            let mut v___x_455_: u8 = 0;
            v___x_455_ = 1;
            return v___x_455_;
        } else {
            let mut v___x_456_: u8 = 0;
            v___x_456_ = 0;
            return v___x_456_;
        }
    } else {
        if lean_obj_tag(v_x_454_) == 0 {
            let mut v___x_457_: u8 = 0;
            v___x_457_ = 0;
            return v___x_457_;
        } else {
            let mut v_val_458_: *mut LeanObject = core::ptr::null_mut();
            let mut v_val_459_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_460_: u8 = 0;
            v_val_458_ = lean_ctor_get(v_x_453_, 0);
            v_val_459_ = lean_ctor_get(v_x_454_, 0);
            v___x_460_ = l_Lean_Lsp_instBEqInsertReplaceEdit_beq(v_val_458_, v_val_459_);
            return v___x_460_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__0___boxed(
    mut v_x_461_: *mut LeanObject,
    mut v_x_462_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_463_: u8 = 0;
    let mut v_r_464_: *mut LeanObject = core::ptr::null_mut();
    v_res_463_ = l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__0(v_x_461_, v_x_462_);
    lean_dec(v_x_462_);
    lean_dec(v_x_461_);
    v_r_464_ = lean_box((v_res_463_) as usize);
    return v_r_464_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0___redArg(
    mut v_a_465_: *mut LeanObject,
    mut v_x_466_: *mut LeanObject,
) -> u8 {
    let mut v___x_467_: u8 = 0;
    let mut v_key_468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_471_: u8 = 0;
    let mut v_fst_473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_477_: u8 = 0;
    let mut v___x_478_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_466_) == 0 {
                    v___x_467_ = 0;
                    return v___x_467_;
                } else {
                    v_key_468_ = lean_ctor_get(v_x_466_, 0);
                    v_tail_469_ = lean_ctor_get(v_x_466_, 2);
                    v_fst_473_ = lean_ctor_get(v_key_468_, 0);
                    v_snd_474_ = lean_ctor_get(v_key_468_, 1);
                    v_fst_475_ = lean_ctor_get(v_a_465_, 0);
                    v_snd_476_ = lean_ctor_get(v_a_465_, 1);
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
    mut v_a_479_: *mut LeanObject,
    mut v_x_480_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_481_: u8 = 0;
    let mut v_r_482_: *mut LeanObject = core::ptr::null_mut();
    v_res_481_ = l_Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0___redArg(v_a_479_, v_x_480_);
    lean_dec(v_x_480_);
    lean_dec_ref(v_a_479_);
    v_r_482_ = lean_box((v_res_481_) as usize);
    return v_r_482_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2_spec__3___redArg(
    mut v_x_483_: *mut LeanObject,
    mut v_x_484_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_490_: u8 = 0;
    let mut v_fst_491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_493_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_515_: u64 = 0;
    let mut v_val_516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_517_: u64 = 0;
    let mut v___x_518_: u64 = 0;
    let mut v___x_519_: u64 = 0;
    let mut v_isSharedCheck_520_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_484_) == 0 {
                    return v_x_483_;
                } else {
                    v_key_485_ = lean_ctor_get(v_x_484_, 0);
                    v_value_486_ = lean_ctor_get(v_x_484_, 1);
                    v_tail_487_ = lean_ctor_get(v_x_484_, 2);
                    v_isSharedCheck_520_ = (!lean_is_exclusive(v_x_484_)) as u8;
                    if v_isSharedCheck_520_ == 0 {
                        v___x_489_ = v_x_484_;
                        v_isShared_490_ = v_isSharedCheck_520_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_487_);
                        lean_inc(v_value_486_);
                        lean_inc(v_key_485_);
                        lean_dec(v_x_484_);
                        v___x_489_ = lean_box(0);
                        v_isShared_490_ = v_isSharedCheck_520_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_491_ = lean_ctor_get(v_key_485_, 0);
                v_snd_492_ = lean_ctor_get(v_key_485_, 1);
                v___x_493_ = lean_array_get_size(v_x_483_);
                v___x_494_ = lean_string_hash(v_fst_491_);
                if lean_obj_tag(v_snd_492_) == 0 {
                    v___x_515_ = 11u64;
                    v___y_496_ = v___x_515_;
                    state = 2;
                    continue;
                } else {
                    v_val_516_ = lean_ctor_get(v_snd_492_, 0);
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
                lean_inc(v___x_509_);
                if v_isShared_490_ == 0 {
                    lean_ctor_set(v___x_489_, 2, v___x_509_);
                    v___x_511_ = v___x_489_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_514_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_514_, 0, v_key_485_);
                    lean_ctor_set(v_reuseFailAlloc_514_, 1, v_value_486_);
                    lean_ctor_set(v_reuseFailAlloc_514_, 2, v___x_509_);
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
    mut v_i_521_: *mut LeanObject,
    mut v_source_522_: *mut LeanObject,
    mut v_target_523_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_525_: u8 = 0;
    let mut v_es_526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_531_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_524_ = lean_array_get_size(v_source_522_);
                v___x_525_ = lean_nat_dec_lt(v_i_521_, v___x_524_);
                if v___x_525_ == 0 {
                    lean_dec_ref(v_source_522_);
                    lean_dec(v_i_521_);
                    return v_target_523_;
                } else {
                    v_es_526_ = lean_array_fget(v_source_522_, v_i_521_);
                    v___x_527_ = lean_box(0);
                    v_source_528_ = lean_array_fset(v_source_522_, v_i_521_, v___x_527_);
                    v_target_529_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2_spec__3___redArg(v_target_523_, v_es_526_);
                    v___x_530_ = lean_unsigned_to_nat(1);
                    v___x_531_ = lean_nat_add(v_i_521_, v___x_530_);
                    lean_dec(v_i_521_);
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
    mut v_data_533_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_540_: *mut LeanObject = core::ptr::null_mut();
    v___x_534_ = lean_array_get_size(v_data_533_);
    v___x_535_ = lean_unsigned_to_nat(2);
    v_nbuckets_536_ = lean_nat_mul(v___x_534_, v___x_535_);
    v___x_537_ = lean_unsigned_to_nat(0);
    v___x_538_ = lean_box(0);
    v___x_539_ = lean_mk_array(v_nbuckets_536_, v___x_538_);
    v___x_540_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2___redArg(v___x_537_, v_data_533_, v___x_539_);
    return v___x_540_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__2(
    mut v_as_541_: *mut LeanObject,
    mut v_sz_542_: usize,
    mut v_i_543_: usize,
    mut v_b_544_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_547_: usize = 0;
    let mut v___x_548_: usize = 0;
    let mut v___x_550_: u8 = 0;
    let mut v_snd_551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_555_: u8 = 0;
    let mut v_size_556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_562_: u8 = 0;
    let mut v___x_563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_label_570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_textEdit_x3f_571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_573_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_590_: u8 = 0;
    let mut v___x_592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_593_: u8 = 0;
    let mut v___x_594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_604_: u8 = 0;
    let mut v_val_605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_614_: u8 = 0;
    let mut v_unused_615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_618_: u64 = 0;
    let mut v_val_619_: *mut LeanObject = core::ptr::null_mut();
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
                    v_snd_551_ = lean_ctor_get(v_b_544_, 1);
                    v_fst_552_ = lean_ctor_get(v_b_544_, 0);
                    v_isSharedCheck_623_ = (!lean_is_exclusive(v_b_544_)) as u8;
                    if v_isSharedCheck_623_ == 0 {
                        v___x_554_ = v_b_544_;
                        v_isShared_555_ = v_isSharedCheck_623_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_snd_551_);
                        lean_inc(v_fst_552_);
                        lean_dec(v_b_544_);
                        v___x_554_ = lean_box(0);
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
                v_size_556_ = lean_ctor_get(v_snd_551_, 0);
                v_buckets_557_ = lean_ctor_get(v_snd_551_, 1);
                v_a_558_ = lean_array_uget_borrowed(v_as_541_, v_i_543_);
                v_label_570_ = lean_ctor_get(v_a_558_, 0);
                v_textEdit_x3f_571_ = lean_ctor_get(v_a_558_, 4);
                lean_inc(v_textEdit_x3f_571_);
                lean_inc_ref(v_label_570_);
                v___x_572_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_572_, 0, v_label_570_);
                lean_ctor_set(v___x_572_, 1, v_textEdit_x3f_571_);
                v___x_573_ = lean_array_get_size(v_buckets_557_);
                v___x_574_ = lean_string_hash(v_label_570_);
                if lean_obj_tag(v_textEdit_x3f_571_) == 0 {
                    v___x_618_ = 11u64;
                    v___y_576_ = v___x_618_;
                    state = 6;
                    continue;
                } else {
                    v_val_619_ = lean_ctor_get(v_textEdit_x3f_571_, 0);
                    v___x_620_ = l_Lean_Lsp_instHashableInsertReplaceEdit_hash(v_val_619_);
                    v___x_621_ = 13u64;
                    v___x_622_ = lean_uint64_mix_hash(v___x_620_, v___x_621_);
                    v___y_576_ = v___x_622_;
                    state = 6;
                    continue;
                }
            }
            3 => {
                v___x_562_ = (lean_unbox(v_fst_560_) as u8);
                lean_dec(v_fst_560_);
                if v___x_562_ == 0 {
                    lean_inc(v_a_558_);
                    v___x_563_ = lean_array_push(v_fst_552_, v_a_558_);
                    if v_isShared_555_ == 0 {
                        lean_ctor_set(v___x_554_, 1, v_snd_561_);
                        lean_ctor_set(v___x_554_, 0, v___x_563_);
                        v___x_565_ = v___x_554_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_566_, 0, v___x_563_);
                        lean_ctor_set(v_reuseFailAlloc_566_, 1, v_snd_561_);
                        v___x_565_ = v_reuseFailAlloc_566_;
                        state = 4;
                        continue;
                    }
                } else {
                    if v_isShared_555_ == 0 {
                        lean_ctor_set(v___x_554_, 1, v_snd_561_);
                        v___x_568_ = v___x_554_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_569_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_569_, 0, v_fst_552_);
                        lean_ctor_set(v_reuseFailAlloc_569_, 1, v_snd_561_);
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
                    lean_inc_ref(v_buckets_557_);
                    lean_inc(v_size_556_);
                    v_isSharedCheck_614_ = (!lean_is_exclusive(v_snd_551_)) as u8;
                    if v_isSharedCheck_614_ == 0 {
                        v_unused_615_ = lean_ctor_get(v_snd_551_, 1);
                        lean_dec(v_unused_615_);
                        v_unused_616_ = lean_ctor_get(v_snd_551_, 0);
                        lean_dec(v_unused_616_);
                        v___x_592_ = v_snd_551_;
                        v_isShared_593_ = v_isSharedCheck_614_;
                        state = 7;
                        continue;
                    } else {
                        lean_dec(v_snd_551_);
                        v___x_592_ = lean_box(0);
                        v_isShared_593_ = v_isSharedCheck_614_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v___x_572_, 2);
                    v___x_617_ = lean_box((v___x_590_) as usize);
                    v_fst_560_ = v___x_617_;
                    v_snd_561_ = v_snd_551_;
                    state = 3;
                    continue;
                }
            }
            7 => {
                v___x_594_ = lean_box(0);
                v___x_595_ = lean_unsigned_to_nat(1);
                v_size_x27_596_ = lean_nat_add(v_size_556_, v___x_595_);
                lean_dec(v_size_556_);
                lean_inc(v_bkt_589_);
                v___x_597_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_597_, 0, v___x_572_);
                lean_ctor_set(v___x_597_, 1, v___x_594_);
                lean_ctor_set(v___x_597_, 2, v_bkt_589_);
                v_buckets_x27_598_ = lean_array_uset(v_buckets_557_, v___x_588_, v___x_597_);
                v___x_599_ = lean_unsigned_to_nat(4);
                v___x_600_ = lean_nat_mul(v_size_x27_596_, v___x_599_);
                v___x_601_ = lean_unsigned_to_nat(3);
                v___x_602_ = lean_nat_div(v___x_600_, v___x_601_);
                lean_dec(v___x_600_);
                v___x_603_ = lean_array_get_size(v_buckets_x27_598_);
                v___x_604_ = lean_nat_dec_le(v___x_602_, v___x_603_);
                lean_dec(v___x_602_);
                if v___x_604_ == 0 {
                    v_val_605_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg(v_buckets_x27_598_);
                    if v_isShared_593_ == 0 {
                        lean_ctor_set(v___x_592_, 1, v_val_605_);
                        lean_ctor_set(v___x_592_, 0, v_size_x27_596_);
                        v___x_607_ = v___x_592_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_609_, 0, v_size_x27_596_);
                        lean_ctor_set(v_reuseFailAlloc_609_, 1, v_val_605_);
                        v___x_607_ = v_reuseFailAlloc_609_;
                        state = 8;
                        continue;
                    }
                } else {
                    if v_isShared_593_ == 0 {
                        lean_ctor_set(v___x_592_, 1, v_buckets_x27_598_);
                        lean_ctor_set(v___x_592_, 0, v_size_x27_596_);
                        v___x_611_ = v___x_592_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_613_, 0, v_size_x27_596_);
                        lean_ctor_set(v_reuseFailAlloc_613_, 1, v_buckets_x27_598_);
                        v___x_611_ = v_reuseFailAlloc_613_;
                        state = 9;
                        continue;
                    }
                }
            }
            8 => {
                v___x_608_ = lean_box((v___x_590_) as usize);
                v_fst_560_ = v___x_608_;
                v_snd_561_ = v___x_607_;
                state = 3;
                continue;
            }
            9 => {
                v___x_612_ = lean_box((v___x_590_) as usize);
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
    mut v_as_624_: *mut LeanObject,
    mut v_sz_625_: *mut LeanObject,
    mut v_i_626_: *mut LeanObject,
    mut v_b_627_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_628_: usize = 0;
    let mut v_i_boxed_629_: usize = 0;
    let mut v_res_630_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_628_ = lean_unbox_usize(v_sz_625_);
    lean_dec(v_sz_625_);
    v_i_boxed_629_ = lean_unbox_usize(v_i_626_);
    lean_dec(v_i_626_);
    v_res_630_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__2(v_as_624_, v_sz_boxed_628_, v_i_boxed_629_, v_b_627_);
    lean_dec_ref(v_as_624_);
    return v_res_630_;
}
pub unsafe fn _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__1()
-> *mut LeanObject {
    let mut v___x_633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_635_: *mut LeanObject = core::ptr::null_mut();
    v___x_633_ = lean_box(0);
    v___x_634_ = lean_unsigned_to_nat(16);
    v___x_635_ = lean_mk_array(v___x_634_, v___x_633_);
    return v___x_635_;
}
pub unsafe fn _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__2()
-> *mut LeanObject {
    let mut v___x_636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_index_638_: *mut LeanObject = core::ptr::null_mut();
    v___x_636_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__1_once), _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__1);
    v___x_637_ = lean_unsigned_to_nat(0);
    v_index_638_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v_index_638_, 0, v___x_637_);
    lean_ctor_set(v_index_638_, 1, v___x_636_);
    return v_index_638_;
}
pub unsafe fn _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__3()
-> *mut LeanObject {
    let mut v_index_639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_641_: *mut LeanObject = core::ptr::null_mut();
    v_index_639_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__2_once), _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__2);
    v_r_640_ = l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__0;
    v___x_641_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_641_, 0, v_r_640_);
    lean_ctor_set(v___x_641_, 1, v_index_639_);
    return v___x_641_;
}
pub unsafe fn l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems(
    mut v_items_642_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_644_: usize = 0;
    let mut v___x_645_: usize = 0;
    let mut v___x_646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_647_: *mut LeanObject = core::ptr::null_mut();
    v___x_643_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__3_once), _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__3);
    v_sz_644_ = lean_array_size(v_items_642_);
    v___x_645_ = 0usize;
    v___x_646_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__2(v_items_642_, v_sz_644_, v___x_645_, v___x_643_);
    v_fst_647_ = lean_ctor_get(v___x_646_, 0);
    lean_inc(v_fst_647_);
    lean_dec_ref(v___x_646_);
    return v_fst_647_;
}
pub unsafe fn l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___boxed(
    mut v_items_648_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_649_: *mut LeanObject = core::ptr::null_mut();
    v_res_649_ =
        l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems(
            v_items_648_,
        );
    lean_dec_ref(v_items_648_);
    return v_res_649_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0(
    mut v_00_u03b2_650_: *mut LeanObject,
    mut v_a_651_: *mut LeanObject,
    mut v_x_652_: *mut LeanObject,
) -> u8 {
    let mut v___x_653_: u8 = 0;
    v___x_653_ = l_Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0___redArg(v_a_651_, v_x_652_);
    return v___x_653_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0___boxed(
    mut v_00_u03b2_654_: *mut LeanObject,
    mut v_a_655_: *mut LeanObject,
    mut v_x_656_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_657_: u8 = 0;
    let mut v_r_658_: *mut LeanObject = core::ptr::null_mut();
    v_res_657_ = l_Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0(v_00_u03b2_654_, v_a_655_, v_x_656_);
    lean_dec(v_x_656_);
    lean_dec_ref(v_a_655_);
    v_r_658_ = lean_box((v_res_657_) as usize);
    return v_r_658_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1(
    mut v_00_u03b2_659_: *mut LeanObject,
    mut v_data_660_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_661_: *mut LeanObject = core::ptr::null_mut();
    v___x_661_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg(v_data_660_);
    return v___x_661_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2(
    mut v_00_u03b2_662_: *mut LeanObject,
    mut v_i_663_: *mut LeanObject,
    mut v_source_664_: *mut LeanObject,
    mut v_target_665_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_666_: *mut LeanObject = core::ptr::null_mut();
    v___x_666_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2___redArg(v_i_663_, v_source_664_, v_target_665_);
    return v___x_666_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2_spec__3(
    mut v_00_u03b2_667_: *mut LeanObject,
    mut v_x_668_: *mut LeanObject,
    mut v_x_669_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_670_: *mut LeanObject = core::ptr::null_mut();
    v___x_670_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2_spec__3___redArg(v_x_668_, v_x_669_);
    return v___x_670_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__0(
    mut v_uri_671_: *mut LeanObject,
    mut v_pos_672_: *mut LeanObject,
    mut v_caps_673_: *mut LeanObject,
    mut v_as_674_: *mut LeanObject,
    mut v_sz_675_: usize,
    mut v_i_676_: usize,
    mut v_b_677_: *mut LeanObject,
    mut v___y_678_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_completions_685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_687_: usize = 0;
    let mut v___x_688_: usize = 0;
    let mut v___x_690_: u8 = 0;
    let mut v___x_691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_info_699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hoverInfo_700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctx_701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stx_702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_danglingDot_704_: u8 = 0;
    let mut v_lctx_705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctx_710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_termInfo_711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctx_716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expectedType_x3f_719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctx_724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_structName_727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctx_732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stx_733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_739_: u8 = 0;
    let mut v___x_741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_743_: u8 = 0;
    let mut v_ctx_744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_partialId_745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_751_: u8 = 0;
    let mut v___x_753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_755_: u8 = 0;
    let mut v_id_x3f_756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_danglingDot_757_: u8 = 0;
    let mut v_scopeNames_758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_764_: u8 = 0;
    let mut v___x_766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_768_: u8 = 0;
    let mut v_ctx_769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_775_: u8 = 0;
    let mut v___x_777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_779_: u8 = 0;
    let mut v_allCompletions_780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_784_: u8 = 0;
    let mut v___x_786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_788_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_690_ = lean_usize_dec_lt(v_i_676_, v_sz_675_);
                if v___x_690_ == 0 {
                    lean_dec_ref(v_caps_673_);
                    lean_dec_ref(v_pos_672_);
                    lean_dec_ref(v_uri_671_);
                    v___x_691_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_691_, 0, v_b_677_);
                    v___x_692_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_692_, 0, v___x_691_);
                    return v___x_692_;
                } else {
                    v_a_693_ = lean_array_uget_borrowed(v_as_674_, v_i_676_);
                    v_fst_694_ = lean_ctor_get(v_a_693_, 0);
                    v_snd_695_ = lean_ctor_get(v_a_693_, 1);
                    v___x_696_ = l_Lean_Server_CancellableM_checkCancelled(v___y_678_);
                    if lean_obj_tag(v___x_696_) == 0 {
                        v_a_697_ = lean_ctor_get(v___x_696_, 0);
                        lean_inc(v_a_697_);
                        lean_dec_ref_known(v___x_696_, 1);
                        if lean_obj_tag(v_a_697_) == 0 {
                            lean_dec_ref(v_b_677_);
                            lean_dec_ref(v_caps_673_);
                            lean_dec_ref(v_pos_672_);
                            lean_dec_ref(v_uri_671_);
                            v_a_698_ = lean_ctor_get(v_a_697_, 0);
                            lean_inc(v_a_698_);
                            lean_dec_ref_known(v_a_697_, 1);
                            v_a_681_ = v_a_698_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec_ref_known(v_a_697_, 1);
                            v_info_699_ = lean_ctor_get(v_fst_694_, 2);
                            match lean_obj_tag(v_info_699_) {
                                1 => {
                                    v_hoverInfo_700_ = lean_ctor_get(v_fst_694_, 0);
                                    v_ctx_701_ = lean_ctor_get(v_fst_694_, 1);
                                    v_stx_702_ = lean_ctor_get(v_info_699_, 0);
                                    v_id_703_ = lean_ctor_get(v_info_699_, 1);
                                    v_danglingDot_704_ = lean_ctor_get_uint8(
                                        v_info_699_,
                                        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                                    );
                                    v_lctx_705_ = lean_ctor_get(v_info_699_, 2);
                                    lean_inc(v_hoverInfo_700_);
                                    lean_inc(v_id_703_);
                                    lean_inc(v_stx_702_);
                                    lean_inc_ref(v_lctx_705_);
                                    lean_inc_ref(v_ctx_701_);
                                    lean_inc(v_snd_695_);
                                    lean_inc_ref(v_pos_672_);
                                    lean_inc_ref(v_uri_671_);
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
                                    if lean_obj_tag(v___x_706_) == 0 {
                                        v_a_707_ = lean_ctor_get(v___x_706_, 0);
                                        lean_inc(v_a_707_);
                                        lean_dec_ref_known(v___x_706_, 1);
                                        if lean_obj_tag(v_a_707_) == 0 {
                                            lean_dec_ref(v_b_677_);
                                            lean_dec_ref(v_caps_673_);
                                            lean_dec_ref(v_pos_672_);
                                            lean_dec_ref(v_uri_671_);
                                            v_a_708_ = lean_ctor_get(v_a_707_, 0);
                                            lean_inc(v_a_708_);
                                            lean_dec_ref_known(v_a_707_, 1);
                                            v_a_681_ = v_a_708_;
                                            state = 1;
                                            continue;
                                        } else {
                                            v_a_709_ = lean_ctor_get(v_a_707_, 0);
                                            lean_inc(v_a_709_);
                                            lean_dec_ref_known(v_a_707_, 1);
                                            v_completions_685_ = v_a_709_;
                                            state = 2;
                                            continue;
                                        }
                                    } else {
                                        lean_dec_ref(v_b_677_);
                                        lean_dec_ref(v_caps_673_);
                                        lean_dec_ref(v_pos_672_);
                                        lean_dec_ref(v_uri_671_);
                                        return v___x_706_;
                                    }
                                }
                                0 => {
                                    v_ctx_710_ = lean_ctor_get(v_fst_694_, 1);
                                    v_termInfo_711_ = lean_ctor_get(v_info_699_, 0);
                                    lean_inc_ref(v_termInfo_711_);
                                    lean_inc_ref(v_ctx_710_);
                                    lean_inc(v_snd_695_);
                                    lean_inc_ref(v_pos_672_);
                                    lean_inc_ref(v_uri_671_);
                                    v___x_712_ = l_Lean_Server_Completion_dotCompletion(
                                        v_uri_671_,
                                        v_pos_672_,
                                        v_snd_695_,
                                        v_ctx_710_,
                                        v_termInfo_711_,
                                        v___y_678_,
                                    );
                                    if lean_obj_tag(v___x_712_) == 0 {
                                        v_a_713_ = lean_ctor_get(v___x_712_, 0);
                                        lean_inc(v_a_713_);
                                        lean_dec_ref_known(v___x_712_, 1);
                                        if lean_obj_tag(v_a_713_) == 0 {
                                            lean_dec_ref(v_b_677_);
                                            lean_dec_ref(v_caps_673_);
                                            lean_dec_ref(v_pos_672_);
                                            lean_dec_ref(v_uri_671_);
                                            v_a_714_ = lean_ctor_get(v_a_713_, 0);
                                            lean_inc(v_a_714_);
                                            lean_dec_ref_known(v_a_713_, 1);
                                            v_a_681_ = v_a_714_;
                                            state = 1;
                                            continue;
                                        } else {
                                            v_a_715_ = lean_ctor_get(v_a_713_, 0);
                                            lean_inc(v_a_715_);
                                            lean_dec_ref_known(v_a_713_, 1);
                                            v_completions_685_ = v_a_715_;
                                            state = 2;
                                            continue;
                                        }
                                    } else {
                                        lean_dec_ref(v_b_677_);
                                        lean_dec_ref(v_caps_673_);
                                        lean_dec_ref(v_pos_672_);
                                        lean_dec_ref(v_uri_671_);
                                        return v___x_712_;
                                    }
                                }
                                2 => {
                                    v_ctx_716_ = lean_ctor_get(v_fst_694_, 1);
                                    v_id_717_ = lean_ctor_get(v_info_699_, 1);
                                    v_lctx_718_ = lean_ctor_get(v_info_699_, 2);
                                    v_expectedType_x3f_719_ = lean_ctor_get(v_info_699_, 3);
                                    lean_inc(v_expectedType_x3f_719_);
                                    lean_inc(v_id_717_);
                                    lean_inc_ref(v_lctx_718_);
                                    lean_inc_ref(v_ctx_716_);
                                    lean_inc(v_snd_695_);
                                    lean_inc_ref(v_pos_672_);
                                    lean_inc_ref(v_uri_671_);
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
                                    if lean_obj_tag(v___x_720_) == 0 {
                                        v_a_721_ = lean_ctor_get(v___x_720_, 0);
                                        lean_inc(v_a_721_);
                                        lean_dec_ref_known(v___x_720_, 1);
                                        if lean_obj_tag(v_a_721_) == 0 {
                                            lean_dec_ref(v_b_677_);
                                            lean_dec_ref(v_caps_673_);
                                            lean_dec_ref(v_pos_672_);
                                            lean_dec_ref(v_uri_671_);
                                            v_a_722_ = lean_ctor_get(v_a_721_, 0);
                                            lean_inc(v_a_722_);
                                            lean_dec_ref_known(v_a_721_, 1);
                                            v_a_681_ = v_a_722_;
                                            state = 1;
                                            continue;
                                        } else {
                                            v_a_723_ = lean_ctor_get(v_a_721_, 0);
                                            lean_inc(v_a_723_);
                                            lean_dec_ref_known(v_a_721_, 1);
                                            v_completions_685_ = v_a_723_;
                                            state = 2;
                                            continue;
                                        }
                                    } else {
                                        lean_dec_ref(v_b_677_);
                                        lean_dec_ref(v_caps_673_);
                                        lean_dec_ref(v_pos_672_);
                                        lean_dec_ref(v_uri_671_);
                                        return v___x_720_;
                                    }
                                }
                                3 => {
                                    v_ctx_724_ = lean_ctor_get(v_fst_694_, 1);
                                    v_id_725_ = lean_ctor_get(v_info_699_, 1);
                                    v_lctx_726_ = lean_ctor_get(v_info_699_, 2);
                                    v_structName_727_ = lean_ctor_get(v_info_699_, 3);
                                    lean_inc(v_structName_727_);
                                    lean_inc(v_id_725_);
                                    lean_inc_ref(v_lctx_726_);
                                    lean_inc_ref(v_ctx_724_);
                                    lean_inc(v_snd_695_);
                                    lean_inc_ref(v_pos_672_);
                                    lean_inc_ref(v_uri_671_);
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
                                    if lean_obj_tag(v___x_728_) == 0 {
                                        v_a_729_ = lean_ctor_get(v___x_728_, 0);
                                        lean_inc(v_a_729_);
                                        lean_dec_ref_known(v___x_728_, 1);
                                        if lean_obj_tag(v_a_729_) == 0 {
                                            lean_dec_ref(v_b_677_);
                                            lean_dec_ref(v_caps_673_);
                                            lean_dec_ref(v_pos_672_);
                                            lean_dec_ref(v_uri_671_);
                                            v_a_730_ = lean_ctor_get(v_a_729_, 0);
                                            lean_inc(v_a_730_);
                                            lean_dec_ref_known(v_a_729_, 1);
                                            v_a_681_ = v_a_730_;
                                            state = 1;
                                            continue;
                                        } else {
                                            v_a_731_ = lean_ctor_get(v_a_729_, 0);
                                            lean_inc(v_a_731_);
                                            lean_dec_ref_known(v_a_729_, 1);
                                            v_completions_685_ = v_a_731_;
                                            state = 2;
                                            continue;
                                        }
                                    } else {
                                        lean_dec_ref(v_b_677_);
                                        lean_dec_ref(v_caps_673_);
                                        lean_dec_ref(v_pos_672_);
                                        lean_dec_ref(v_uri_671_);
                                        return v___x_728_;
                                    }
                                }
                                5 => {
                                    v_ctx_732_ = lean_ctor_get(v_fst_694_, 1);
                                    v_stx_733_ = lean_ctor_get(v_info_699_, 0);
                                    lean_inc_ref(v_caps_673_);
                                    lean_inc(v_stx_733_);
                                    lean_inc_ref(v_ctx_732_);
                                    lean_inc(v_snd_695_);
                                    lean_inc_ref(v_pos_672_);
                                    lean_inc_ref(v_uri_671_);
                                    v___x_734_ = l_Lean_Server_Completion_optionCompletion(
                                        v_uri_671_,
                                        v_pos_672_,
                                        v_snd_695_,
                                        v_ctx_732_,
                                        v_stx_733_,
                                        v_caps_673_,
                                    );
                                    if lean_obj_tag(v___x_734_) == 0 {
                                        v_a_735_ = lean_ctor_get(v___x_734_, 0);
                                        lean_inc(v_a_735_);
                                        lean_dec_ref_known(v___x_734_, 1);
                                        v_completions_685_ = v_a_735_;
                                        state = 2;
                                        continue;
                                    } else {
                                        lean_dec_ref(v_b_677_);
                                        lean_dec_ref(v_caps_673_);
                                        lean_dec_ref(v_pos_672_);
                                        lean_dec_ref(v_uri_671_);
                                        v_a_736_ = lean_ctor_get(v___x_734_, 0);
                                        v_isSharedCheck_743_ =
                                            (!lean_is_exclusive(v___x_734_)) as u8;
                                        if v_isSharedCheck_743_ == 0 {
                                            v___x_738_ = v___x_734_;
                                            v_isShared_739_ = v_isSharedCheck_743_;
                                            state = 3;
                                            continue;
                                        } else {
                                            lean_inc(v_a_736_);
                                            lean_dec(v___x_734_);
                                            v___x_738_ = lean_box(0);
                                            v_isShared_739_ = v_isSharedCheck_743_;
                                            state = 3;
                                            continue;
                                        }
                                    }
                                }
                                6 => {
                                    v_ctx_744_ = lean_ctor_get(v_fst_694_, 1);
                                    v_partialId_745_ = lean_ctor_get(v_info_699_, 1);
                                    lean_inc_ref(v_caps_673_);
                                    lean_inc(v_partialId_745_);
                                    lean_inc_ref(v_ctx_744_);
                                    lean_inc(v_snd_695_);
                                    lean_inc_ref(v_pos_672_);
                                    lean_inc_ref(v_uri_671_);
                                    v___x_746_ = l_Lean_Server_Completion_errorNameCompletion(
                                        v_uri_671_,
                                        v_pos_672_,
                                        v_snd_695_,
                                        v_ctx_744_,
                                        v_partialId_745_,
                                        v_caps_673_,
                                    );
                                    if lean_obj_tag(v___x_746_) == 0 {
                                        v_a_747_ = lean_ctor_get(v___x_746_, 0);
                                        lean_inc(v_a_747_);
                                        lean_dec_ref_known(v___x_746_, 1);
                                        v_completions_685_ = v_a_747_;
                                        state = 2;
                                        continue;
                                    } else {
                                        lean_dec_ref(v_b_677_);
                                        lean_dec_ref(v_caps_673_);
                                        lean_dec_ref(v_pos_672_);
                                        lean_dec_ref(v_uri_671_);
                                        v_a_748_ = lean_ctor_get(v___x_746_, 0);
                                        v_isSharedCheck_755_ =
                                            (!lean_is_exclusive(v___x_746_)) as u8;
                                        if v_isSharedCheck_755_ == 0 {
                                            v___x_750_ = v___x_746_;
                                            v_isShared_751_ = v_isSharedCheck_755_;
                                            state = 5;
                                            continue;
                                        } else {
                                            lean_inc(v_a_748_);
                                            lean_dec(v___x_746_);
                                            v___x_750_ = lean_box(0);
                                            v_isShared_751_ = v_isSharedCheck_755_;
                                            state = 5;
                                            continue;
                                        }
                                    }
                                }
                                7 => {
                                    v_id_x3f_756_ = lean_ctor_get(v_info_699_, 1);
                                    v_danglingDot_757_ = lean_ctor_get_uint8(
                                        v_info_699_,
                                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                                    );
                                    v_scopeNames_758_ = lean_ctor_get(v_info_699_, 2);
                                    lean_inc(v_scopeNames_758_);
                                    lean_inc(v_id_x3f_756_);
                                    lean_inc(v_snd_695_);
                                    lean_inc_ref(v_pos_672_);
                                    lean_inc_ref(v_uri_671_);
                                    v___x_759_ = l_Lean_Server_Completion_endSectionCompletion(
                                        v_uri_671_,
                                        v_pos_672_,
                                        v_snd_695_,
                                        v_id_x3f_756_,
                                        v_danglingDot_757_,
                                        v_scopeNames_758_,
                                    );
                                    if lean_obj_tag(v___x_759_) == 0 {
                                        v_a_760_ = lean_ctor_get(v___x_759_, 0);
                                        lean_inc(v_a_760_);
                                        lean_dec_ref_known(v___x_759_, 1);
                                        v_completions_685_ = v_a_760_;
                                        state = 2;
                                        continue;
                                    } else {
                                        lean_dec_ref(v_b_677_);
                                        lean_dec_ref(v_caps_673_);
                                        lean_dec_ref(v_pos_672_);
                                        lean_dec_ref(v_uri_671_);
                                        v_a_761_ = lean_ctor_get(v___x_759_, 0);
                                        v_isSharedCheck_768_ =
                                            (!lean_is_exclusive(v___x_759_)) as u8;
                                        if v_isSharedCheck_768_ == 0 {
                                            v___x_763_ = v___x_759_;
                                            v_isShared_764_ = v_isSharedCheck_768_;
                                            state = 7;
                                            continue;
                                        } else {
                                            lean_inc(v_a_761_);
                                            lean_dec(v___x_759_);
                                            v___x_763_ = lean_box(0);
                                            v_isShared_764_ = v_isSharedCheck_768_;
                                            state = 7;
                                            continue;
                                        }
                                    }
                                }
                                8 => {
                                    v_ctx_769_ = lean_ctor_get(v_fst_694_, 1);
                                    lean_inc_ref(v_ctx_769_);
                                    lean_inc(v_snd_695_);
                                    lean_inc_ref(v_pos_672_);
                                    lean_inc_ref(v_uri_671_);
                                    v___x_770_ = l_Lean_Server_Completion_tacticCompletion(
                                        v_uri_671_, v_pos_672_, v_snd_695_, v_ctx_769_,
                                    );
                                    if lean_obj_tag(v___x_770_) == 0 {
                                        v_a_771_ = lean_ctor_get(v___x_770_, 0);
                                        lean_inc(v_a_771_);
                                        lean_dec_ref_known(v___x_770_, 1);
                                        v_completions_685_ = v_a_771_;
                                        state = 2;
                                        continue;
                                    } else {
                                        lean_dec_ref(v_b_677_);
                                        lean_dec_ref(v_caps_673_);
                                        lean_dec_ref(v_pos_672_);
                                        lean_dec_ref(v_uri_671_);
                                        v_a_772_ = lean_ctor_get(v___x_770_, 0);
                                        v_isSharedCheck_779_ =
                                            (!lean_is_exclusive(v___x_770_)) as u8;
                                        if v_isSharedCheck_779_ == 0 {
                                            v___x_774_ = v___x_770_;
                                            v_isShared_775_ = v_isSharedCheck_779_;
                                            state = 9;
                                            continue;
                                        } else {
                                            lean_inc(v_a_772_);
                                            lean_dec(v___x_770_);
                                            v___x_774_ = lean_box(0);
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
                        lean_dec_ref(v_b_677_);
                        lean_dec_ref(v_caps_673_);
                        lean_dec_ref(v_pos_672_);
                        lean_dec_ref(v_uri_671_);
                        v_a_781_ = lean_ctor_get(v___x_696_, 0);
                        v_isSharedCheck_788_ = (!lean_is_exclusive(v___x_696_)) as u8;
                        if v_isSharedCheck_788_ == 0 {
                            v___x_783_ = v___x_696_;
                            v_isShared_784_ = v_isSharedCheck_788_;
                            state = 11;
                            continue;
                        } else {
                            lean_inc(v_a_781_);
                            lean_dec(v___x_696_);
                            v___x_783_ = lean_box(0);
                            v_isShared_784_ = v_isSharedCheck_788_;
                            state = 11;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_682_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_682_, 0, v_a_681_);
                v___x_683_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_683_, 0, v___x_682_);
                return v___x_683_;
            }
            2 => {
                v___x_686_ = l_Array_append___redArg(v_b_677_, v_completions_685_);
                lean_dec_ref(v_completions_685_);
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
                    v_reuseFailAlloc_742_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_742_, 0, v_a_736_);
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
                    v_reuseFailAlloc_754_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_754_, 0, v_a_748_);
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
                    v_reuseFailAlloc_767_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_767_, 0, v_a_761_);
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
                    v_reuseFailAlloc_778_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_778_, 0, v_a_772_);
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
                    v_reuseFailAlloc_787_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_787_, 0, v_a_781_);
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
    mut v_uri_789_: *mut LeanObject,
    mut v_pos_790_: *mut LeanObject,
    mut v_caps_791_: *mut LeanObject,
    mut v_as_792_: *mut LeanObject,
    mut v_sz_793_: *mut LeanObject,
    mut v_i_794_: *mut LeanObject,
    mut v_b_795_: *mut LeanObject,
    mut v___y_796_: *mut LeanObject,
    mut v___y_797_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_798_: usize = 0;
    let mut v_i_boxed_799_: usize = 0;
    let mut v_res_800_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_798_ = lean_unbox_usize(v_sz_793_);
    lean_dec(v_sz_793_);
    v_i_boxed_799_ = lean_unbox_usize(v_i_794_);
    lean_dec(v_i_794_);
    v_res_800_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__0(v_uri_789_, v_pos_790_, v_caps_791_, v_as_792_, v_sz_boxed_798_, v_i_boxed_799_, v_b_795_, v___y_796_);
    lean_dec_ref(v___y_796_);
    lean_dec_ref(v_as_792_);
    return v_res_800_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__1(
    mut v_uri_801_: *mut LeanObject,
    mut v_pos_802_: *mut LeanObject,
    mut v_caps_803_: *mut LeanObject,
    mut v_as_804_: *mut LeanObject,
    mut v_sz_805_: usize,
    mut v_i_806_: usize,
    mut v_b_807_: *mut LeanObject,
    mut v___y_808_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_810_: u8 = 0;
    let mut v___x_811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_814_: usize = 0;
    let mut v___x_815_: usize = 0;
    let mut v___x_816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_821_: u8 = 0;
    let mut v___x_822_: usize = 0;
    let mut v___x_823_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_810_ = lean_usize_dec_lt(v_i_806_, v_sz_805_);
                if v___x_810_ == 0 {
                    lean_dec_ref(v_caps_803_);
                    lean_dec_ref(v_pos_802_);
                    lean_dec_ref(v_uri_801_);
                    v___x_811_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_811_, 0, v_b_807_);
                    v___x_812_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_812_, 0, v___x_811_);
                    return v___x_812_;
                } else {
                    v_a_813_ = lean_array_uget_borrowed(v_as_804_, v_i_806_);
                    v_sz_814_ = lean_array_size(v_a_813_);
                    v___x_815_ = 0usize;
                    lean_inc_ref(v_caps_803_);
                    lean_inc_ref(v_pos_802_);
                    lean_inc_ref(v_uri_801_);
                    v___x_816_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__0(v_uri_801_, v_pos_802_, v_caps_803_, v_a_813_, v_sz_814_, v___x_815_, v_b_807_, v___y_808_);
                    if lean_obj_tag(v___x_816_) == 0 {
                        v_a_817_ = lean_ctor_get(v___x_816_, 0);
                        lean_inc(v_a_817_);
                        if lean_obj_tag(v_a_817_) == 0 {
                            lean_dec_ref_known(v_a_817_, 1);
                            lean_dec_ref(v_caps_803_);
                            lean_dec_ref(v_pos_802_);
                            lean_dec_ref(v_uri_801_);
                            return v___x_816_;
                        } else {
                            v_a_818_ = lean_ctor_get(v_a_817_, 0);
                            lean_inc(v_a_818_);
                            lean_dec_ref_known(v_a_817_, 1);
                            v___x_819_ = lean_array_get_size(v_a_818_);
                            v___x_820_ = lean_unsigned_to_nat(0);
                            v___x_821_ = lean_nat_dec_eq(v___x_819_, v___x_820_);
                            if v___x_821_ == 0 {
                                lean_dec(v_a_818_);
                                lean_dec_ref(v_caps_803_);
                                lean_dec_ref(v_pos_802_);
                                lean_dec_ref(v_uri_801_);
                                return v___x_816_;
                            } else {
                                lean_dec_ref_known(v___x_816_, 1);
                                v___x_822_ = 1usize;
                                v___x_823_ = lean_usize_add(v_i_806_, v___x_822_);
                                v_i_806_ = v___x_823_;
                                v_b_807_ = v_a_818_;
                                state = 0;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_caps_803_);
                        lean_dec_ref(v_pos_802_);
                        lean_dec_ref(v_uri_801_);
                        return v___x_816_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__1___boxed(
    mut v_uri_825_: *mut LeanObject,
    mut v_pos_826_: *mut LeanObject,
    mut v_caps_827_: *mut LeanObject,
    mut v_as_828_: *mut LeanObject,
    mut v_sz_829_: *mut LeanObject,
    mut v_i_830_: *mut LeanObject,
    mut v_b_831_: *mut LeanObject,
    mut v___y_832_: *mut LeanObject,
    mut v___y_833_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_834_: usize = 0;
    let mut v_i_boxed_835_: usize = 0;
    let mut v_res_836_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_834_ = lean_unbox_usize(v_sz_829_);
    lean_dec(v_sz_829_);
    v_i_boxed_835_ = lean_unbox_usize(v_i_830_);
    lean_dec(v_i_830_);
    v_res_836_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__1(v_uri_825_, v_pos_826_, v_caps_827_, v_as_828_, v_sz_boxed_834_, v_i_boxed_835_, v_b_831_, v___y_832_);
    lean_dec_ref(v___y_832_);
    lean_dec_ref(v_as_828_);
    return v_res_836_;
}
pub unsafe fn l_Lean_Server_Completion_find_x3f(
    mut v_uri_837_: *mut LeanObject,
    mut v_pos_838_: *mut LeanObject,
    mut v_fileMap_839_: *mut LeanObject,
    mut v_hoverPos_840_: *mut LeanObject,
    mut v_cmdStx_841_: *mut LeanObject,
    mut v_infoTree_842_: *mut LeanObject,
    mut v_caps_843_: *mut LeanObject,
    mut v_a_844_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_allCompletions_849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_850_: usize = 0;
    let mut v___x_851_: usize = 0;
    let mut v___x_852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_856_: u8 = 0;
    let mut v_a_857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_860_: u8 = 0;
    let mut v___x_862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_867_: u8 = 0;
    let mut v_a_868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_871_: u8 = 0;
    let mut v___x_872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_874_: u8 = 0;
    let mut v___x_875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_882_: u8 = 0;
    let mut v___x_883_: u8 = 0;
    let mut v___x_884_: u8 = 0;
    let mut v_isSharedCheck_885_: u8 = 0;
    let mut v_isSharedCheck_886_: u8 = 0;
    let mut v_a_887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_890_: u8 = 0;
    let mut v___x_892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_893_: *mut LeanObject = core::ptr::null_mut();
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
                v_fst_847_ = lean_ctor_get(v___x_846_, 0);
                lean_inc(v_fst_847_);
                v_snd_848_ = lean_ctor_get(v___x_846_, 1);
                lean_inc(v_snd_848_);
                lean_dec_ref(v___x_846_);
                v_allCompletions_849_ = l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__0;
                v_sz_850_ = lean_array_size(v_fst_847_);
                v___x_851_ = 0usize;
                v___x_852_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__1(v_uri_837_, v_pos_838_, v_caps_843_, v_fst_847_, v_sz_850_, v___x_851_, v_allCompletions_849_, v_a_844_);
                lean_dec(v_fst_847_);
                if lean_obj_tag(v___x_852_) == 0 {
                    v_a_853_ = lean_ctor_get(v___x_852_, 0);
                    v_isSharedCheck_886_ = (!lean_is_exclusive(v___x_852_)) as u8;
                    if v_isSharedCheck_886_ == 0 {
                        v___x_855_ = v___x_852_;
                        v_isShared_856_ = v_isSharedCheck_886_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_853_);
                        lean_dec(v___x_852_);
                        v___x_855_ = lean_box(0);
                        v_isShared_856_ = v_isSharedCheck_886_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_snd_848_);
                    v_a_887_ = lean_ctor_get(v___x_852_, 0);
                    v_isSharedCheck_894_ = (!lean_is_exclusive(v___x_852_)) as u8;
                    if v_isSharedCheck_894_ == 0 {
                        v___x_889_ = v___x_852_;
                        v_isShared_890_ = v_isSharedCheck_894_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_887_);
                        lean_dec(v___x_852_);
                        v___x_889_ = lean_box(0);
                        v_isShared_890_ = v_isSharedCheck_894_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_853_) == 0 {
                    lean_dec(v_snd_848_);
                    v_a_857_ = lean_ctor_get(v_a_853_, 0);
                    v_isSharedCheck_867_ = (!lean_is_exclusive(v_a_853_)) as u8;
                    if v_isSharedCheck_867_ == 0 {
                        v___x_859_ = v_a_853_;
                        v_isShared_860_ = v_isSharedCheck_867_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_857_);
                        lean_dec(v_a_853_);
                        v___x_859_ = lean_box(0);
                        v_isShared_860_ = v_isSharedCheck_867_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_868_ = lean_ctor_get(v_a_853_, 0);
                    v_isSharedCheck_885_ = (!lean_is_exclusive(v_a_853_)) as u8;
                    if v_isSharedCheck_885_ == 0 {
                        v___x_870_ = v_a_853_;
                        v_isShared_871_ = v_isSharedCheck_885_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_868_);
                        lean_dec(v_a_853_);
                        v___x_870_ = lean_box(0);
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
                    v_reuseFailAlloc_866_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_866_, 0, v_a_857_);
                    v___x_862_ = v_reuseFailAlloc_866_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_856_ == 0 {
                    lean_ctor_set(v___x_855_, 0, v___x_862_);
                    v___x_864_ = v___x_855_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_865_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_865_, 0, v___x_862_);
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
                lean_dec(v_a_868_);
                v___x_882_ = (lean_unbox(v_snd_848_) as u8);
                lean_dec(v_snd_848_);
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
                v___x_875_ = lean_alloc_ctor(0, 1, (1) as u32);
                lean_ctor_set(v___x_875_, 0, v___x_872_);
                lean_ctor_set_uint8(
                    v___x_875_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___y_874_,
                );
                if v_isShared_871_ == 0 {
                    lean_ctor_set(v___x_870_, 0, v___x_875_);
                    v___x_877_ = v___x_870_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_881_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_881_, 0, v___x_875_);
                    v___x_877_ = v_reuseFailAlloc_881_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_856_ == 0 {
                    lean_ctor_set(v___x_855_, 0, v___x_877_);
                    v___x_879_ = v___x_855_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_880_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_880_, 0, v___x_877_);
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
                    v_reuseFailAlloc_893_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_893_, 0, v_a_887_);
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
    mut v_uri_895_: *mut LeanObject,
    mut v_pos_896_: *mut LeanObject,
    mut v_fileMap_897_: *mut LeanObject,
    mut v_hoverPos_898_: *mut LeanObject,
    mut v_cmdStx_899_: *mut LeanObject,
    mut v_infoTree_900_: *mut LeanObject,
    mut v_caps_901_: *mut LeanObject,
    mut v_a_902_: *mut LeanObject,
    mut v_a_903_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_904_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_a_902_);
    return v_res_904_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Server_Completion(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Server_Completion_CompletionCollectors(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_HashMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Server_Completion(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Server_Completion(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Server_Completion_CompletionCollectors(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Data_HashMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Server_Completion(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Server_Completion(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Server_Completion(builtin);
}
