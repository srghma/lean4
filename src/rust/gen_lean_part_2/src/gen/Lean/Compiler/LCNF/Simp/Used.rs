// Lean compiler output
// Module: Lean.Compiler.LCNF.Simp.Used
// Imports: Lean.Compiler.LCNF.Simp.SimpM Init.Omega
use crate::ffi::{
    lean_array_fget, lean_array_fset, lean_array_get_borrowed, lean_array_get_size,
    lean_array_uget_borrowed, lean_array_uset, lean_mk_array, lean_nat_add, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_sub, lean_st_ref_get, lean_st_ref_set,
    lean_st_ref_take, lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor,
    lean_usize_add, lean_usize_dec_eq, lean_usize_land, lean_usize_of_nat, lean_usize_sub,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Lean::Compiler::LCNF::Basic::{
    l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg,
    l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default,
};
use crate::r#gen::Lean::Compiler::LCNF::CompilerM::l_Lean_Compiler_LCNF_eraseCodeDecl___redArg;
use crate::r#gen::Lean::Compiler::LCNF::Simp::SimpM::{
    initialize_Lean_Compiler_LCNF_Simp_SimpM, runtime_initialize_Lean_Compiler_LCNF_Simp_SimpM,
};
use crate::r#gen::Lean::Expr::{l_Lean_instBEqFVarId_beq, l_Lean_instHashableFVarId_hash};
static mut l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0_spec__0___redArg(
    mut v_a_700_: *mut leanh::LeanObject,
    mut v_x_701_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_702_: u8 = 0;
    let mut v_key_703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_705_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_701_) == 0 {
                    v___x_702_ = 0;
                    return v___x_702_;
                } else {
                    v_key_703_ = leanh::lean_ctor_get(v_x_701_, 0);
                    v_tail_704_ = leanh::lean_ctor_get(v_x_701_, 2);
                    v___x_705_ = l_Lean_instBEqFVarId_beq(v_key_703_, v_a_700_);
                    if v___x_705_ == 0 {
                        v_x_701_ = v_tail_704_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_705_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0_spec__0___redArg___boxed(
    mut v_a_707_: *mut leanh::LeanObject,
    mut v_x_708_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_709_: u8 = 0;
    let mut v_r_710_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_709_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0_spec__0___redArg(v_a_707_, v_x_708_);
    leanh::lean_dec(v_x_708_);
    leanh::lean_dec(v_a_707_);
    v_r_710_ = leanh::lean_box((v_res_709_) as usize);
    return v_r_710_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0_spec__1_spec__2_spec__3___redArg(
    mut v_x_711_: *mut leanh::LeanObject,
    mut v_x_712_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_718_: u8 = 0;
    let mut v___x_719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_720_: u64 = 0;
    let mut v___x_721_: u64 = 0;
    let mut v___x_722_: u64 = 0;
    let mut v_fold_723_: u64 = 0;
    let mut v___x_724_: u64 = 0;
    let mut v___x_725_: u64 = 0;
    let mut v___x_726_: u64 = 0;
    let mut v___x_727_: usize = 0;
    let mut v___x_728_: usize = 0;
    let mut v___x_729_: usize = 0;
    let mut v___x_730_: usize = 0;
    let mut v___x_731_: usize = 0;
    let mut v___x_732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_738_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_712_) == 0 {
                    return v_x_711_;
                } else {
                    v_key_713_ = leanh::lean_ctor_get(v_x_712_, 0);
                    v_value_714_ = leanh::lean_ctor_get(v_x_712_, 1);
                    v_tail_715_ = leanh::lean_ctor_get(v_x_712_, 2);
                    v_isSharedCheck_738_ = (!leanh::lean_is_exclusive(v_x_712_)) as u8;
                    if v_isSharedCheck_738_ == 0 {
                        v___x_717_ = v_x_712_;
                        v_isShared_718_ = v_isSharedCheck_738_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_715_);
                        leanh::lean_inc(v_value_714_);
                        leanh::lean_inc(v_key_713_);
                        leanh::lean_dec(v_x_712_);
                        v___x_717_ = leanh::lean_box(0);
                        v_isShared_718_ = v_isSharedCheck_738_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_719_ = lean_array_get_size(v_x_711_);
                v___x_720_ = l_Lean_instHashableFVarId_hash(v_key_713_);
                v___x_721_ = 32u64;
                v___x_722_ = lean_uint64_shift_right(v___x_720_, v___x_721_);
                v_fold_723_ = lean_uint64_xor(v___x_720_, v___x_722_);
                v___x_724_ = 16u64;
                v___x_725_ = lean_uint64_shift_right(v_fold_723_, v___x_724_);
                v___x_726_ = lean_uint64_xor(v_fold_723_, v___x_725_);
                v___x_727_ = lean_uint64_to_usize(v___x_726_);
                v___x_728_ = lean_usize_of_nat(v___x_719_);
                v___x_729_ = 1usize;
                v___x_730_ = lean_usize_sub(v___x_728_, v___x_729_);
                v___x_731_ = lean_usize_land(v___x_727_, v___x_730_);
                v___x_732_ = lean_array_uget_borrowed(v_x_711_, v___x_731_);
                leanh::lean_inc(v___x_732_);
                if v_isShared_718_ == 0 {
                    leanh::lean_ctor_set(v___x_717_, 2, v___x_732_);
                    v___x_734_ = v___x_717_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_737_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_737_, 0, v_key_713_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_737_, 1, v_value_714_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_737_, 2, v___x_732_);
                    v___x_734_ = v_reuseFailAlloc_737_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_735_ = lean_array_uset(v_x_711_, v___x_731_, v___x_734_);
                v_x_711_ = v___x_735_;
                v_x_712_ = v_tail_715_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0_spec__1_spec__2___redArg(
    mut v_i_739_: *mut leanh::LeanObject,
    mut v_source_740_: *mut leanh::LeanObject,
    mut v_target_741_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_743_: u8 = 0;
    let mut v_es_744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_742_ = lean_array_get_size(v_source_740_);
                v___x_743_ = lean_nat_dec_lt(v_i_739_, v___x_742_);
                if v___x_743_ == 0 {
                    leanh::lean_dec_ref(v_source_740_);
                    leanh::lean_dec(v_i_739_);
                    return v_target_741_;
                } else {
                    v_es_744_ = lean_array_fget(v_source_740_, v_i_739_);
                    v___x_745_ = leanh::lean_box(0);
                    v_source_746_ = lean_array_fset(v_source_740_, v_i_739_, v___x_745_);
                    v_target_747_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0_spec__1_spec__2_spec__3___redArg(v_target_741_, v_es_744_);
                    v___x_748_ = leanh::lean_unsigned_to_nat(1);
                    v___x_749_ = lean_nat_add(v_i_739_, v___x_748_);
                    leanh::lean_dec(v_i_739_);
                    v_i_739_ = v___x_749_;
                    v_source_740_ = v_source_746_;
                    v_target_741_ = v_target_747_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0_spec__1___redArg(
    mut v_data_751_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_758_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_752_ = lean_array_get_size(v_data_751_);
    v___x_753_ = leanh::lean_unsigned_to_nat(2);
    v_nbuckets_754_ = lean_nat_mul(v___x_752_, v___x_753_);
    v___x_755_ = leanh::lean_unsigned_to_nat(0);
    v___x_756_ = leanh::lean_box(0);
    v___x_757_ = lean_mk_array(v_nbuckets_754_, v___x_756_);
    v___x_758_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0_spec__1_spec__2___redArg(v___x_755_, v_data_751_, v___x_757_);
    return v___x_758_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0___redArg(
    mut v_m_759_: *mut leanh::LeanObject,
    mut v_a_760_: *mut leanh::LeanObject,
    mut v_b_761_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_765_: u64 = 0;
    let mut v___x_766_: u64 = 0;
    let mut v___x_767_: u64 = 0;
    let mut v_fold_768_: u64 = 0;
    let mut v___x_769_: u64 = 0;
    let mut v___x_770_: u64 = 0;
    let mut v___x_771_: u64 = 0;
    let mut v___x_772_: usize = 0;
    let mut v___x_773_: usize = 0;
    let mut v___x_774_: usize = 0;
    let mut v___x_775_: usize = 0;
    let mut v___x_776_: usize = 0;
    let mut v_bkt_777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_778_: u8 = 0;
    let mut v___x_780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_781_: u8 = 0;
    let mut v___x_782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_791_: u8 = 0;
    let mut v_val_792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_799_: u8 = 0;
    let mut v_unused_800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_762_ = leanh::lean_ctor_get(v_m_759_, 0);
                v_buckets_763_ = leanh::lean_ctor_get(v_m_759_, 1);
                v___x_764_ = lean_array_get_size(v_buckets_763_);
                v___x_765_ = l_Lean_instHashableFVarId_hash(v_a_760_);
                v___x_766_ = 32u64;
                v___x_767_ = lean_uint64_shift_right(v___x_765_, v___x_766_);
                v_fold_768_ = lean_uint64_xor(v___x_765_, v___x_767_);
                v___x_769_ = 16u64;
                v___x_770_ = lean_uint64_shift_right(v_fold_768_, v___x_769_);
                v___x_771_ = lean_uint64_xor(v_fold_768_, v___x_770_);
                v___x_772_ = lean_uint64_to_usize(v___x_771_);
                v___x_773_ = lean_usize_of_nat(v___x_764_);
                v___x_774_ = 1usize;
                v___x_775_ = lean_usize_sub(v___x_773_, v___x_774_);
                v___x_776_ = lean_usize_land(v___x_772_, v___x_775_);
                v_bkt_777_ = lean_array_uget_borrowed(v_buckets_763_, v___x_776_);
                v___x_778_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0_spec__0___redArg(v_a_760_, v_bkt_777_);
                if v___x_778_ == 0 {
                    leanh::lean_inc_ref(v_buckets_763_);
                    leanh::lean_inc(v_size_762_);
                    v_isSharedCheck_799_ = (!leanh::lean_is_exclusive(v_m_759_)) as u8;
                    if v_isSharedCheck_799_ == 0 {
                        v_unused_800_ = leanh::lean_ctor_get(v_m_759_, 1);
                        leanh::lean_dec(v_unused_800_);
                        v_unused_801_ = leanh::lean_ctor_get(v_m_759_, 0);
                        leanh::lean_dec(v_unused_801_);
                        v___x_780_ = v_m_759_;
                        v_isShared_781_ = v_isSharedCheck_799_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_m_759_);
                        v___x_780_ = leanh::lean_box(0);
                        v_isShared_781_ = v_isSharedCheck_799_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_b_761_);
                    leanh::lean_dec(v_a_760_);
                    return v_m_759_;
                }
            }
            1 => {
                v___x_782_ = leanh::lean_unsigned_to_nat(1);
                v_size_x27_783_ = lean_nat_add(v_size_762_, v___x_782_);
                leanh::lean_dec(v_size_762_);
                leanh::lean_inc(v_bkt_777_);
                v___x_784_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_784_, 0, v_a_760_);
                leanh::lean_ctor_set(v___x_784_, 1, v_b_761_);
                leanh::lean_ctor_set(v___x_784_, 2, v_bkt_777_);
                v_buckets_x27_785_ = lean_array_uset(v_buckets_763_, v___x_776_, v___x_784_);
                v___x_786_ = leanh::lean_unsigned_to_nat(4);
                v___x_787_ = lean_nat_mul(v_size_x27_783_, v___x_786_);
                v___x_788_ = leanh::lean_unsigned_to_nat(3);
                v___x_789_ = lean_nat_div(v___x_787_, v___x_788_);
                leanh::lean_dec(v___x_787_);
                v___x_790_ = lean_array_get_size(v_buckets_x27_785_);
                v___x_791_ = lean_nat_dec_le(v___x_789_, v___x_790_);
                leanh::lean_dec(v___x_789_);
                if v___x_791_ == 0 {
                    v_val_792_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0_spec__1___redArg(v_buckets_x27_785_);
                    if v_isShared_781_ == 0 {
                        leanh::lean_ctor_set(v___x_780_, 1, v_val_792_);
                        leanh::lean_ctor_set(v___x_780_, 0, v_size_x27_783_);
                        v___x_794_ = v___x_780_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_795_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_795_, 0, v_size_x27_783_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_795_, 1, v_val_792_);
                        v___x_794_ = v_reuseFailAlloc_795_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_781_ == 0 {
                        leanh::lean_ctor_set(v___x_780_, 1, v_buckets_x27_785_);
                        leanh::lean_ctor_set(v___x_780_, 0, v_size_x27_783_);
                        v___x_797_ = v___x_780_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_798_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_798_, 0, v_size_x27_783_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_798_, 1, v_buckets_x27_785_);
                        v___x_797_ = v_reuseFailAlloc_798_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_794_;
            }
            3 => {
                return v___x_797_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(
    mut v_fvarId_802_: *mut leanh::LeanObject,
    mut v_a_803_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_subst_806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_used_807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderRenaming_808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_funDeclInfoMap_809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_simplified_810_: u8 = 0;
    let mut v_visited_811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inline_812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inlineLocal_813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_816_: u8 = 0;
    let mut v___x_817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_824_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_805_ = lean_st_ref_take(v_a_803_);
                v_subst_806_ = leanh::lean_ctor_get(v___x_805_, 0);
                v_used_807_ = leanh::lean_ctor_get(v___x_805_, 1);
                v_binderRenaming_808_ = leanh::lean_ctor_get(v___x_805_, 2);
                v_funDeclInfoMap_809_ = leanh::lean_ctor_get(v___x_805_, 3);
                v_simplified_810_ = leanh::lean_ctor_get_uint8(
                    v___x_805_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                );
                v_visited_811_ = leanh::lean_ctor_get(v___x_805_, 4);
                v_inline_812_ = leanh::lean_ctor_get(v___x_805_, 5);
                v_inlineLocal_813_ = leanh::lean_ctor_get(v___x_805_, 6);
                v_isSharedCheck_824_ = (!leanh::lean_is_exclusive(v___x_805_)) as u8;
                if v_isSharedCheck_824_ == 0 {
                    v___x_815_ = v___x_805_;
                    v_isShared_816_ = v_isSharedCheck_824_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_inlineLocal_813_);
                    leanh::lean_inc(v_inline_812_);
                    leanh::lean_inc(v_visited_811_);
                    leanh::lean_inc(v_funDeclInfoMap_809_);
                    leanh::lean_inc(v_binderRenaming_808_);
                    leanh::lean_inc(v_used_807_);
                    leanh::lean_inc(v_subst_806_);
                    leanh::lean_dec(v___x_805_);
                    v___x_815_ = leanh::lean_box(0);
                    v_isShared_816_ = v_isSharedCheck_824_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_817_ = leanh::lean_box(0);
                v___x_818_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0___redArg(v_used_807_, v_fvarId_802_, v___x_817_);
                if v_isShared_816_ == 0 {
                    leanh::lean_ctor_set(v___x_815_, 1, v___x_818_);
                    v___x_820_ = v___x_815_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_823_ = leanh::lean_alloc_ctor(0, 7, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_823_, 0, v_subst_806_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_823_, 1, v___x_818_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_823_, 2, v_binderRenaming_808_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_823_, 3, v_funDeclInfoMap_809_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_823_, 4, v_visited_811_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_823_, 5, v_inline_812_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_823_, 6, v_inlineLocal_813_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_823_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                        v_simplified_810_,
                    );
                    v___x_820_ = v_reuseFailAlloc_823_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_821_ = lean_st_ref_set(v_a_803_, v___x_820_);
                v___x_822_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_822_, 0, v___x_817_);
                return v___x_822_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg___boxed(
    mut v_fvarId_825_: *mut leanh::LeanObject,
    mut v_a_826_: *mut leanh::LeanObject,
    mut v_a_827_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_828_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_828_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_fvarId_825_, v_a_826_);
    leanh::lean_dec(v_a_826_);
    return v_res_828_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_markUsedFVar(
    mut v_fvarId_829_: *mut leanh::LeanObject,
    mut v_a_830_: *mut leanh::LeanObject,
    mut v_a_831_: *mut leanh::LeanObject,
    mut v_a_832_: *mut leanh::LeanObject,
    mut v_a_833_: *mut leanh::LeanObject,
    mut v_a_834_: *mut leanh::LeanObject,
    mut v_a_835_: *mut leanh::LeanObject,
    mut v_a_836_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_838_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_838_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_fvarId_829_, v_a_831_);
    return v___x_838_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_markUsedFVar___boxed(
    mut v_fvarId_839_: *mut leanh::LeanObject,
    mut v_a_840_: *mut leanh::LeanObject,
    mut v_a_841_: *mut leanh::LeanObject,
    mut v_a_842_: *mut leanh::LeanObject,
    mut v_a_843_: *mut leanh::LeanObject,
    mut v_a_844_: *mut leanh::LeanObject,
    mut v_a_845_: *mut leanh::LeanObject,
    mut v_a_846_: *mut leanh::LeanObject,
    mut v_a_847_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_848_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_848_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar(
        v_fvarId_839_,
        v_a_840_,
        v_a_841_,
        v_a_842_,
        v_a_843_,
        v_a_844_,
        v_a_845_,
        v_a_846_,
    );
    leanh::lean_dec(v_a_846_);
    leanh::lean_dec_ref(v_a_845_);
    leanh::lean_dec(v_a_844_);
    leanh::lean_dec_ref(v_a_843_);
    leanh::lean_dec_ref(v_a_842_);
    leanh::lean_dec(v_a_841_);
    leanh::lean_dec_ref(v_a_840_);
    return v_res_848_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0(
    mut v_00_u03b2_849_: *mut leanh::LeanObject,
    mut v_m_850_: *mut leanh::LeanObject,
    mut v_a_851_: *mut leanh::LeanObject,
    mut v_b_852_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_853_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_853_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0___redArg(v_m_850_, v_a_851_, v_b_852_);
    return v___x_853_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0_spec__0(
    mut v_00_u03b2_854_: *mut leanh::LeanObject,
    mut v_a_855_: *mut leanh::LeanObject,
    mut v_x_856_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_857_: u8 = 0;
    v___x_857_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0_spec__0___redArg(v_a_855_, v_x_856_);
    return v___x_857_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0_spec__0___boxed(
    mut v_00_u03b2_858_: *mut leanh::LeanObject,
    mut v_a_859_: *mut leanh::LeanObject,
    mut v_x_860_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_861_: u8 = 0;
    let mut v_r_862_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_861_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0_spec__0(v_00_u03b2_858_, v_a_859_, v_x_860_);
    leanh::lean_dec(v_x_860_);
    leanh::lean_dec(v_a_859_);
    v_r_862_ = leanh::lean_box((v_res_861_) as usize);
    return v_r_862_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0_spec__1(
    mut v_00_u03b2_863_: *mut leanh::LeanObject,
    mut v_data_864_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_865_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_865_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0_spec__1___redArg(v_data_864_);
    return v___x_865_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0_spec__1_spec__2(
    mut v_00_u03b2_866_: *mut leanh::LeanObject,
    mut v_i_867_: *mut leanh::LeanObject,
    mut v_source_868_: *mut leanh::LeanObject,
    mut v_target_869_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_870_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_870_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0_spec__1_spec__2___redArg(v_i_867_, v_source_868_, v_target_869_);
    return v___x_870_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0_spec__1_spec__2_spec__3(
    mut v_00_u03b2_871_: *mut leanh::LeanObject,
    mut v_x_872_: *mut leanh::LeanObject,
    mut v_x_873_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_874_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_874_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0_spec__1_spec__2_spec__3___redArg(v_x_872_, v_x_873_);
    return v___x_874_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_markUsedArg___redArg(
    mut v_arg_875_: *mut leanh::LeanObject,
    mut v_a_876_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_arg_875_) == 1 {
        let mut v_fvarId_878_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_879_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_fvarId_878_ = leanh::lean_ctor_get(v_arg_875_, 0);
        leanh::lean_inc(v_fvarId_878_);
        leanh::lean_dec_ref_known(v_arg_875_, 1);
        v___x_879_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_fvarId_878_, v_a_876_);
        return v___x_879_;
    } else {
        let mut v___x_880_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_881_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_arg_875_);
        v___x_880_ = leanh::lean_box(0);
        v___x_881_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_881_, 0, v___x_880_);
        return v___x_881_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_markUsedArg___redArg___boxed(
    mut v_arg_882_: *mut leanh::LeanObject,
    mut v_a_883_: *mut leanh::LeanObject,
    mut v_a_884_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_885_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_885_ = l_Lean_Compiler_LCNF_Simp_markUsedArg___redArg(v_arg_882_, v_a_883_);
    leanh::lean_dec(v_a_883_);
    return v_res_885_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_markUsedArg(
    mut v_arg_886_: *mut leanh::LeanObject,
    mut v_a_887_: *mut leanh::LeanObject,
    mut v_a_888_: *mut leanh::LeanObject,
    mut v_a_889_: *mut leanh::LeanObject,
    mut v_a_890_: *mut leanh::LeanObject,
    mut v_a_891_: *mut leanh::LeanObject,
    mut v_a_892_: *mut leanh::LeanObject,
    mut v_a_893_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_895_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_895_ = l_Lean_Compiler_LCNF_Simp_markUsedArg___redArg(v_arg_886_, v_a_888_);
    return v___x_895_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_markUsedArg___boxed(
    mut v_arg_896_: *mut leanh::LeanObject,
    mut v_a_897_: *mut leanh::LeanObject,
    mut v_a_898_: *mut leanh::LeanObject,
    mut v_a_899_: *mut leanh::LeanObject,
    mut v_a_900_: *mut leanh::LeanObject,
    mut v_a_901_: *mut leanh::LeanObject,
    mut v_a_902_: *mut leanh::LeanObject,
    mut v_a_903_: *mut leanh::LeanObject,
    mut v_a_904_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_905_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_905_ = l_Lean_Compiler_LCNF_Simp_markUsedArg(
        v_arg_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_,
    );
    leanh::lean_dec(v_a_903_);
    leanh::lean_dec_ref(v_a_902_);
    leanh::lean_dec(v_a_901_);
    leanh::lean_dec_ref(v_a_900_);
    leanh::lean_dec_ref(v_a_899_);
    leanh::lean_dec(v_a_898_);
    leanh::lean_dec_ref(v_a_897_);
    return v_res_905_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___redArg(
    mut v_as_906_: *mut leanh::LeanObject,
    mut v_i_907_: usize,
    mut v_stop_908_: usize,
    mut v_b_909_: *mut leanh::LeanObject,
    mut v___y_910_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_912_: u8 = 0;
    let mut v___x_913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_916_: usize = 0;
    let mut v___x_917_: usize = 0;
    let mut v___x_919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_912_ = lean_usize_dec_eq(v_i_907_, v_stop_908_);
                if v___x_912_ == 0 {
                    v___x_913_ = lean_array_uget_borrowed(v_as_906_, v_i_907_);
                    leanh::lean_inc(v___x_913_);
                    v___x_914_ =
                        l_Lean_Compiler_LCNF_Simp_markUsedArg___redArg(v___x_913_, v___y_910_);
                    if leanh::lean_obj_tag(v___x_914_) == 0 {
                        v_a_915_ = leanh::lean_ctor_get(v___x_914_, 0);
                        leanh::lean_inc(v_a_915_);
                        leanh::lean_dec_ref_known(v___x_914_, 1);
                        v___x_916_ = 1usize;
                        v___x_917_ = lean_usize_add(v_i_907_, v___x_916_);
                        v_i_907_ = v___x_917_;
                        v_b_909_ = v_a_915_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_914_;
                    }
                } else {
                    v___x_919_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_919_, 0, v_b_909_);
                    return v___x_919_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___redArg___boxed(
    mut v_as_920_: *mut leanh::LeanObject,
    mut v_i_921_: *mut leanh::LeanObject,
    mut v_stop_922_: *mut leanh::LeanObject,
    mut v_b_923_: *mut leanh::LeanObject,
    mut v___y_924_: *mut leanh::LeanObject,
    mut v___y_925_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_926_: usize = 0;
    let mut v_stop_boxed_927_: usize = 0;
    let mut v_res_928_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_926_ = leanh::lean_unbox_usize(v_i_921_);
    leanh::lean_dec(v_i_921_);
    v_stop_boxed_927_ = leanh::lean_unbox_usize(v_stop_922_);
    leanh::lean_dec(v_stop_922_);
    v_res_928_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___redArg(v_as_920_, v_i_boxed_926_, v_stop_boxed_927_, v_b_923_, v___y_924_);
    leanh::lean_dec(v___y_924_);
    leanh::lean_dec_ref(v_as_920_);
    return v_res_928_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_markUsedLetValue(
    mut v_e_929_: *mut leanh::LeanObject,
    mut v_a_930_: *mut leanh::LeanObject,
    mut v_a_931_: *mut leanh::LeanObject,
    mut v_a_932_: *mut leanh::LeanObject,
    mut v_a_933_: *mut leanh::LeanObject,
    mut v_a_934_: *mut leanh::LeanObject,
    mut v_a_935_: *mut leanh::LeanObject,
    mut v_a_936_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_940_: u8 = 0;
    let mut v___x_941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_945_: u8 = 0;
    let mut v_unused_946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_955_: u8 = 0;
    let mut v___x_956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_957_: u8 = 0;
    let mut v___x_958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_959_: usize = 0;
    let mut v___x_960_: usize = 0;
    let mut v___x_961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_962_: usize = 0;
    let mut v___x_963_: usize = 0;
    let mut v___x_964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_970_: u8 = 0;
    let mut v___x_971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_974_: u8 = 0;
    let mut v___x_976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_978_: u8 = 0;
    let mut v___x_980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_982_: usize = 0;
    let mut v___x_983_: usize = 0;
    let mut v___x_984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_985_: usize = 0;
    let mut v___x_986_: usize = 0;
    let mut v___x_987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_988_: u8 = 0;
    let mut v_unused_989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_e_929_) {
                0 => {
                    v_isSharedCheck_945_ = (!leanh::lean_is_exclusive(v_e_929_)) as u8;
                    if v_isSharedCheck_945_ == 0 {
                        v_unused_946_ = leanh::lean_ctor_get(v_e_929_, 0);
                        leanh::lean_dec(v_unused_946_);
                        v___x_939_ = v_e_929_;
                        v_isShared_940_ = v_isSharedCheck_945_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_e_929_);
                        v___x_939_ = leanh::lean_box(0);
                        v_isShared_940_ = v_isSharedCheck_945_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v___x_947_ = leanh::lean_box(0);
                    v___x_948_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_948_, 0, v___x_947_);
                    return v___x_948_;
                }
                2 => {
                    v_struct_949_ = leanh::lean_ctor_get(v_e_929_, 2);
                    leanh::lean_inc(v_struct_949_);
                    leanh::lean_dec_ref_known(v_e_929_, 3);
                    v___x_950_ =
                        l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_struct_949_, v_a_931_);
                    return v___x_950_;
                }
                3 => {
                    v_args_951_ = leanh::lean_ctor_get(v_e_929_, 2);
                    leanh::lean_inc_ref(v_args_951_);
                    leanh::lean_dec_ref_known(v_e_929_, 3);
                    v___x_952_ = leanh::lean_unsigned_to_nat(0);
                    v___x_953_ = lean_array_get_size(v_args_951_);
                    v___x_954_ = leanh::lean_box(0);
                    v___x_955_ = lean_nat_dec_lt(v___x_952_, v___x_953_);
                    if v___x_955_ == 0 {
                        leanh::lean_dec_ref(v_args_951_);
                        v___x_956_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_956_, 0, v___x_954_);
                        return v___x_956_;
                    } else {
                        v___x_957_ = lean_nat_dec_le(v___x_953_, v___x_953_);
                        if v___x_957_ == 0 {
                            if v___x_955_ == 0 {
                                leanh::lean_dec_ref(v_args_951_);
                                v___x_958_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_958_, 0, v___x_954_);
                                return v___x_958_;
                            } else {
                                v___x_959_ = 0usize;
                                v___x_960_ = lean_usize_of_nat(v___x_953_);
                                v___x_961_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___redArg(v_args_951_, v___x_959_, v___x_960_, v___x_954_, v_a_931_);
                                leanh::lean_dec_ref(v_args_951_);
                                return v___x_961_;
                            }
                        } else {
                            v___x_962_ = 0usize;
                            v___x_963_ = lean_usize_of_nat(v___x_953_);
                            v___x_964_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___redArg(v_args_951_, v___x_962_, v___x_963_, v___x_954_, v_a_931_);
                            leanh::lean_dec_ref(v_args_951_);
                            return v___x_964_;
                        }
                    }
                }
                _ => {
                    v_fvarId_965_ = leanh::lean_ctor_get(v_e_929_, 0);
                    leanh::lean_inc(v_fvarId_965_);
                    v_args_966_ = leanh::lean_ctor_get(v_e_929_, 1);
                    leanh::lean_inc_ref(v_args_966_);
                    leanh::lean_dec_ref_known(v_e_929_, 2);
                    v___x_967_ =
                        l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_fvarId_965_, v_a_931_);
                    v_isSharedCheck_988_ = (!leanh::lean_is_exclusive(v___x_967_)) as u8;
                    if v_isSharedCheck_988_ == 0 {
                        v_unused_989_ = leanh::lean_ctor_get(v___x_967_, 0);
                        leanh::lean_dec(v_unused_989_);
                        v___x_969_ = v___x_967_;
                        v_isShared_970_ = v_isSharedCheck_988_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_967_);
                        v___x_969_ = leanh::lean_box(0);
                        v_isShared_970_ = v_isSharedCheck_988_;
                        state = 3;
                        continue;
                    }
                }
            },
            1 => {
                v___x_941_ = leanh::lean_box(0);
                if v_isShared_940_ == 0 {
                    leanh::lean_ctor_set(v___x_939_, 0, v___x_941_);
                    v___x_943_ = v___x_939_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_944_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_944_, 0, v___x_941_);
                    v___x_943_ = v_reuseFailAlloc_944_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_943_;
            }
            3 => {
                v___x_971_ = leanh::lean_unsigned_to_nat(0);
                v___x_972_ = lean_array_get_size(v_args_966_);
                v___x_973_ = leanh::lean_box(0);
                v___x_974_ = lean_nat_dec_lt(v___x_971_, v___x_972_);
                if v___x_974_ == 0 {
                    leanh::lean_dec_ref(v_args_966_);
                    if v_isShared_970_ == 0 {
                        leanh::lean_ctor_set(v___x_969_, 0, v___x_973_);
                        v___x_976_ = v___x_969_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_977_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_977_, 0, v___x_973_);
                        v___x_976_ = v_reuseFailAlloc_977_;
                        state = 4;
                        continue;
                    }
                } else {
                    v___x_978_ = lean_nat_dec_le(v___x_972_, v___x_972_);
                    if v___x_978_ == 0 {
                        if v___x_974_ == 0 {
                            leanh::lean_dec_ref(v_args_966_);
                            if v_isShared_970_ == 0 {
                                leanh::lean_ctor_set(v___x_969_, 0, v___x_973_);
                                v___x_980_ = v___x_969_;
                                state = 5;
                                continue;
                            } else {
                                v_reuseFailAlloc_981_ =
                                    leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_981_, 0, v___x_973_);
                                v___x_980_ = v_reuseFailAlloc_981_;
                                state = 5;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_969_);
                            v___x_982_ = 0usize;
                            v___x_983_ = lean_usize_of_nat(v___x_972_);
                            v___x_984_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___redArg(v_args_966_, v___x_982_, v___x_983_, v___x_973_, v_a_931_);
                            leanh::lean_dec_ref(v_args_966_);
                            return v___x_984_;
                        }
                    } else {
                        leanh::lean_del_object(v___x_969_);
                        v___x_985_ = 0usize;
                        v___x_986_ = lean_usize_of_nat(v___x_972_);
                        v___x_987_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___redArg(v_args_966_, v___x_985_, v___x_986_, v___x_973_, v_a_931_);
                        leanh::lean_dec_ref(v_args_966_);
                        return v___x_987_;
                    }
                }
            }
            4 => {
                return v___x_976_;
            }
            5 => {
                return v___x_980_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_markUsedLetValue___boxed(
    mut v_e_990_: *mut leanh::LeanObject,
    mut v_a_991_: *mut leanh::LeanObject,
    mut v_a_992_: *mut leanh::LeanObject,
    mut v_a_993_: *mut leanh::LeanObject,
    mut v_a_994_: *mut leanh::LeanObject,
    mut v_a_995_: *mut leanh::LeanObject,
    mut v_a_996_: *mut leanh::LeanObject,
    mut v_a_997_: *mut leanh::LeanObject,
    mut v_a_998_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_999_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_999_ = l_Lean_Compiler_LCNF_Simp_markUsedLetValue(
        v_e_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_, v_a_995_, v_a_996_, v_a_997_,
    );
    leanh::lean_dec(v_a_997_);
    leanh::lean_dec_ref(v_a_996_);
    leanh::lean_dec(v_a_995_);
    leanh::lean_dec_ref(v_a_994_);
    leanh::lean_dec_ref(v_a_993_);
    leanh::lean_dec(v_a_992_);
    leanh::lean_dec_ref(v_a_991_);
    return v_res_999_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0(
    mut v_as_1000_: *mut leanh::LeanObject,
    mut v_i_1001_: usize,
    mut v_stop_1002_: usize,
    mut v_b_1003_: *mut leanh::LeanObject,
    mut v___y_1004_: *mut leanh::LeanObject,
    mut v___y_1005_: *mut leanh::LeanObject,
    mut v___y_1006_: *mut leanh::LeanObject,
    mut v___y_1007_: *mut leanh::LeanObject,
    mut v___y_1008_: *mut leanh::LeanObject,
    mut v___y_1009_: *mut leanh::LeanObject,
    mut v___y_1010_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1012_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1012_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___redArg(v_as_1000_, v_i_1001_, v_stop_1002_, v_b_1003_, v___y_1005_);
    return v___x_1012_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___boxed(
    mut v_as_1013_: *mut leanh::LeanObject,
    mut v_i_1014_: *mut leanh::LeanObject,
    mut v_stop_1015_: *mut leanh::LeanObject,
    mut v_b_1016_: *mut leanh::LeanObject,
    mut v___y_1017_: *mut leanh::LeanObject,
    mut v___y_1018_: *mut leanh::LeanObject,
    mut v___y_1019_: *mut leanh::LeanObject,
    mut v___y_1020_: *mut leanh::LeanObject,
    mut v___y_1021_: *mut leanh::LeanObject,
    mut v___y_1022_: *mut leanh::LeanObject,
    mut v___y_1023_: *mut leanh::LeanObject,
    mut v___y_1024_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1025_: usize = 0;
    let mut v_stop_boxed_1026_: usize = 0;
    let mut v_res_1027_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1025_ = leanh::lean_unbox_usize(v_i_1014_);
    leanh::lean_dec(v_i_1014_);
    v_stop_boxed_1026_ = leanh::lean_unbox_usize(v_stop_1015_);
    leanh::lean_dec(v_stop_1015_);
    v_res_1027_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0(v_as_1013_, v_i_boxed_1025_, v_stop_boxed_1026_, v_b_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_);
    leanh::lean_dec(v___y_1023_);
    leanh::lean_dec_ref(v___y_1022_);
    leanh::lean_dec(v___y_1021_);
    leanh::lean_dec_ref(v___y_1020_);
    leanh::lean_dec_ref(v___y_1019_);
    leanh::lean_dec(v___y_1018_);
    leanh::lean_dec_ref(v___y_1017_);
    leanh::lean_dec_ref(v_as_1013_);
    return v_res_1027_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(
    mut v_letDecl_1028_: *mut leanh::LeanObject,
    mut v_a_1029_: *mut leanh::LeanObject,
    mut v_a_1030_: *mut leanh::LeanObject,
    mut v_a_1031_: *mut leanh::LeanObject,
    mut v_a_1032_: *mut leanh::LeanObject,
    mut v_a_1033_: *mut leanh::LeanObject,
    mut v_a_1034_: *mut leanh::LeanObject,
    mut v_a_1035_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_value_1037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_value_1037_ = leanh::lean_ctor_get(v_letDecl_1028_, 3);
    leanh::lean_inc(v_value_1037_);
    leanh::lean_dec_ref(v_letDecl_1028_);
    v___x_1038_ = l_Lean_Compiler_LCNF_Simp_markUsedLetValue(
        v_value_1037_,
        v_a_1029_,
        v_a_1030_,
        v_a_1031_,
        v_a_1032_,
        v_a_1033_,
        v_a_1034_,
        v_a_1035_,
    );
    return v___x_1038_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_markUsedLetDecl___boxed(
    mut v_letDecl_1039_: *mut leanh::LeanObject,
    mut v_a_1040_: *mut leanh::LeanObject,
    mut v_a_1041_: *mut leanh::LeanObject,
    mut v_a_1042_: *mut leanh::LeanObject,
    mut v_a_1043_: *mut leanh::LeanObject,
    mut v_a_1044_: *mut leanh::LeanObject,
    mut v_a_1045_: *mut leanh::LeanObject,
    mut v_a_1046_: *mut leanh::LeanObject,
    mut v_a_1047_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1048_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1048_ = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(
        v_letDecl_1039_,
        v_a_1040_,
        v_a_1041_,
        v_a_1042_,
        v_a_1043_,
        v_a_1044_,
        v_a_1045_,
        v_a_1046_,
    );
    leanh::lean_dec(v_a_1046_);
    leanh::lean_dec_ref(v_a_1045_);
    leanh::lean_dec(v_a_1044_);
    leanh::lean_dec_ref(v_a_1043_);
    leanh::lean_dec_ref(v_a_1042_);
    leanh::lean_dec(v_a_1041_);
    leanh::lean_dec_ref(v_a_1040_);
    return v_res_1048_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedCode_spec__0(
    mut v_as_1049_: *mut leanh::LeanObject,
    mut v_i_1050_: usize,
    mut v_stop_1051_: usize,
    mut v_b_1052_: *mut leanh::LeanObject,
    mut v___y_1053_: *mut leanh::LeanObject,
    mut v___y_1054_: *mut leanh::LeanObject,
    mut v___y_1055_: *mut leanh::LeanObject,
    mut v___y_1056_: *mut leanh::LeanObject,
    mut v___y_1057_: *mut leanh::LeanObject,
    mut v___y_1058_: *mut leanh::LeanObject,
    mut v___y_1059_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: usize = 0;
    let mut v___x_1066_: usize = 0;
    let mut v___x_1068_: u8 = 0;
    let mut v___x_1069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_1070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_1071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_1072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1068_ = lean_usize_dec_eq(v_i_1050_, v_stop_1051_);
                if v___x_1068_ == 0 {
                    v___x_1069_ = lean_array_uget_borrowed(v_as_1049_, v_i_1050_);
                    match leanh::lean_obj_tag(v___x_1069_) {
                        0 => {
                            v_code_1070_ = leanh::lean_ctor_get(v___x_1069_, 2);
                            leanh::lean_inc_ref(v_code_1070_);
                            v___y_1062_ = v_code_1070_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v_code_1071_ = leanh::lean_ctor_get(v___x_1069_, 1);
                            leanh::lean_inc_ref(v_code_1071_);
                            v___y_1062_ = v_code_1071_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v_code_1072_ = leanh::lean_ctor_get(v___x_1069_, 0);
                            leanh::lean_inc_ref(v_code_1072_);
                            v___y_1062_ = v_code_1072_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v___x_1073_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1073_, 0, v_b_1052_);
                    return v___x_1073_;
                }
            }
            1 => {
                v___x_1063_ = l_Lean_Compiler_LCNF_Simp_markUsedCode(
                    v___y_1062_,
                    v___y_1053_,
                    v___y_1054_,
                    v___y_1055_,
                    v___y_1056_,
                    v___y_1057_,
                    v___y_1058_,
                    v___y_1059_,
                );
                if leanh::lean_obj_tag(v___x_1063_) == 0 {
                    v_a_1064_ = leanh::lean_ctor_get(v___x_1063_, 0);
                    leanh::lean_inc(v_a_1064_);
                    leanh::lean_dec_ref_known(v___x_1063_, 1);
                    v___x_1065_ = 1usize;
                    v___x_1066_ = lean_usize_add(v_i_1050_, v___x_1065_);
                    v_i_1050_ = v___x_1066_;
                    v_b_1052_ = v_a_1064_;
                    state = 0;
                    continue;
                } else {
                    return v___x_1063_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_markUsedCode(
    mut v_code_1074_: *mut leanh::LeanObject,
    mut v_a_1075_: *mut leanh::LeanObject,
    mut v_a_1076_: *mut leanh::LeanObject,
    mut v_a_1077_: *mut leanh::LeanObject,
    mut v_a_1078_: *mut leanh::LeanObject,
    mut v_a_1079_: *mut leanh::LeanObject,
    mut v_a_1080_: *mut leanh::LeanObject,
    mut v_a_1081_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_decl_1084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_1095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_1100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1104_: u8 = 0;
    let mut v___x_1105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1108_: u8 = 0;
    let mut v___x_1110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1112_: u8 = 0;
    let mut v___x_1114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1116_: usize = 0;
    let mut v___x_1117_: usize = 0;
    let mut v___x_1118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1119_: usize = 0;
    let mut v___x_1120_: usize = 0;
    let mut v___x_1121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1122_: u8 = 0;
    let mut v_unused_1123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cases_1124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_discr_1125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_alts_1126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1130_: u8 = 0;
    let mut v___x_1131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: u8 = 0;
    let mut v___x_1136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: u8 = 0;
    let mut v___x_1140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: usize = 0;
    let mut v___x_1143_: usize = 0;
    let mut v___x_1144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: usize = 0;
    let mut v___x_1146_: usize = 0;
    let mut v___x_1147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1148_: u8 = 0;
    let mut v_unused_1149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1154_: u8 = 0;
    let mut v___x_1155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1159_: u8 = 0;
    let mut v_unused_1160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_1161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_code_1074_) {
                0 => {
                    v_decl_1095_ = leanh::lean_ctor_get(v_code_1074_, 0);
                    leanh::lean_inc_ref(v_decl_1095_);
                    v_k_1096_ = leanh::lean_ctor_get(v_code_1074_, 1);
                    leanh::lean_inc_ref(v_k_1096_);
                    leanh::lean_dec_ref_known(v_code_1074_, 2);
                    v___x_1097_ = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(
                        v_decl_1095_,
                        v_a_1075_,
                        v_a_1076_,
                        v_a_1077_,
                        v_a_1078_,
                        v_a_1079_,
                        v_a_1080_,
                        v_a_1081_,
                    );
                    if leanh::lean_obj_tag(v___x_1097_) == 0 {
                        leanh::lean_dec_ref_known(v___x_1097_, 1);
                        v_code_1074_ = v_k_1096_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_k_1096_);
                        return v___x_1097_;
                    }
                }
                3 => {
                    v_fvarId_1099_ = leanh::lean_ctor_get(v_code_1074_, 0);
                    leanh::lean_inc(v_fvarId_1099_);
                    v_args_1100_ = leanh::lean_ctor_get(v_code_1074_, 1);
                    leanh::lean_inc_ref(v_args_1100_);
                    leanh::lean_dec_ref_known(v_code_1074_, 2);
                    v___x_1101_ =
                        l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_fvarId_1099_, v_a_1076_);
                    if leanh::lean_obj_tag(v___x_1101_) == 0 {
                        v_isSharedCheck_1122_ =
                            (!leanh::lean_is_exclusive(v___x_1101_)) as u8;
                        if v_isSharedCheck_1122_ == 0 {
                            v_unused_1123_ = leanh::lean_ctor_get(v___x_1101_, 0);
                            leanh::lean_dec(v_unused_1123_);
                            v___x_1103_ = v___x_1101_;
                            v_isShared_1104_ = v_isSharedCheck_1122_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_1101_);
                            v___x_1103_ = leanh::lean_box(0);
                            v_isShared_1104_ = v_isSharedCheck_1122_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_args_1100_);
                        return v___x_1101_;
                    }
                }
                4 => {
                    v_cases_1124_ = leanh::lean_ctor_get(v_code_1074_, 0);
                    leanh::lean_inc_ref(v_cases_1124_);
                    leanh::lean_dec_ref_known(v_code_1074_, 1);
                    v_discr_1125_ = leanh::lean_ctor_get(v_cases_1124_, 2);
                    leanh::lean_inc(v_discr_1125_);
                    v_alts_1126_ = leanh::lean_ctor_get(v_cases_1124_, 3);
                    leanh::lean_inc_ref(v_alts_1126_);
                    leanh::lean_dec_ref(v_cases_1124_);
                    v___x_1127_ =
                        l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_discr_1125_, v_a_1076_);
                    if leanh::lean_obj_tag(v___x_1127_) == 0 {
                        v_isSharedCheck_1148_ =
                            (!leanh::lean_is_exclusive(v___x_1127_)) as u8;
                        if v_isSharedCheck_1148_ == 0 {
                            v_unused_1149_ = leanh::lean_ctor_get(v___x_1127_, 0);
                            leanh::lean_dec(v_unused_1149_);
                            v___x_1129_ = v___x_1127_;
                            v_isShared_1130_ = v_isSharedCheck_1148_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_1127_);
                            v___x_1129_ = leanh::lean_box(0);
                            v_isShared_1130_ = v_isSharedCheck_1148_;
                            state = 5;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_alts_1126_);
                        return v___x_1127_;
                    }
                }
                5 => {
                    v_fvarId_1150_ = leanh::lean_ctor_get(v_code_1074_, 0);
                    leanh::lean_inc(v_fvarId_1150_);
                    leanh::lean_dec_ref_known(v_code_1074_, 1);
                    v___x_1151_ =
                        l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_fvarId_1150_, v_a_1076_);
                    return v___x_1151_;
                }
                6 => {
                    v_isSharedCheck_1159_ = (!leanh::lean_is_exclusive(v_code_1074_)) as u8;
                    if v_isSharedCheck_1159_ == 0 {
                        v_unused_1160_ = leanh::lean_ctor_get(v_code_1074_, 0);
                        leanh::lean_dec(v_unused_1160_);
                        v___x_1153_ = v_code_1074_;
                        v_isShared_1154_ = v_isSharedCheck_1159_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_dec(v_code_1074_);
                        v___x_1153_ = leanh::lean_box(0);
                        v_isShared_1154_ = v_isSharedCheck_1159_;
                        state = 8;
                        continue;
                    }
                }
                _ => {
                    v_decl_1161_ = leanh::lean_ctor_get(v_code_1074_, 0);
                    leanh::lean_inc_ref(v_decl_1161_);
                    v_k_1162_ = leanh::lean_ctor_get(v_code_1074_, 1);
                    leanh::lean_inc_ref(v_k_1162_);
                    leanh::lean_dec_ref(v_code_1074_);
                    v_decl_1084_ = v_decl_1161_;
                    v_k_1085_ = v_k_1162_;
                    v___y_1086_ = v_a_1075_;
                    v___y_1087_ = v_a_1076_;
                    v___y_1088_ = v_a_1077_;
                    v___y_1089_ = v_a_1078_;
                    v___y_1090_ = v_a_1079_;
                    v___y_1091_ = v_a_1080_;
                    v___y_1092_ = v_a_1081_;
                    state = 1;
                    continue;
                }
            },
            1 => {
                v___x_1093_ = l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(
                    v_decl_1084_,
                    v___y_1086_,
                    v___y_1087_,
                    v___y_1088_,
                    v___y_1089_,
                    v___y_1090_,
                    v___y_1091_,
                    v___y_1092_,
                );
                if leanh::lean_obj_tag(v___x_1093_) == 0 {
                    leanh::lean_dec_ref_known(v___x_1093_, 1);
                    v_code_1074_ = v_k_1085_;
                    v_a_1075_ = v___y_1086_;
                    v_a_1076_ = v___y_1087_;
                    v_a_1077_ = v___y_1088_;
                    v_a_1078_ = v___y_1089_;
                    v_a_1079_ = v___y_1090_;
                    v_a_1080_ = v___y_1091_;
                    v_a_1081_ = v___y_1092_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_k_1085_);
                    return v___x_1093_;
                }
            }
            2 => {
                v___x_1105_ = leanh::lean_unsigned_to_nat(0);
                v___x_1106_ = lean_array_get_size(v_args_1100_);
                v___x_1107_ = leanh::lean_box(0);
                v___x_1108_ = lean_nat_dec_lt(v___x_1105_, v___x_1106_);
                if v___x_1108_ == 0 {
                    leanh::lean_dec_ref(v_args_1100_);
                    if v_isShared_1104_ == 0 {
                        leanh::lean_ctor_set(v___x_1103_, 0, v___x_1107_);
                        v___x_1110_ = v___x_1103_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1111_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1111_, 0, v___x_1107_);
                        v___x_1110_ = v_reuseFailAlloc_1111_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___x_1112_ = lean_nat_dec_le(v___x_1106_, v___x_1106_);
                    if v___x_1112_ == 0 {
                        if v___x_1108_ == 0 {
                            leanh::lean_dec_ref(v_args_1100_);
                            if v_isShared_1104_ == 0 {
                                leanh::lean_ctor_set(v___x_1103_, 0, v___x_1107_);
                                v___x_1114_ = v___x_1103_;
                                state = 4;
                                continue;
                            } else {
                                v_reuseFailAlloc_1115_ =
                                    leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_1115_, 0, v___x_1107_);
                                v___x_1114_ = v_reuseFailAlloc_1115_;
                                state = 4;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_1103_);
                            v___x_1116_ = 0usize;
                            v___x_1117_ = lean_usize_of_nat(v___x_1106_);
                            v___x_1118_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___redArg(v_args_1100_, v___x_1116_, v___x_1117_, v___x_1107_, v_a_1076_);
                            leanh::lean_dec_ref(v_args_1100_);
                            return v___x_1118_;
                        }
                    } else {
                        leanh::lean_del_object(v___x_1103_);
                        v___x_1119_ = 0usize;
                        v___x_1120_ = lean_usize_of_nat(v___x_1106_);
                        v___x_1121_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___redArg(v_args_1100_, v___x_1119_, v___x_1120_, v___x_1107_, v_a_1076_);
                        leanh::lean_dec_ref(v_args_1100_);
                        return v___x_1121_;
                    }
                }
            }
            3 => {
                return v___x_1110_;
            }
            4 => {
                return v___x_1114_;
            }
            5 => {
                v___x_1131_ = leanh::lean_unsigned_to_nat(0);
                v___x_1132_ = lean_array_get_size(v_alts_1126_);
                v___x_1133_ = leanh::lean_box(0);
                v___x_1134_ = lean_nat_dec_lt(v___x_1131_, v___x_1132_);
                if v___x_1134_ == 0 {
                    leanh::lean_dec_ref(v_alts_1126_);
                    if v_isShared_1130_ == 0 {
                        leanh::lean_ctor_set(v___x_1129_, 0, v___x_1133_);
                        v___x_1136_ = v___x_1129_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1137_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1137_, 0, v___x_1133_);
                        v___x_1136_ = v_reuseFailAlloc_1137_;
                        state = 6;
                        continue;
                    }
                } else {
                    v___x_1138_ = lean_nat_dec_le(v___x_1132_, v___x_1132_);
                    if v___x_1138_ == 0 {
                        if v___x_1134_ == 0 {
                            leanh::lean_dec_ref(v_alts_1126_);
                            if v_isShared_1130_ == 0 {
                                leanh::lean_ctor_set(v___x_1129_, 0, v___x_1133_);
                                v___x_1140_ = v___x_1129_;
                                state = 7;
                                continue;
                            } else {
                                v_reuseFailAlloc_1141_ =
                                    leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_1141_, 0, v___x_1133_);
                                v___x_1140_ = v_reuseFailAlloc_1141_;
                                state = 7;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_1129_);
                            v___x_1142_ = 0usize;
                            v___x_1143_ = lean_usize_of_nat(v___x_1132_);
                            v___x_1144_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedCode_spec__0(v_alts_1126_, v___x_1142_, v___x_1143_, v___x_1133_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_);
                            leanh::lean_dec_ref(v_alts_1126_);
                            return v___x_1144_;
                        }
                    } else {
                        leanh::lean_del_object(v___x_1129_);
                        v___x_1145_ = 0usize;
                        v___x_1146_ = lean_usize_of_nat(v___x_1132_);
                        v___x_1147_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedCode_spec__0(v_alts_1126_, v___x_1145_, v___x_1146_, v___x_1133_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_);
                        leanh::lean_dec_ref(v_alts_1126_);
                        return v___x_1147_;
                    }
                }
            }
            6 => {
                return v___x_1136_;
            }
            7 => {
                return v___x_1140_;
            }
            8 => {
                v___x_1155_ = leanh::lean_box(0);
                if v_isShared_1154_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1153_, 0);
                    leanh::lean_ctor_set(v___x_1153_, 0, v___x_1155_);
                    v___x_1157_ = v___x_1153_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1158_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1158_, 0, v___x_1155_);
                    v___x_1157_ = v_reuseFailAlloc_1158_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1157_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(
    mut v_funDecl_1163_: *mut leanh::LeanObject,
    mut v_a_1164_: *mut leanh::LeanObject,
    mut v_a_1165_: *mut leanh::LeanObject,
    mut v_a_1166_: *mut leanh::LeanObject,
    mut v_a_1167_: *mut leanh::LeanObject,
    mut v_a_1168_: *mut leanh::LeanObject,
    mut v_a_1169_: *mut leanh::LeanObject,
    mut v_a_1170_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_value_1172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_value_1172_ = leanh::lean_ctor_get(v_funDecl_1163_, 4);
    leanh::lean_inc_ref(v_value_1172_);
    leanh::lean_dec_ref(v_funDecl_1163_);
    v___x_1173_ = l_Lean_Compiler_LCNF_Simp_markUsedCode(
        v_value_1172_,
        v_a_1164_,
        v_a_1165_,
        v_a_1166_,
        v_a_1167_,
        v_a_1168_,
        v_a_1169_,
        v_a_1170_,
    );
    return v___x_1173_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_markUsedFunDecl___boxed(
    mut v_funDecl_1174_: *mut leanh::LeanObject,
    mut v_a_1175_: *mut leanh::LeanObject,
    mut v_a_1176_: *mut leanh::LeanObject,
    mut v_a_1177_: *mut leanh::LeanObject,
    mut v_a_1178_: *mut leanh::LeanObject,
    mut v_a_1179_: *mut leanh::LeanObject,
    mut v_a_1180_: *mut leanh::LeanObject,
    mut v_a_1181_: *mut leanh::LeanObject,
    mut v_a_1182_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1183_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1183_ = l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(
        v_funDecl_1174_,
        v_a_1175_,
        v_a_1176_,
        v_a_1177_,
        v_a_1178_,
        v_a_1179_,
        v_a_1180_,
        v_a_1181_,
    );
    leanh::lean_dec(v_a_1181_);
    leanh::lean_dec_ref(v_a_1180_);
    leanh::lean_dec(v_a_1179_);
    leanh::lean_dec_ref(v_a_1178_);
    leanh::lean_dec_ref(v_a_1177_);
    leanh::lean_dec(v_a_1176_);
    leanh::lean_dec_ref(v_a_1175_);
    return v_res_1183_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedCode_spec__0___boxed(
    mut v_as_1184_: *mut leanh::LeanObject,
    mut v_i_1185_: *mut leanh::LeanObject,
    mut v_stop_1186_: *mut leanh::LeanObject,
    mut v_b_1187_: *mut leanh::LeanObject,
    mut v___y_1188_: *mut leanh::LeanObject,
    mut v___y_1189_: *mut leanh::LeanObject,
    mut v___y_1190_: *mut leanh::LeanObject,
    mut v___y_1191_: *mut leanh::LeanObject,
    mut v___y_1192_: *mut leanh::LeanObject,
    mut v___y_1193_: *mut leanh::LeanObject,
    mut v___y_1194_: *mut leanh::LeanObject,
    mut v___y_1195_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1196_: usize = 0;
    let mut v_stop_boxed_1197_: usize = 0;
    let mut v_res_1198_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1196_ = leanh::lean_unbox_usize(v_i_1185_);
    leanh::lean_dec(v_i_1185_);
    v_stop_boxed_1197_ = leanh::lean_unbox_usize(v_stop_1186_);
    leanh::lean_dec(v_stop_1186_);
    v_res_1198_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedCode_spec__0(v_as_1184_, v_i_boxed_1196_, v_stop_boxed_1197_, v_b_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_);
    leanh::lean_dec(v___y_1194_);
    leanh::lean_dec_ref(v___y_1193_);
    leanh::lean_dec(v___y_1192_);
    leanh::lean_dec_ref(v___y_1191_);
    leanh::lean_dec_ref(v___y_1190_);
    leanh::lean_dec(v___y_1189_);
    leanh::lean_dec_ref(v___y_1188_);
    leanh::lean_dec_ref(v_as_1184_);
    return v_res_1198_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_markUsedCode___boxed(
    mut v_code_1199_: *mut leanh::LeanObject,
    mut v_a_1200_: *mut leanh::LeanObject,
    mut v_a_1201_: *mut leanh::LeanObject,
    mut v_a_1202_: *mut leanh::LeanObject,
    mut v_a_1203_: *mut leanh::LeanObject,
    mut v_a_1204_: *mut leanh::LeanObject,
    mut v_a_1205_: *mut leanh::LeanObject,
    mut v_a_1206_: *mut leanh::LeanObject,
    mut v_a_1207_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1208_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1208_ = l_Lean_Compiler_LCNF_Simp_markUsedCode(
        v_code_1199_,
        v_a_1200_,
        v_a_1201_,
        v_a_1202_,
        v_a_1203_,
        v_a_1204_,
        v_a_1205_,
        v_a_1206_,
    );
    leanh::lean_dec(v_a_1206_);
    leanh::lean_dec_ref(v_a_1205_);
    leanh::lean_dec(v_a_1204_);
    leanh::lean_dec_ref(v_a_1203_);
    leanh::lean_dec_ref(v_a_1202_);
    leanh::lean_dec(v_a_1201_);
    leanh::lean_dec_ref(v_a_1200_);
    return v_res_1208_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Simp_isUsed_spec__0___redArg(
    mut v_m_1209_: *mut leanh::LeanObject,
    mut v_a_1210_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_buckets_1211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1213_: u64 = 0;
    let mut v___x_1214_: u64 = 0;
    let mut v___x_1215_: u64 = 0;
    let mut v_fold_1216_: u64 = 0;
    let mut v___x_1217_: u64 = 0;
    let mut v___x_1218_: u64 = 0;
    let mut v___x_1219_: u64 = 0;
    let mut v___x_1220_: usize = 0;
    let mut v___x_1221_: usize = 0;
    let mut v___x_1222_: usize = 0;
    let mut v___x_1223_: usize = 0;
    let mut v___x_1224_: usize = 0;
    let mut v___x_1225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: u8 = 0;
    v_buckets_1211_ = leanh::lean_ctor_get(v_m_1209_, 1);
    v___x_1212_ = lean_array_get_size(v_buckets_1211_);
    v___x_1213_ = l_Lean_instHashableFVarId_hash(v_a_1210_);
    v___x_1214_ = 32u64;
    v___x_1215_ = lean_uint64_shift_right(v___x_1213_, v___x_1214_);
    v_fold_1216_ = lean_uint64_xor(v___x_1213_, v___x_1215_);
    v___x_1217_ = 16u64;
    v___x_1218_ = lean_uint64_shift_right(v_fold_1216_, v___x_1217_);
    v___x_1219_ = lean_uint64_xor(v_fold_1216_, v___x_1218_);
    v___x_1220_ = lean_uint64_to_usize(v___x_1219_);
    v___x_1221_ = lean_usize_of_nat(v___x_1212_);
    v___x_1222_ = 1usize;
    v___x_1223_ = lean_usize_sub(v___x_1221_, v___x_1222_);
    v___x_1224_ = lean_usize_land(v___x_1220_, v___x_1223_);
    v___x_1225_ = lean_array_uget_borrowed(v_buckets_1211_, v___x_1224_);
    v___x_1226_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0_spec__0___redArg(v_a_1210_, v___x_1225_);
    return v___x_1226_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Simp_isUsed_spec__0___redArg___boxed(
    mut v_m_1227_: *mut leanh::LeanObject,
    mut v_a_1228_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1229_: u8 = 0;
    let mut v_r_1230_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1229_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Simp_isUsed_spec__0___redArg(v_m_1227_, v_a_1228_);
    leanh::lean_dec(v_a_1228_);
    leanh::lean_dec_ref(v_m_1227_);
    v_r_1230_ = leanh::lean_box((v_res_1229_) as usize);
    return v_r_1230_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_isUsed___redArg(
    mut v_fvarId_1231_: *mut leanh::LeanObject,
    mut v_a_1232_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_used_1235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: u8 = 0;
    let mut v___x_1237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1238_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1234_ = lean_st_ref_get(v_a_1232_);
    v_used_1235_ = leanh::lean_ctor_get(v___x_1234_, 1);
    leanh::lean_inc_ref(v_used_1235_);
    leanh::lean_dec(v___x_1234_);
    v___x_1236_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Simp_isUsed_spec__0___redArg(v_used_1235_, v_fvarId_1231_);
    leanh::lean_dec_ref(v_used_1235_);
    v___x_1237_ = leanh::lean_box((v___x_1236_) as usize);
    v___x_1238_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1238_, 0, v___x_1237_);
    return v___x_1238_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_isUsed___redArg___boxed(
    mut v_fvarId_1239_: *mut leanh::LeanObject,
    mut v_a_1240_: *mut leanh::LeanObject,
    mut v_a_1241_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1242_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1242_ = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(v_fvarId_1239_, v_a_1240_);
    leanh::lean_dec(v_a_1240_);
    leanh::lean_dec(v_fvarId_1239_);
    return v_res_1242_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_isUsed(
    mut v_fvarId_1243_: *mut leanh::LeanObject,
    mut v_a_1244_: *mut leanh::LeanObject,
    mut v_a_1245_: *mut leanh::LeanObject,
    mut v_a_1246_: *mut leanh::LeanObject,
    mut v_a_1247_: *mut leanh::LeanObject,
    mut v_a_1248_: *mut leanh::LeanObject,
    mut v_a_1249_: *mut leanh::LeanObject,
    mut v_a_1250_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1252_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1252_ = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(v_fvarId_1243_, v_a_1245_);
    return v___x_1252_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_isUsed___boxed(
    mut v_fvarId_1253_: *mut leanh::LeanObject,
    mut v_a_1254_: *mut leanh::LeanObject,
    mut v_a_1255_: *mut leanh::LeanObject,
    mut v_a_1256_: *mut leanh::LeanObject,
    mut v_a_1257_: *mut leanh::LeanObject,
    mut v_a_1258_: *mut leanh::LeanObject,
    mut v_a_1259_: *mut leanh::LeanObject,
    mut v_a_1260_: *mut leanh::LeanObject,
    mut v_a_1261_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1262_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1262_ = l_Lean_Compiler_LCNF_Simp_isUsed(
        v_fvarId_1253_,
        v_a_1254_,
        v_a_1255_,
        v_a_1256_,
        v_a_1257_,
        v_a_1258_,
        v_a_1259_,
        v_a_1260_,
    );
    leanh::lean_dec(v_a_1260_);
    leanh::lean_dec_ref(v_a_1259_);
    leanh::lean_dec(v_a_1258_);
    leanh::lean_dec_ref(v_a_1257_);
    leanh::lean_dec_ref(v_a_1256_);
    leanh::lean_dec(v_a_1255_);
    leanh::lean_dec_ref(v_a_1254_);
    leanh::lean_dec(v_fvarId_1253_);
    return v_res_1262_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Simp_isUsed_spec__0(
    mut v_00_u03b2_1263_: *mut leanh::LeanObject,
    mut v_m_1264_: *mut leanh::LeanObject,
    mut v_a_1265_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1266_: u8 = 0;
    v___x_1266_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Simp_isUsed_spec__0___redArg(v_m_1264_, v_a_1265_);
    return v___x_1266_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Simp_isUsed_spec__0___boxed(
    mut v_00_u03b2_1267_: *mut leanh::LeanObject,
    mut v_m_1268_: *mut leanh::LeanObject,
    mut v_a_1269_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1270_: u8 = 0;
    let mut v_r_1271_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1270_ =
        l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Simp_isUsed_spec__0(
            v_00_u03b2_1267_,
            v_m_1268_,
            v_a_1269_,
        );
    leanh::lean_dec(v_a_1269_);
    leanh::lean_dec_ref(v_m_1268_);
    v_r_1271_ = leanh::lean_box((v_res_1270_) as usize);
    return v_r_1271_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1272_: u8 = 0;
    let mut v___x_1273_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1272_ = 0;
    v___x_1273_ = l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default(v___x_1272_);
    return v___x_1273_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go(
    mut v_decls_1274_: *mut leanh::LeanObject,
    mut v_i_1275_: *mut leanh::LeanObject,
    mut v_code_1276_: *mut leanh::LeanObject,
    mut v_a_1277_: *mut leanh::LeanObject,
    mut v_a_1278_: *mut leanh::LeanObject,
    mut v_a_1279_: *mut leanh::LeanObject,
    mut v_a_1280_: *mut leanh::LeanObject,
    mut v_a_1281_: *mut leanh::LeanObject,
    mut v_a_1282_: *mut leanh::LeanObject,
    mut v_a_1283_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1286_: u8 = 0;
    let mut v___x_1287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: u8 = 0;
    let mut v___x_1289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_1292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: u8 = 0;
    let mut v___x_1297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1302_: u8 = 0;
    let mut v___x_1304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1306_: u8 = 0;
    let mut v_decl_1307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1314_: u8 = 0;
    let mut v___x_1316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1318_: u8 = 0;
    let mut v_decl_1319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1326_: u8 = 0;
    let mut v___x_1328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1330_: u8 = 0;
    let mut v_decl_1331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1338_: u8 = 0;
    let mut v___x_1340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1342_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1285_ = leanh::lean_unsigned_to_nat(0);
                v___x_1286_ = lean_nat_dec_lt(v___x_1285_, v_i_1275_);
                if v___x_1286_ == 0 {
                    leanh::lean_dec(v_i_1275_);
                    v___x_1287_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1287_, 0, v_code_1276_);
                    return v___x_1287_;
                } else {
                    v___x_1288_ = 0;
                    v___x_1289_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__0_once), _init_l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__0);
                    v___x_1290_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1291_ = lean_nat_sub(v_i_1275_, v___x_1290_);
                    leanh::lean_dec(v_i_1275_);
                    v_decl_1292_ = lean_array_get_borrowed(v___x_1289_, v_decls_1274_, v___x_1291_);
                    v___x_1293_ = l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg(v_decl_1292_);
                    v___x_1294_ = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(v___x_1293_, v_a_1278_);
                    leanh::lean_dec(v___x_1293_);
                    v_a_1295_ = leanh::lean_ctor_get(v___x_1294_, 0);
                    leanh::lean_inc(v_a_1295_);
                    leanh::lean_dec_ref(v___x_1294_);
                    v___x_1296_ = (leanh::lean_unbox(v_a_1295_) as u8);
                    leanh::lean_dec(v_a_1295_);
                    if v___x_1296_ == 0 {
                        v___x_1297_ = l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(
                            v___x_1288_,
                            v_decl_1292_,
                            v_a_1281_,
                        );
                        if leanh::lean_obj_tag(v___x_1297_) == 0 {
                            leanh::lean_dec_ref_known(v___x_1297_, 1);
                            v_i_1275_ = v___x_1291_;
                            state = 0;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_1291_);
                            leanh::lean_dec_ref(v_code_1276_);
                            v_a_1299_ = leanh::lean_ctor_get(v___x_1297_, 0);
                            v_isSharedCheck_1306_ =
                                (!leanh::lean_is_exclusive(v___x_1297_)) as u8;
                            if v_isSharedCheck_1306_ == 0 {
                                v___x_1301_ = v___x_1297_;
                                v_isShared_1302_ = v_isSharedCheck_1306_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1299_);
                                leanh::lean_dec(v___x_1297_);
                                v___x_1301_ = leanh::lean_box(0);
                                v_isShared_1302_ = v_isSharedCheck_1306_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        match leanh::lean_obj_tag(v_decl_1292_) {
                            0 => {
                                v_decl_1307_ = leanh::lean_ctor_get(v_decl_1292_, 0);
                                leanh::lean_inc_ref(v_decl_1307_);
                                v___x_1308_ = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(
                                    v_decl_1307_,
                                    v_a_1277_,
                                    v_a_1278_,
                                    v_a_1279_,
                                    v_a_1280_,
                                    v_a_1281_,
                                    v_a_1282_,
                                    v_a_1283_,
                                );
                                if leanh::lean_obj_tag(v___x_1308_) == 0 {
                                    leanh::lean_dec_ref_known(v___x_1308_, 1);
                                    leanh::lean_inc_ref(v_decl_1307_);
                                    v___x_1309_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_1309_, 0, v_decl_1307_);
                                    leanh::lean_ctor_set(v___x_1309_, 1, v_code_1276_);
                                    v_i_1275_ = v___x_1291_;
                                    v_code_1276_ = v___x_1309_;
                                    state = 0;
                                    continue;
                                } else {
                                    leanh::lean_dec(v___x_1291_);
                                    leanh::lean_dec_ref(v_code_1276_);
                                    v_a_1311_ = leanh::lean_ctor_get(v___x_1308_, 0);
                                    v_isSharedCheck_1318_ =
                                        (!leanh::lean_is_exclusive(v___x_1308_)) as u8;
                                    if v_isSharedCheck_1318_ == 0 {
                                        v___x_1313_ = v___x_1308_;
                                        v_isShared_1314_ = v_isSharedCheck_1318_;
                                        state = 3;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_1311_);
                                        leanh::lean_dec(v___x_1308_);
                                        v___x_1313_ = leanh::lean_box(0);
                                        v_isShared_1314_ = v_isSharedCheck_1318_;
                                        state = 3;
                                        continue;
                                    }
                                }
                            }
                            1 => {
                                v_decl_1319_ = leanh::lean_ctor_get(v_decl_1292_, 0);
                                leanh::lean_inc_ref(v_decl_1319_);
                                v___x_1320_ = l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(
                                    v_decl_1319_,
                                    v_a_1277_,
                                    v_a_1278_,
                                    v_a_1279_,
                                    v_a_1280_,
                                    v_a_1281_,
                                    v_a_1282_,
                                    v_a_1283_,
                                );
                                if leanh::lean_obj_tag(v___x_1320_) == 0 {
                                    leanh::lean_dec_ref_known(v___x_1320_, 1);
                                    leanh::lean_inc_ref(v_decl_1319_);
                                    v___x_1321_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_1321_, 0, v_decl_1319_);
                                    leanh::lean_ctor_set(v___x_1321_, 1, v_code_1276_);
                                    v_i_1275_ = v___x_1291_;
                                    v_code_1276_ = v___x_1321_;
                                    state = 0;
                                    continue;
                                } else {
                                    leanh::lean_dec(v___x_1291_);
                                    leanh::lean_dec_ref(v_code_1276_);
                                    v_a_1323_ = leanh::lean_ctor_get(v___x_1320_, 0);
                                    v_isSharedCheck_1330_ =
                                        (!leanh::lean_is_exclusive(v___x_1320_)) as u8;
                                    if v_isSharedCheck_1330_ == 0 {
                                        v___x_1325_ = v___x_1320_;
                                        v_isShared_1326_ = v_isSharedCheck_1330_;
                                        state = 5;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_1323_);
                                        leanh::lean_dec(v___x_1320_);
                                        v___x_1325_ = leanh::lean_box(0);
                                        v_isShared_1326_ = v_isSharedCheck_1330_;
                                        state = 5;
                                        continue;
                                    }
                                }
                            }
                            _ => {
                                v_decl_1331_ = leanh::lean_ctor_get(v_decl_1292_, 0);
                                leanh::lean_inc_ref(v_decl_1331_);
                                v___x_1332_ = l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(
                                    v_decl_1331_,
                                    v_a_1277_,
                                    v_a_1278_,
                                    v_a_1279_,
                                    v_a_1280_,
                                    v_a_1281_,
                                    v_a_1282_,
                                    v_a_1283_,
                                );
                                if leanh::lean_obj_tag(v___x_1332_) == 0 {
                                    leanh::lean_dec_ref_known(v___x_1332_, 1);
                                    leanh::lean_inc_ref(v_decl_1331_);
                                    v___x_1333_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_1333_, 0, v_decl_1331_);
                                    leanh::lean_ctor_set(v___x_1333_, 1, v_code_1276_);
                                    v_i_1275_ = v___x_1291_;
                                    v_code_1276_ = v___x_1333_;
                                    state = 0;
                                    continue;
                                } else {
                                    leanh::lean_dec(v___x_1291_);
                                    leanh::lean_dec_ref(v_code_1276_);
                                    v_a_1335_ = leanh::lean_ctor_get(v___x_1332_, 0);
                                    v_isSharedCheck_1342_ =
                                        (!leanh::lean_is_exclusive(v___x_1332_)) as u8;
                                    if v_isSharedCheck_1342_ == 0 {
                                        v___x_1337_ = v___x_1332_;
                                        v_isShared_1338_ = v_isSharedCheck_1342_;
                                        state = 7;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_1335_);
                                        leanh::lean_dec(v___x_1332_);
                                        v___x_1337_ = leanh::lean_box(0);
                                        v_isShared_1338_ = v_isSharedCheck_1342_;
                                        state = 7;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1302_ == 0 {
                    v___x_1304_ = v___x_1301_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1305_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1305_, 0, v_a_1299_);
                    v___x_1304_ = v_reuseFailAlloc_1305_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1304_;
            }
            3 => {
                if v_isShared_1314_ == 0 {
                    v___x_1316_ = v___x_1313_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1317_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1317_, 0, v_a_1311_);
                    v___x_1316_ = v_reuseFailAlloc_1317_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1316_;
            }
            5 => {
                if v_isShared_1326_ == 0 {
                    v___x_1328_ = v___x_1325_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1329_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1329_, 0, v_a_1323_);
                    v___x_1328_ = v_reuseFailAlloc_1329_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1328_;
            }
            7 => {
                if v_isShared_1338_ == 0 {
                    v___x_1340_ = v___x_1337_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1341_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1341_, 0, v_a_1335_);
                    v___x_1340_ = v_reuseFailAlloc_1341_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1340_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go___boxed(
    mut v_decls_1343_: *mut leanh::LeanObject,
    mut v_i_1344_: *mut leanh::LeanObject,
    mut v_code_1345_: *mut leanh::LeanObject,
    mut v_a_1346_: *mut leanh::LeanObject,
    mut v_a_1347_: *mut leanh::LeanObject,
    mut v_a_1348_: *mut leanh::LeanObject,
    mut v_a_1349_: *mut leanh::LeanObject,
    mut v_a_1350_: *mut leanh::LeanObject,
    mut v_a_1351_: *mut leanh::LeanObject,
    mut v_a_1352_: *mut leanh::LeanObject,
    mut v_a_1353_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1354_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1354_ =
        l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go(
            v_decls_1343_,
            v_i_1344_,
            v_code_1345_,
            v_a_1346_,
            v_a_1347_,
            v_a_1348_,
            v_a_1349_,
            v_a_1350_,
            v_a_1351_,
            v_a_1352_,
        );
    leanh::lean_dec(v_a_1352_);
    leanh::lean_dec_ref(v_a_1351_);
    leanh::lean_dec(v_a_1350_);
    leanh::lean_dec_ref(v_a_1349_);
    leanh::lean_dec_ref(v_a_1348_);
    leanh::lean_dec(v_a_1347_);
    leanh::lean_dec_ref(v_a_1346_);
    leanh::lean_dec_ref(v_decls_1343_);
    return v_res_1354_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go_match__1_splitter___redArg(
    mut v_decl_1355_: *mut leanh::LeanObject,
    mut v_h__1_1356_: *mut leanh::LeanObject,
    mut v_h__2_1357_: *mut leanh::LeanObject,
    mut v_h__3_1358_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_decl_1355_) {
        0 => {
            let mut v_decl_1359_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1360_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1358_);
            leanh::lean_dec(v_h__2_1357_);
            v_decl_1359_ = leanh::lean_ctor_get(v_decl_1355_, 0);
            leanh::lean_inc_ref(v_decl_1359_);
            leanh::lean_dec_ref_known(v_decl_1355_, 1);
            v___x_1360_ = leanh::lean_apply_1(v_h__1_1356_, v_decl_1359_);
            return v___x_1360_;
        }
        1 => {
            let mut v_decl_1361_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1362_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1358_);
            leanh::lean_dec(v_h__1_1356_);
            v_decl_1361_ = leanh::lean_ctor_get(v_decl_1355_, 0);
            leanh::lean_inc_ref(v_decl_1361_);
            leanh::lean_dec_ref_known(v_decl_1355_, 1);
            v___x_1362_ = leanh::lean_apply_1(v_h__2_1357_, v_decl_1361_);
            return v___x_1362_;
        }
        _ => {
            let mut v_decl_1363_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1364_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_1357_);
            leanh::lean_dec(v_h__1_1356_);
            v_decl_1363_ = leanh::lean_ctor_get(v_decl_1355_, 0);
            leanh::lean_inc_ref(v_decl_1363_);
            leanh::lean_dec_ref_known(v_decl_1355_, 1);
            v___x_1364_ = leanh::lean_apply_1(v_h__3_1358_, v_decl_1363_);
            return v___x_1364_;
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go_match__1_splitter(
    mut v_motive_1365_: *mut leanh::LeanObject,
    mut v_decl_1366_: *mut leanh::LeanObject,
    mut v_h__1_1367_: *mut leanh::LeanObject,
    mut v_h__2_1368_: *mut leanh::LeanObject,
    mut v_h__3_1369_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_decl_1366_) {
        0 => {
            let mut v_decl_1370_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1369_);
            leanh::lean_dec(v_h__2_1368_);
            v_decl_1370_ = leanh::lean_ctor_get(v_decl_1366_, 0);
            leanh::lean_inc_ref(v_decl_1370_);
            leanh::lean_dec_ref_known(v_decl_1366_, 1);
            v___x_1371_ = leanh::lean_apply_1(v_h__1_1367_, v_decl_1370_);
            return v___x_1371_;
        }
        1 => {
            let mut v_decl_1372_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1373_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1369_);
            leanh::lean_dec(v_h__1_1367_);
            v_decl_1372_ = leanh::lean_ctor_get(v_decl_1366_, 0);
            leanh::lean_inc_ref(v_decl_1372_);
            leanh::lean_dec_ref_known(v_decl_1366_, 1);
            v___x_1373_ = leanh::lean_apply_1(v_h__2_1368_, v_decl_1372_);
            return v___x_1373_;
        }
        _ => {
            let mut v_decl_1374_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1375_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_1368_);
            leanh::lean_dec(v_h__1_1367_);
            v_decl_1374_ = leanh::lean_ctor_get(v_decl_1366_, 0);
            leanh::lean_inc_ref(v_decl_1374_);
            leanh::lean_dec_ref_known(v_decl_1366_, 1);
            v___x_1375_ = leanh::lean_apply_1(v_h__3_1369_, v_decl_1374_);
            return v___x_1375_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_attachCodeDecls(
    mut v_decls_1376_: *mut leanh::LeanObject,
    mut v_code_1377_: *mut leanh::LeanObject,
    mut v_a_1378_: *mut leanh::LeanObject,
    mut v_a_1379_: *mut leanh::LeanObject,
    mut v_a_1380_: *mut leanh::LeanObject,
    mut v_a_1381_: *mut leanh::LeanObject,
    mut v_a_1382_: *mut leanh::LeanObject,
    mut v_a_1383_: *mut leanh::LeanObject,
    mut v_a_1384_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1386_ = lean_array_get_size(v_decls_1376_);
    v___x_1387_ =
        l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go(
            v_decls_1376_,
            v___x_1386_,
            v_code_1377_,
            v_a_1378_,
            v_a_1379_,
            v_a_1380_,
            v_a_1381_,
            v_a_1382_,
            v_a_1383_,
            v_a_1384_,
        );
    return v___x_1387_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_attachCodeDecls___boxed(
    mut v_decls_1388_: *mut leanh::LeanObject,
    mut v_code_1389_: *mut leanh::LeanObject,
    mut v_a_1390_: *mut leanh::LeanObject,
    mut v_a_1391_: *mut leanh::LeanObject,
    mut v_a_1392_: *mut leanh::LeanObject,
    mut v_a_1393_: *mut leanh::LeanObject,
    mut v_a_1394_: *mut leanh::LeanObject,
    mut v_a_1395_: *mut leanh::LeanObject,
    mut v_a_1396_: *mut leanh::LeanObject,
    mut v_a_1397_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1398_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1398_ = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(
        v_decls_1388_,
        v_code_1389_,
        v_a_1390_,
        v_a_1391_,
        v_a_1392_,
        v_a_1393_,
        v_a_1394_,
        v_a_1395_,
        v_a_1396_,
    );
    leanh::lean_dec(v_a_1396_);
    leanh::lean_dec_ref(v_a_1395_);
    leanh::lean_dec(v_a_1394_);
    leanh::lean_dec_ref(v_a_1393_);
    leanh::lean_dec_ref(v_a_1392_);
    leanh::lean_dec(v_a_1391_);
    leanh::lean_dec_ref(v_a_1390_);
    leanh::lean_dec_ref(v_decls_1388_);
    return v_res_1398_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_Simp_Used(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_Simp_SimpM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_Simp_Used(
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
pub unsafe fn initialize_Lean_Compiler_LCNF_Simp_Used(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_Simp_SimpM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Simp_Used(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_Simp_Used(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_Simp_Used(builtin);
}