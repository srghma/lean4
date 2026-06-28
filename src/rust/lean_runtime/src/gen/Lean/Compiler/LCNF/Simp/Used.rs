// Lean compiler output
// Module: Lean.Compiler.LCNF.Simp.Used
// Imports: Lean.Compiler.LCNF.Simp.SimpM Init.Omega
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
    lean_array_fget, lean_array_get_borrowed, lean_array_get_size, lean_nat_add, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_sub, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_apply_1, lean_box, lean_ctor_get,
    lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
static mut l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__0: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0_spec__0___redArg(
    mut v_a_700_: *mut LeanObject,
    mut v_x_701_: *mut LeanObject,
) -> u8 {
    let mut v___x_702_: u8 = 0;
    let mut v_key_703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_705_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_701_) == 0 {
                    v___x_702_ = 0;
                    return v___x_702_;
                } else {
                    v_key_703_ = lean_ctor_get(v_x_701_, 0);
                    v_tail_704_ = lean_ctor_get(v_x_701_, 2);
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
    mut v_a_707_: *mut LeanObject,
    mut v_x_708_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_709_: u8 = 0;
    let mut v_r_710_: *mut LeanObject = core::ptr::null_mut();
    v_res_709_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0_spec__0___redArg(v_a_707_, v_x_708_);
    lean_dec(v_x_708_);
    lean_dec(v_a_707_);
    v_r_710_ = lean_box((v_res_709_) as usize);
    return v_r_710_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0_spec__1_spec__2_spec__3___redArg(
    mut v_x_711_: *mut LeanObject,
    mut v_x_712_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_718_: u8 = 0;
    let mut v___x_719_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_738_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_712_) == 0 {
                    return v_x_711_;
                } else {
                    v_key_713_ = lean_ctor_get(v_x_712_, 0);
                    v_value_714_ = lean_ctor_get(v_x_712_, 1);
                    v_tail_715_ = lean_ctor_get(v_x_712_, 2);
                    v_isSharedCheck_738_ = (!lean_is_exclusive(v_x_712_)) as u8;
                    if v_isSharedCheck_738_ == 0 {
                        v___x_717_ = v_x_712_;
                        v_isShared_718_ = v_isSharedCheck_738_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_715_);
                        lean_inc(v_value_714_);
                        lean_inc(v_key_713_);
                        lean_dec(v_x_712_);
                        v___x_717_ = lean_box(0);
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
                lean_inc(v___x_732_);
                if v_isShared_718_ == 0 {
                    lean_ctor_set(v___x_717_, 2, v___x_732_);
                    v___x_734_ = v___x_717_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_737_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_737_, 0, v_key_713_);
                    lean_ctor_set(v_reuseFailAlloc_737_, 1, v_value_714_);
                    lean_ctor_set(v_reuseFailAlloc_737_, 2, v___x_732_);
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
    mut v_i_739_: *mut LeanObject,
    mut v_source_740_: *mut LeanObject,
    mut v_target_741_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_743_: u8 = 0;
    let mut v_es_744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_749_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_742_ = lean_array_get_size(v_source_740_);
                v___x_743_ = lean_nat_dec_lt(v_i_739_, v___x_742_);
                if v___x_743_ == 0 {
                    lean_dec_ref(v_source_740_);
                    lean_dec(v_i_739_);
                    return v_target_741_;
                } else {
                    v_es_744_ = lean_array_fget(v_source_740_, v_i_739_);
                    v___x_745_ = lean_box(0);
                    v_source_746_ = lean_array_fset(v_source_740_, v_i_739_, v___x_745_);
                    v_target_747_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0_spec__1_spec__2_spec__3___redArg(v_target_741_, v_es_744_);
                    v___x_748_ = lean_unsigned_to_nat(1);
                    v___x_749_ = lean_nat_add(v_i_739_, v___x_748_);
                    lean_dec(v_i_739_);
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
    mut v_data_751_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_758_: *mut LeanObject = core::ptr::null_mut();
    v___x_752_ = lean_array_get_size(v_data_751_);
    v___x_753_ = lean_unsigned_to_nat(2);
    v_nbuckets_754_ = lean_nat_mul(v___x_752_, v___x_753_);
    v___x_755_ = lean_unsigned_to_nat(0);
    v___x_756_ = lean_box(0);
    v___x_757_ = lean_mk_array(v_nbuckets_754_, v___x_756_);
    v___x_758_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0_spec__1_spec__2___redArg(v___x_755_, v_data_751_, v___x_757_);
    return v___x_758_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0___redArg(
    mut v_m_759_: *mut LeanObject,
    mut v_a_760_: *mut LeanObject,
    mut v_b_761_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_764_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_778_: u8 = 0;
    let mut v___x_780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_781_: u8 = 0;
    let mut v___x_782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_791_: u8 = 0;
    let mut v_val_792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_799_: u8 = 0;
    let mut v_unused_800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_801_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_762_ = lean_ctor_get(v_m_759_, 0);
                v_buckets_763_ = lean_ctor_get(v_m_759_, 1);
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
                    lean_inc_ref(v_buckets_763_);
                    lean_inc(v_size_762_);
                    v_isSharedCheck_799_ = (!lean_is_exclusive(v_m_759_)) as u8;
                    if v_isSharedCheck_799_ == 0 {
                        v_unused_800_ = lean_ctor_get(v_m_759_, 1);
                        lean_dec(v_unused_800_);
                        v_unused_801_ = lean_ctor_get(v_m_759_, 0);
                        lean_dec(v_unused_801_);
                        v___x_780_ = v_m_759_;
                        v_isShared_781_ = v_isSharedCheck_799_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_m_759_);
                        v___x_780_ = lean_box(0);
                        v_isShared_781_ = v_isSharedCheck_799_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_b_761_);
                    lean_dec(v_a_760_);
                    return v_m_759_;
                }
            }
            1 => {
                v___x_782_ = lean_unsigned_to_nat(1);
                v_size_x27_783_ = lean_nat_add(v_size_762_, v___x_782_);
                lean_dec(v_size_762_);
                lean_inc(v_bkt_777_);
                v___x_784_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_784_, 0, v_a_760_);
                lean_ctor_set(v___x_784_, 1, v_b_761_);
                lean_ctor_set(v___x_784_, 2, v_bkt_777_);
                v_buckets_x27_785_ = lean_array_uset(v_buckets_763_, v___x_776_, v___x_784_);
                v___x_786_ = lean_unsigned_to_nat(4);
                v___x_787_ = lean_nat_mul(v_size_x27_783_, v___x_786_);
                v___x_788_ = lean_unsigned_to_nat(3);
                v___x_789_ = lean_nat_div(v___x_787_, v___x_788_);
                lean_dec(v___x_787_);
                v___x_790_ = lean_array_get_size(v_buckets_x27_785_);
                v___x_791_ = lean_nat_dec_le(v___x_789_, v___x_790_);
                lean_dec(v___x_789_);
                if v___x_791_ == 0 {
                    v_val_792_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0_spec__1___redArg(v_buckets_x27_785_);
                    if v_isShared_781_ == 0 {
                        lean_ctor_set(v___x_780_, 1, v_val_792_);
                        lean_ctor_set(v___x_780_, 0, v_size_x27_783_);
                        v___x_794_ = v___x_780_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_795_, 0, v_size_x27_783_);
                        lean_ctor_set(v_reuseFailAlloc_795_, 1, v_val_792_);
                        v___x_794_ = v_reuseFailAlloc_795_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_781_ == 0 {
                        lean_ctor_set(v___x_780_, 1, v_buckets_x27_785_);
                        lean_ctor_set(v___x_780_, 0, v_size_x27_783_);
                        v___x_797_ = v___x_780_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_798_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_798_, 0, v_size_x27_783_);
                        lean_ctor_set(v_reuseFailAlloc_798_, 1, v_buckets_x27_785_);
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
    mut v_fvarId_802_: *mut LeanObject,
    mut v_a_803_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subst_806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_used_807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderRenaming_808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_funDeclInfoMap_809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_simplified_810_: u8 = 0;
    let mut v_visited_811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inline_812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inlineLocal_813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_816_: u8 = 0;
    let mut v___x_817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_824_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_805_ = lean_st_ref_take(v_a_803_);
                v_subst_806_ = lean_ctor_get(v___x_805_, 0);
                v_used_807_ = lean_ctor_get(v___x_805_, 1);
                v_binderRenaming_808_ = lean_ctor_get(v___x_805_, 2);
                v_funDeclInfoMap_809_ = lean_ctor_get(v___x_805_, 3);
                v_simplified_810_ = lean_ctor_get_uint8(
                    v___x_805_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                );
                v_visited_811_ = lean_ctor_get(v___x_805_, 4);
                v_inline_812_ = lean_ctor_get(v___x_805_, 5);
                v_inlineLocal_813_ = lean_ctor_get(v___x_805_, 6);
                v_isSharedCheck_824_ = (!lean_is_exclusive(v___x_805_)) as u8;
                if v_isSharedCheck_824_ == 0 {
                    v___x_815_ = v___x_805_;
                    v_isShared_816_ = v_isSharedCheck_824_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_inlineLocal_813_);
                    lean_inc(v_inline_812_);
                    lean_inc(v_visited_811_);
                    lean_inc(v_funDeclInfoMap_809_);
                    lean_inc(v_binderRenaming_808_);
                    lean_inc(v_used_807_);
                    lean_inc(v_subst_806_);
                    lean_dec(v___x_805_);
                    v___x_815_ = lean_box(0);
                    v_isShared_816_ = v_isSharedCheck_824_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_817_ = lean_box(0);
                v___x_818_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0___redArg(v_used_807_, v_fvarId_802_, v___x_817_);
                if v_isShared_816_ == 0 {
                    lean_ctor_set(v___x_815_, 1, v___x_818_);
                    v___x_820_ = v___x_815_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_823_ = lean_alloc_ctor(0, 7, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_823_, 0, v_subst_806_);
                    lean_ctor_set(v_reuseFailAlloc_823_, 1, v___x_818_);
                    lean_ctor_set(v_reuseFailAlloc_823_, 2, v_binderRenaming_808_);
                    lean_ctor_set(v_reuseFailAlloc_823_, 3, v_funDeclInfoMap_809_);
                    lean_ctor_set(v_reuseFailAlloc_823_, 4, v_visited_811_);
                    lean_ctor_set(v_reuseFailAlloc_823_, 5, v_inline_812_);
                    lean_ctor_set(v_reuseFailAlloc_823_, 6, v_inlineLocal_813_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_823_,
                        (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                        v_simplified_810_,
                    );
                    v___x_820_ = v_reuseFailAlloc_823_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_821_ = lean_st_ref_set(v_a_803_, v___x_820_);
                v___x_822_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_822_, 0, v___x_817_);
                return v___x_822_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg___boxed(
    mut v_fvarId_825_: *mut LeanObject,
    mut v_a_826_: *mut LeanObject,
    mut v_a_827_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_828_: *mut LeanObject = core::ptr::null_mut();
    v_res_828_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_fvarId_825_, v_a_826_);
    lean_dec(v_a_826_);
    return v_res_828_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_markUsedFVar(
    mut v_fvarId_829_: *mut LeanObject,
    mut v_a_830_: *mut LeanObject,
    mut v_a_831_: *mut LeanObject,
    mut v_a_832_: *mut LeanObject,
    mut v_a_833_: *mut LeanObject,
    mut v_a_834_: *mut LeanObject,
    mut v_a_835_: *mut LeanObject,
    mut v_a_836_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_838_: *mut LeanObject = core::ptr::null_mut();
    v___x_838_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_fvarId_829_, v_a_831_);
    return v___x_838_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_markUsedFVar___boxed(
    mut v_fvarId_839_: *mut LeanObject,
    mut v_a_840_: *mut LeanObject,
    mut v_a_841_: *mut LeanObject,
    mut v_a_842_: *mut LeanObject,
    mut v_a_843_: *mut LeanObject,
    mut v_a_844_: *mut LeanObject,
    mut v_a_845_: *mut LeanObject,
    mut v_a_846_: *mut LeanObject,
    mut v_a_847_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_848_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_846_);
    lean_dec_ref(v_a_845_);
    lean_dec(v_a_844_);
    lean_dec_ref(v_a_843_);
    lean_dec_ref(v_a_842_);
    lean_dec(v_a_841_);
    lean_dec_ref(v_a_840_);
    return v_res_848_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0(
    mut v_00_u03b2_849_: *mut LeanObject,
    mut v_m_850_: *mut LeanObject,
    mut v_a_851_: *mut LeanObject,
    mut v_b_852_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_853_: *mut LeanObject = core::ptr::null_mut();
    v___x_853_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0___redArg(v_m_850_, v_a_851_, v_b_852_);
    return v___x_853_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0_spec__0(
    mut v_00_u03b2_854_: *mut LeanObject,
    mut v_a_855_: *mut LeanObject,
    mut v_x_856_: *mut LeanObject,
) -> u8 {
    let mut v___x_857_: u8 = 0;
    v___x_857_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0_spec__0___redArg(v_a_855_, v_x_856_);
    return v___x_857_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0_spec__0___boxed(
    mut v_00_u03b2_858_: *mut LeanObject,
    mut v_a_859_: *mut LeanObject,
    mut v_x_860_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_861_: u8 = 0;
    let mut v_r_862_: *mut LeanObject = core::ptr::null_mut();
    v_res_861_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0_spec__0(v_00_u03b2_858_, v_a_859_, v_x_860_);
    lean_dec(v_x_860_);
    lean_dec(v_a_859_);
    v_r_862_ = lean_box((v_res_861_) as usize);
    return v_r_862_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0_spec__1(
    mut v_00_u03b2_863_: *mut LeanObject,
    mut v_data_864_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_865_: *mut LeanObject = core::ptr::null_mut();
    v___x_865_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0_spec__1___redArg(v_data_864_);
    return v___x_865_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0_spec__1_spec__2(
    mut v_00_u03b2_866_: *mut LeanObject,
    mut v_i_867_: *mut LeanObject,
    mut v_source_868_: *mut LeanObject,
    mut v_target_869_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_870_: *mut LeanObject = core::ptr::null_mut();
    v___x_870_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0_spec__1_spec__2___redArg(v_i_867_, v_source_868_, v_target_869_);
    return v___x_870_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0_spec__1_spec__2_spec__3(
    mut v_00_u03b2_871_: *mut LeanObject,
    mut v_x_872_: *mut LeanObject,
    mut v_x_873_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_874_: *mut LeanObject = core::ptr::null_mut();
    v___x_874_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Simp_markUsedFVar_spec__0_spec__1_spec__2_spec__3___redArg(v_x_872_, v_x_873_);
    return v___x_874_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_markUsedArg___redArg(
    mut v_arg_875_: *mut LeanObject,
    mut v_a_876_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_arg_875_) == 1 {
        let mut v_fvarId_878_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_879_: *mut LeanObject = core::ptr::null_mut();
        v_fvarId_878_ = lean_ctor_get(v_arg_875_, 0);
        lean_inc(v_fvarId_878_);
        lean_dec_ref_known(v_arg_875_, 1);
        v___x_879_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_fvarId_878_, v_a_876_);
        return v___x_879_;
    } else {
        let mut v___x_880_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_881_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_arg_875_);
        v___x_880_ = lean_box(0);
        v___x_881_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_881_, 0, v___x_880_);
        return v___x_881_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_markUsedArg___redArg___boxed(
    mut v_arg_882_: *mut LeanObject,
    mut v_a_883_: *mut LeanObject,
    mut v_a_884_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_885_: *mut LeanObject = core::ptr::null_mut();
    v_res_885_ = l_Lean_Compiler_LCNF_Simp_markUsedArg___redArg(v_arg_882_, v_a_883_);
    lean_dec(v_a_883_);
    return v_res_885_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_markUsedArg(
    mut v_arg_886_: *mut LeanObject,
    mut v_a_887_: *mut LeanObject,
    mut v_a_888_: *mut LeanObject,
    mut v_a_889_: *mut LeanObject,
    mut v_a_890_: *mut LeanObject,
    mut v_a_891_: *mut LeanObject,
    mut v_a_892_: *mut LeanObject,
    mut v_a_893_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_895_: *mut LeanObject = core::ptr::null_mut();
    v___x_895_ = l_Lean_Compiler_LCNF_Simp_markUsedArg___redArg(v_arg_886_, v_a_888_);
    return v___x_895_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_markUsedArg___boxed(
    mut v_arg_896_: *mut LeanObject,
    mut v_a_897_: *mut LeanObject,
    mut v_a_898_: *mut LeanObject,
    mut v_a_899_: *mut LeanObject,
    mut v_a_900_: *mut LeanObject,
    mut v_a_901_: *mut LeanObject,
    mut v_a_902_: *mut LeanObject,
    mut v_a_903_: *mut LeanObject,
    mut v_a_904_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_905_: *mut LeanObject = core::ptr::null_mut();
    v_res_905_ = l_Lean_Compiler_LCNF_Simp_markUsedArg(
        v_arg_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_,
    );
    lean_dec(v_a_903_);
    lean_dec_ref(v_a_902_);
    lean_dec(v_a_901_);
    lean_dec_ref(v_a_900_);
    lean_dec_ref(v_a_899_);
    lean_dec(v_a_898_);
    lean_dec_ref(v_a_897_);
    return v_res_905_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___redArg(
    mut v_as_906_: *mut LeanObject,
    mut v_i_907_: usize,
    mut v_stop_908_: usize,
    mut v_b_909_: *mut LeanObject,
    mut v___y_910_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_912_: u8 = 0;
    let mut v___x_913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_916_: usize = 0;
    let mut v___x_917_: usize = 0;
    let mut v___x_919_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_912_ = lean_usize_dec_eq(v_i_907_, v_stop_908_);
                if v___x_912_ == 0 {
                    v___x_913_ = lean_array_uget_borrowed(v_as_906_, v_i_907_);
                    lean_inc(v___x_913_);
                    v___x_914_ =
                        l_Lean_Compiler_LCNF_Simp_markUsedArg___redArg(v___x_913_, v___y_910_);
                    if lean_obj_tag(v___x_914_) == 0 {
                        v_a_915_ = lean_ctor_get(v___x_914_, 0);
                        lean_inc(v_a_915_);
                        lean_dec_ref_known(v___x_914_, 1);
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
                    v___x_919_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_919_, 0, v_b_909_);
                    return v___x_919_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___redArg___boxed(
    mut v_as_920_: *mut LeanObject,
    mut v_i_921_: *mut LeanObject,
    mut v_stop_922_: *mut LeanObject,
    mut v_b_923_: *mut LeanObject,
    mut v___y_924_: *mut LeanObject,
    mut v___y_925_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_926_: usize = 0;
    let mut v_stop_boxed_927_: usize = 0;
    let mut v_res_928_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_926_ = lean_unbox_usize(v_i_921_);
    lean_dec(v_i_921_);
    v_stop_boxed_927_ = lean_unbox_usize(v_stop_922_);
    lean_dec(v_stop_922_);
    v_res_928_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___redArg(v_as_920_, v_i_boxed_926_, v_stop_boxed_927_, v_b_923_, v___y_924_);
    lean_dec(v___y_924_);
    lean_dec_ref(v_as_920_);
    return v_res_928_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_markUsedLetValue(
    mut v_e_929_: *mut LeanObject,
    mut v_a_930_: *mut LeanObject,
    mut v_a_931_: *mut LeanObject,
    mut v_a_932_: *mut LeanObject,
    mut v_a_933_: *mut LeanObject,
    mut v_a_934_: *mut LeanObject,
    mut v_a_935_: *mut LeanObject,
    mut v_a_936_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_940_: u8 = 0;
    let mut v___x_941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_945_: u8 = 0;
    let mut v_unused_946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_struct_949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_955_: u8 = 0;
    let mut v___x_956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_957_: u8 = 0;
    let mut v___x_958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_959_: usize = 0;
    let mut v___x_960_: usize = 0;
    let mut v___x_961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_962_: usize = 0;
    let mut v___x_963_: usize = 0;
    let mut v___x_964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_970_: u8 = 0;
    let mut v___x_971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_974_: u8 = 0;
    let mut v___x_976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_978_: u8 = 0;
    let mut v___x_980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_982_: usize = 0;
    let mut v___x_983_: usize = 0;
    let mut v___x_984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_985_: usize = 0;
    let mut v___x_986_: usize = 0;
    let mut v___x_987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_988_: u8 = 0;
    let mut v_unused_989_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_e_929_) {
                0 => {
                    v_isSharedCheck_945_ = (!lean_is_exclusive(v_e_929_)) as u8;
                    if v_isSharedCheck_945_ == 0 {
                        v_unused_946_ = lean_ctor_get(v_e_929_, 0);
                        lean_dec(v_unused_946_);
                        v___x_939_ = v_e_929_;
                        v_isShared_940_ = v_isSharedCheck_945_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_e_929_);
                        v___x_939_ = lean_box(0);
                        v_isShared_940_ = v_isSharedCheck_945_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v___x_947_ = lean_box(0);
                    v___x_948_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_948_, 0, v___x_947_);
                    return v___x_948_;
                }
                2 => {
                    v_struct_949_ = lean_ctor_get(v_e_929_, 2);
                    lean_inc(v_struct_949_);
                    lean_dec_ref_known(v_e_929_, 3);
                    v___x_950_ =
                        l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_struct_949_, v_a_931_);
                    return v___x_950_;
                }
                3 => {
                    v_args_951_ = lean_ctor_get(v_e_929_, 2);
                    lean_inc_ref(v_args_951_);
                    lean_dec_ref_known(v_e_929_, 3);
                    v___x_952_ = lean_unsigned_to_nat(0);
                    v___x_953_ = lean_array_get_size(v_args_951_);
                    v___x_954_ = lean_box(0);
                    v___x_955_ = lean_nat_dec_lt(v___x_952_, v___x_953_);
                    if v___x_955_ == 0 {
                        lean_dec_ref(v_args_951_);
                        v___x_956_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_956_, 0, v___x_954_);
                        return v___x_956_;
                    } else {
                        v___x_957_ = lean_nat_dec_le(v___x_953_, v___x_953_);
                        if v___x_957_ == 0 {
                            if v___x_955_ == 0 {
                                lean_dec_ref(v_args_951_);
                                v___x_958_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_958_, 0, v___x_954_);
                                return v___x_958_;
                            } else {
                                v___x_959_ = 0usize;
                                v___x_960_ = lean_usize_of_nat(v___x_953_);
                                v___x_961_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___redArg(v_args_951_, v___x_959_, v___x_960_, v___x_954_, v_a_931_);
                                lean_dec_ref(v_args_951_);
                                return v___x_961_;
                            }
                        } else {
                            v___x_962_ = 0usize;
                            v___x_963_ = lean_usize_of_nat(v___x_953_);
                            v___x_964_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___redArg(v_args_951_, v___x_962_, v___x_963_, v___x_954_, v_a_931_);
                            lean_dec_ref(v_args_951_);
                            return v___x_964_;
                        }
                    }
                }
                _ => {
                    v_fvarId_965_ = lean_ctor_get(v_e_929_, 0);
                    lean_inc(v_fvarId_965_);
                    v_args_966_ = lean_ctor_get(v_e_929_, 1);
                    lean_inc_ref(v_args_966_);
                    lean_dec_ref_known(v_e_929_, 2);
                    v___x_967_ =
                        l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_fvarId_965_, v_a_931_);
                    v_isSharedCheck_988_ = (!lean_is_exclusive(v___x_967_)) as u8;
                    if v_isSharedCheck_988_ == 0 {
                        v_unused_989_ = lean_ctor_get(v___x_967_, 0);
                        lean_dec(v_unused_989_);
                        v___x_969_ = v___x_967_;
                        v_isShared_970_ = v_isSharedCheck_988_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v___x_967_);
                        v___x_969_ = lean_box(0);
                        v_isShared_970_ = v_isSharedCheck_988_;
                        state = 3;
                        continue;
                    }
                }
            },
            1 => {
                v___x_941_ = lean_box(0);
                if v_isShared_940_ == 0 {
                    lean_ctor_set(v___x_939_, 0, v___x_941_);
                    v___x_943_ = v___x_939_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_944_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_944_, 0, v___x_941_);
                    v___x_943_ = v_reuseFailAlloc_944_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_943_;
            }
            3 => {
                v___x_971_ = lean_unsigned_to_nat(0);
                v___x_972_ = lean_array_get_size(v_args_966_);
                v___x_973_ = lean_box(0);
                v___x_974_ = lean_nat_dec_lt(v___x_971_, v___x_972_);
                if v___x_974_ == 0 {
                    lean_dec_ref(v_args_966_);
                    if v_isShared_970_ == 0 {
                        lean_ctor_set(v___x_969_, 0, v___x_973_);
                        v___x_976_ = v___x_969_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_977_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_977_, 0, v___x_973_);
                        v___x_976_ = v_reuseFailAlloc_977_;
                        state = 4;
                        continue;
                    }
                } else {
                    v___x_978_ = lean_nat_dec_le(v___x_972_, v___x_972_);
                    if v___x_978_ == 0 {
                        if v___x_974_ == 0 {
                            lean_dec_ref(v_args_966_);
                            if v_isShared_970_ == 0 {
                                lean_ctor_set(v___x_969_, 0, v___x_973_);
                                v___x_980_ = v___x_969_;
                                state = 5;
                                continue;
                            } else {
                                v_reuseFailAlloc_981_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_981_, 0, v___x_973_);
                                v___x_980_ = v_reuseFailAlloc_981_;
                                state = 5;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_969_);
                            v___x_982_ = 0usize;
                            v___x_983_ = lean_usize_of_nat(v___x_972_);
                            v___x_984_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___redArg(v_args_966_, v___x_982_, v___x_983_, v___x_973_, v_a_931_);
                            lean_dec_ref(v_args_966_);
                            return v___x_984_;
                        }
                    } else {
                        lean_del_object(v___x_969_);
                        v___x_985_ = 0usize;
                        v___x_986_ = lean_usize_of_nat(v___x_972_);
                        v___x_987_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___redArg(v_args_966_, v___x_985_, v___x_986_, v___x_973_, v_a_931_);
                        lean_dec_ref(v_args_966_);
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
    mut v_e_990_: *mut LeanObject,
    mut v_a_991_: *mut LeanObject,
    mut v_a_992_: *mut LeanObject,
    mut v_a_993_: *mut LeanObject,
    mut v_a_994_: *mut LeanObject,
    mut v_a_995_: *mut LeanObject,
    mut v_a_996_: *mut LeanObject,
    mut v_a_997_: *mut LeanObject,
    mut v_a_998_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_999_: *mut LeanObject = core::ptr::null_mut();
    v_res_999_ = l_Lean_Compiler_LCNF_Simp_markUsedLetValue(
        v_e_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_, v_a_995_, v_a_996_, v_a_997_,
    );
    lean_dec(v_a_997_);
    lean_dec_ref(v_a_996_);
    lean_dec(v_a_995_);
    lean_dec_ref(v_a_994_);
    lean_dec_ref(v_a_993_);
    lean_dec(v_a_992_);
    lean_dec_ref(v_a_991_);
    return v_res_999_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0(
    mut v_as_1000_: *mut LeanObject,
    mut v_i_1001_: usize,
    mut v_stop_1002_: usize,
    mut v_b_1003_: *mut LeanObject,
    mut v___y_1004_: *mut LeanObject,
    mut v___y_1005_: *mut LeanObject,
    mut v___y_1006_: *mut LeanObject,
    mut v___y_1007_: *mut LeanObject,
    mut v___y_1008_: *mut LeanObject,
    mut v___y_1009_: *mut LeanObject,
    mut v___y_1010_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1012_: *mut LeanObject = core::ptr::null_mut();
    v___x_1012_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___redArg(v_as_1000_, v_i_1001_, v_stop_1002_, v_b_1003_, v___y_1005_);
    return v___x_1012_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___boxed(
    mut v_as_1013_: *mut LeanObject,
    mut v_i_1014_: *mut LeanObject,
    mut v_stop_1015_: *mut LeanObject,
    mut v_b_1016_: *mut LeanObject,
    mut v___y_1017_: *mut LeanObject,
    mut v___y_1018_: *mut LeanObject,
    mut v___y_1019_: *mut LeanObject,
    mut v___y_1020_: *mut LeanObject,
    mut v___y_1021_: *mut LeanObject,
    mut v___y_1022_: *mut LeanObject,
    mut v___y_1023_: *mut LeanObject,
    mut v___y_1024_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1025_: usize = 0;
    let mut v_stop_boxed_1026_: usize = 0;
    let mut v_res_1027_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1025_ = lean_unbox_usize(v_i_1014_);
    lean_dec(v_i_1014_);
    v_stop_boxed_1026_ = lean_unbox_usize(v_stop_1015_);
    lean_dec(v_stop_1015_);
    v_res_1027_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0(v_as_1013_, v_i_boxed_1025_, v_stop_boxed_1026_, v_b_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_);
    lean_dec(v___y_1023_);
    lean_dec_ref(v___y_1022_);
    lean_dec(v___y_1021_);
    lean_dec_ref(v___y_1020_);
    lean_dec_ref(v___y_1019_);
    lean_dec(v___y_1018_);
    lean_dec_ref(v___y_1017_);
    lean_dec_ref(v_as_1013_);
    return v_res_1027_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(
    mut v_letDecl_1028_: *mut LeanObject,
    mut v_a_1029_: *mut LeanObject,
    mut v_a_1030_: *mut LeanObject,
    mut v_a_1031_: *mut LeanObject,
    mut v_a_1032_: *mut LeanObject,
    mut v_a_1033_: *mut LeanObject,
    mut v_a_1034_: *mut LeanObject,
    mut v_a_1035_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_value_1037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: *mut LeanObject = core::ptr::null_mut();
    v_value_1037_ = lean_ctor_get(v_letDecl_1028_, 3);
    lean_inc(v_value_1037_);
    lean_dec_ref(v_letDecl_1028_);
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
    mut v_letDecl_1039_: *mut LeanObject,
    mut v_a_1040_: *mut LeanObject,
    mut v_a_1041_: *mut LeanObject,
    mut v_a_1042_: *mut LeanObject,
    mut v_a_1043_: *mut LeanObject,
    mut v_a_1044_: *mut LeanObject,
    mut v_a_1045_: *mut LeanObject,
    mut v_a_1046_: *mut LeanObject,
    mut v_a_1047_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1048_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_1046_);
    lean_dec_ref(v_a_1045_);
    lean_dec(v_a_1044_);
    lean_dec_ref(v_a_1043_);
    lean_dec_ref(v_a_1042_);
    lean_dec(v_a_1041_);
    lean_dec_ref(v_a_1040_);
    return v_res_1048_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedCode_spec__0(
    mut v_as_1049_: *mut LeanObject,
    mut v_i_1050_: usize,
    mut v_stop_1051_: usize,
    mut v_b_1052_: *mut LeanObject,
    mut v___y_1053_: *mut LeanObject,
    mut v___y_1054_: *mut LeanObject,
    mut v___y_1055_: *mut LeanObject,
    mut v___y_1056_: *mut LeanObject,
    mut v___y_1057_: *mut LeanObject,
    mut v___y_1058_: *mut LeanObject,
    mut v___y_1059_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: usize = 0;
    let mut v___x_1066_: usize = 0;
    let mut v___x_1068_: u8 = 0;
    let mut v___x_1069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_1070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_1071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_1072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1068_ = lean_usize_dec_eq(v_i_1050_, v_stop_1051_);
                if v___x_1068_ == 0 {
                    v___x_1069_ = lean_array_uget_borrowed(v_as_1049_, v_i_1050_);
                    match lean_obj_tag(v___x_1069_) {
                        0 => {
                            v_code_1070_ = lean_ctor_get(v___x_1069_, 2);
                            lean_inc_ref(v_code_1070_);
                            v___y_1062_ = v_code_1070_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v_code_1071_ = lean_ctor_get(v___x_1069_, 1);
                            lean_inc_ref(v_code_1071_);
                            v___y_1062_ = v_code_1071_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v_code_1072_ = lean_ctor_get(v___x_1069_, 0);
                            lean_inc_ref(v_code_1072_);
                            v___y_1062_ = v_code_1072_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v___x_1073_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1073_, 0, v_b_1052_);
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
                if lean_obj_tag(v___x_1063_) == 0 {
                    v_a_1064_ = lean_ctor_get(v___x_1063_, 0);
                    lean_inc(v_a_1064_);
                    lean_dec_ref_known(v___x_1063_, 1);
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
    mut v_code_1074_: *mut LeanObject,
    mut v_a_1075_: *mut LeanObject,
    mut v_a_1076_: *mut LeanObject,
    mut v_a_1077_: *mut LeanObject,
    mut v_a_1078_: *mut LeanObject,
    mut v_a_1079_: *mut LeanObject,
    mut v_a_1080_: *mut LeanObject,
    mut v_a_1081_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_decl_1084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decl_1095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_1100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1104_: u8 = 0;
    let mut v___x_1105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1108_: u8 = 0;
    let mut v___x_1110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1112_: u8 = 0;
    let mut v___x_1114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1116_: usize = 0;
    let mut v___x_1117_: usize = 0;
    let mut v___x_1118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1119_: usize = 0;
    let mut v___x_1120_: usize = 0;
    let mut v___x_1121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1122_: u8 = 0;
    let mut v_unused_1123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cases_1124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_discr_1125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_alts_1126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1130_: u8 = 0;
    let mut v___x_1131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: u8 = 0;
    let mut v___x_1136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: u8 = 0;
    let mut v___x_1140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: usize = 0;
    let mut v___x_1143_: usize = 0;
    let mut v___x_1144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: usize = 0;
    let mut v___x_1146_: usize = 0;
    let mut v___x_1147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1148_: u8 = 0;
    let mut v_unused_1149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1154_: u8 = 0;
    let mut v___x_1155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1159_: u8 = 0;
    let mut v_unused_1160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decl_1161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1162_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_code_1074_) {
                0 => {
                    v_decl_1095_ = lean_ctor_get(v_code_1074_, 0);
                    lean_inc_ref(v_decl_1095_);
                    v_k_1096_ = lean_ctor_get(v_code_1074_, 1);
                    lean_inc_ref(v_k_1096_);
                    lean_dec_ref_known(v_code_1074_, 2);
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
                    if lean_obj_tag(v___x_1097_) == 0 {
                        lean_dec_ref_known(v___x_1097_, 1);
                        v_code_1074_ = v_k_1096_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_k_1096_);
                        return v___x_1097_;
                    }
                }
                3 => {
                    v_fvarId_1099_ = lean_ctor_get(v_code_1074_, 0);
                    lean_inc(v_fvarId_1099_);
                    v_args_1100_ = lean_ctor_get(v_code_1074_, 1);
                    lean_inc_ref(v_args_1100_);
                    lean_dec_ref_known(v_code_1074_, 2);
                    v___x_1101_ =
                        l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_fvarId_1099_, v_a_1076_);
                    if lean_obj_tag(v___x_1101_) == 0 {
                        v_isSharedCheck_1122_ = (!lean_is_exclusive(v___x_1101_)) as u8;
                        if v_isSharedCheck_1122_ == 0 {
                            v_unused_1123_ = lean_ctor_get(v___x_1101_, 0);
                            lean_dec(v_unused_1123_);
                            v___x_1103_ = v___x_1101_;
                            v_isShared_1104_ = v_isSharedCheck_1122_;
                            state = 2;
                            continue;
                        } else {
                            lean_dec(v___x_1101_);
                            v___x_1103_ = lean_box(0);
                            v_isShared_1104_ = v_isSharedCheck_1122_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_args_1100_);
                        return v___x_1101_;
                    }
                }
                4 => {
                    v_cases_1124_ = lean_ctor_get(v_code_1074_, 0);
                    lean_inc_ref(v_cases_1124_);
                    lean_dec_ref_known(v_code_1074_, 1);
                    v_discr_1125_ = lean_ctor_get(v_cases_1124_, 2);
                    lean_inc(v_discr_1125_);
                    v_alts_1126_ = lean_ctor_get(v_cases_1124_, 3);
                    lean_inc_ref(v_alts_1126_);
                    lean_dec_ref(v_cases_1124_);
                    v___x_1127_ =
                        l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_discr_1125_, v_a_1076_);
                    if lean_obj_tag(v___x_1127_) == 0 {
                        v_isSharedCheck_1148_ = (!lean_is_exclusive(v___x_1127_)) as u8;
                        if v_isSharedCheck_1148_ == 0 {
                            v_unused_1149_ = lean_ctor_get(v___x_1127_, 0);
                            lean_dec(v_unused_1149_);
                            v___x_1129_ = v___x_1127_;
                            v_isShared_1130_ = v_isSharedCheck_1148_;
                            state = 5;
                            continue;
                        } else {
                            lean_dec(v___x_1127_);
                            v___x_1129_ = lean_box(0);
                            v_isShared_1130_ = v_isSharedCheck_1148_;
                            state = 5;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_alts_1126_);
                        return v___x_1127_;
                    }
                }
                5 => {
                    v_fvarId_1150_ = lean_ctor_get(v_code_1074_, 0);
                    lean_inc(v_fvarId_1150_);
                    lean_dec_ref_known(v_code_1074_, 1);
                    v___x_1151_ =
                        l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_fvarId_1150_, v_a_1076_);
                    return v___x_1151_;
                }
                6 => {
                    v_isSharedCheck_1159_ = (!lean_is_exclusive(v_code_1074_)) as u8;
                    if v_isSharedCheck_1159_ == 0 {
                        v_unused_1160_ = lean_ctor_get(v_code_1074_, 0);
                        lean_dec(v_unused_1160_);
                        v___x_1153_ = v_code_1074_;
                        v_isShared_1154_ = v_isSharedCheck_1159_;
                        state = 8;
                        continue;
                    } else {
                        lean_dec(v_code_1074_);
                        v___x_1153_ = lean_box(0);
                        v_isShared_1154_ = v_isSharedCheck_1159_;
                        state = 8;
                        continue;
                    }
                }
                _ => {
                    v_decl_1161_ = lean_ctor_get(v_code_1074_, 0);
                    lean_inc_ref(v_decl_1161_);
                    v_k_1162_ = lean_ctor_get(v_code_1074_, 1);
                    lean_inc_ref(v_k_1162_);
                    lean_dec_ref(v_code_1074_);
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
                if lean_obj_tag(v___x_1093_) == 0 {
                    lean_dec_ref_known(v___x_1093_, 1);
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
                    lean_dec_ref(v_k_1085_);
                    return v___x_1093_;
                }
            }
            2 => {
                v___x_1105_ = lean_unsigned_to_nat(0);
                v___x_1106_ = lean_array_get_size(v_args_1100_);
                v___x_1107_ = lean_box(0);
                v___x_1108_ = lean_nat_dec_lt(v___x_1105_, v___x_1106_);
                if v___x_1108_ == 0 {
                    lean_dec_ref(v_args_1100_);
                    if v_isShared_1104_ == 0 {
                        lean_ctor_set(v___x_1103_, 0, v___x_1107_);
                        v___x_1110_ = v___x_1103_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1111_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1111_, 0, v___x_1107_);
                        v___x_1110_ = v_reuseFailAlloc_1111_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___x_1112_ = lean_nat_dec_le(v___x_1106_, v___x_1106_);
                    if v___x_1112_ == 0 {
                        if v___x_1108_ == 0 {
                            lean_dec_ref(v_args_1100_);
                            if v_isShared_1104_ == 0 {
                                lean_ctor_set(v___x_1103_, 0, v___x_1107_);
                                v___x_1114_ = v___x_1103_;
                                state = 4;
                                continue;
                            } else {
                                v_reuseFailAlloc_1115_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_1115_, 0, v___x_1107_);
                                v___x_1114_ = v_reuseFailAlloc_1115_;
                                state = 4;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_1103_);
                            v___x_1116_ = 0usize;
                            v___x_1117_ = lean_usize_of_nat(v___x_1106_);
                            v___x_1118_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___redArg(v_args_1100_, v___x_1116_, v___x_1117_, v___x_1107_, v_a_1076_);
                            lean_dec_ref(v_args_1100_);
                            return v___x_1118_;
                        }
                    } else {
                        lean_del_object(v___x_1103_);
                        v___x_1119_ = 0usize;
                        v___x_1120_ = lean_usize_of_nat(v___x_1106_);
                        v___x_1121_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___redArg(v_args_1100_, v___x_1119_, v___x_1120_, v___x_1107_, v_a_1076_);
                        lean_dec_ref(v_args_1100_);
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
                v___x_1131_ = lean_unsigned_to_nat(0);
                v___x_1132_ = lean_array_get_size(v_alts_1126_);
                v___x_1133_ = lean_box(0);
                v___x_1134_ = lean_nat_dec_lt(v___x_1131_, v___x_1132_);
                if v___x_1134_ == 0 {
                    lean_dec_ref(v_alts_1126_);
                    if v_isShared_1130_ == 0 {
                        lean_ctor_set(v___x_1129_, 0, v___x_1133_);
                        v___x_1136_ = v___x_1129_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1137_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1137_, 0, v___x_1133_);
                        v___x_1136_ = v_reuseFailAlloc_1137_;
                        state = 6;
                        continue;
                    }
                } else {
                    v___x_1138_ = lean_nat_dec_le(v___x_1132_, v___x_1132_);
                    if v___x_1138_ == 0 {
                        if v___x_1134_ == 0 {
                            lean_dec_ref(v_alts_1126_);
                            if v_isShared_1130_ == 0 {
                                lean_ctor_set(v___x_1129_, 0, v___x_1133_);
                                v___x_1140_ = v___x_1129_;
                                state = 7;
                                continue;
                            } else {
                                v_reuseFailAlloc_1141_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_1141_, 0, v___x_1133_);
                                v___x_1140_ = v_reuseFailAlloc_1141_;
                                state = 7;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_1129_);
                            v___x_1142_ = 0usize;
                            v___x_1143_ = lean_usize_of_nat(v___x_1132_);
                            v___x_1144_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedCode_spec__0(v_alts_1126_, v___x_1142_, v___x_1143_, v___x_1133_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_);
                            lean_dec_ref(v_alts_1126_);
                            return v___x_1144_;
                        }
                    } else {
                        lean_del_object(v___x_1129_);
                        v___x_1145_ = 0usize;
                        v___x_1146_ = lean_usize_of_nat(v___x_1132_);
                        v___x_1147_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedCode_spec__0(v_alts_1126_, v___x_1145_, v___x_1146_, v___x_1133_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_);
                        lean_dec_ref(v_alts_1126_);
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
                v___x_1155_ = lean_box(0);
                if v_isShared_1154_ == 0 {
                    lean_ctor_set_tag(v___x_1153_, 0);
                    lean_ctor_set(v___x_1153_, 0, v___x_1155_);
                    v___x_1157_ = v___x_1153_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1158_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1158_, 0, v___x_1155_);
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
    mut v_funDecl_1163_: *mut LeanObject,
    mut v_a_1164_: *mut LeanObject,
    mut v_a_1165_: *mut LeanObject,
    mut v_a_1166_: *mut LeanObject,
    mut v_a_1167_: *mut LeanObject,
    mut v_a_1168_: *mut LeanObject,
    mut v_a_1169_: *mut LeanObject,
    mut v_a_1170_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_value_1172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut LeanObject = core::ptr::null_mut();
    v_value_1172_ = lean_ctor_get(v_funDecl_1163_, 4);
    lean_inc_ref(v_value_1172_);
    lean_dec_ref(v_funDecl_1163_);
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
    mut v_funDecl_1174_: *mut LeanObject,
    mut v_a_1175_: *mut LeanObject,
    mut v_a_1176_: *mut LeanObject,
    mut v_a_1177_: *mut LeanObject,
    mut v_a_1178_: *mut LeanObject,
    mut v_a_1179_: *mut LeanObject,
    mut v_a_1180_: *mut LeanObject,
    mut v_a_1181_: *mut LeanObject,
    mut v_a_1182_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1183_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_1181_);
    lean_dec_ref(v_a_1180_);
    lean_dec(v_a_1179_);
    lean_dec_ref(v_a_1178_);
    lean_dec_ref(v_a_1177_);
    lean_dec(v_a_1176_);
    lean_dec_ref(v_a_1175_);
    return v_res_1183_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedCode_spec__0___boxed(
    mut v_as_1184_: *mut LeanObject,
    mut v_i_1185_: *mut LeanObject,
    mut v_stop_1186_: *mut LeanObject,
    mut v_b_1187_: *mut LeanObject,
    mut v___y_1188_: *mut LeanObject,
    mut v___y_1189_: *mut LeanObject,
    mut v___y_1190_: *mut LeanObject,
    mut v___y_1191_: *mut LeanObject,
    mut v___y_1192_: *mut LeanObject,
    mut v___y_1193_: *mut LeanObject,
    mut v___y_1194_: *mut LeanObject,
    mut v___y_1195_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1196_: usize = 0;
    let mut v_stop_boxed_1197_: usize = 0;
    let mut v_res_1198_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1196_ = lean_unbox_usize(v_i_1185_);
    lean_dec(v_i_1185_);
    v_stop_boxed_1197_ = lean_unbox_usize(v_stop_1186_);
    lean_dec(v_stop_1186_);
    v_res_1198_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_markUsedCode_spec__0(v_as_1184_, v_i_boxed_1196_, v_stop_boxed_1197_, v_b_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_);
    lean_dec(v___y_1194_);
    lean_dec_ref(v___y_1193_);
    lean_dec(v___y_1192_);
    lean_dec_ref(v___y_1191_);
    lean_dec_ref(v___y_1190_);
    lean_dec(v___y_1189_);
    lean_dec_ref(v___y_1188_);
    lean_dec_ref(v_as_1184_);
    return v_res_1198_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_markUsedCode___boxed(
    mut v_code_1199_: *mut LeanObject,
    mut v_a_1200_: *mut LeanObject,
    mut v_a_1201_: *mut LeanObject,
    mut v_a_1202_: *mut LeanObject,
    mut v_a_1203_: *mut LeanObject,
    mut v_a_1204_: *mut LeanObject,
    mut v_a_1205_: *mut LeanObject,
    mut v_a_1206_: *mut LeanObject,
    mut v_a_1207_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1208_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_1206_);
    lean_dec_ref(v_a_1205_);
    lean_dec(v_a_1204_);
    lean_dec_ref(v_a_1203_);
    lean_dec_ref(v_a_1202_);
    lean_dec(v_a_1201_);
    lean_dec_ref(v_a_1200_);
    return v_res_1208_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Simp_isUsed_spec__0___redArg(
    mut v_m_1209_: *mut LeanObject,
    mut v_a_1210_: *mut LeanObject,
) -> u8 {
    let mut v_buckets_1211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1212_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_1225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: u8 = 0;
    v_buckets_1211_ = lean_ctor_get(v_m_1209_, 1);
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
    mut v_m_1227_: *mut LeanObject,
    mut v_a_1228_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1229_: u8 = 0;
    let mut v_r_1230_: *mut LeanObject = core::ptr::null_mut();
    v_res_1229_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Simp_isUsed_spec__0___redArg(v_m_1227_, v_a_1228_);
    lean_dec(v_a_1228_);
    lean_dec_ref(v_m_1227_);
    v_r_1230_ = lean_box((v_res_1229_) as usize);
    return v_r_1230_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_isUsed___redArg(
    mut v_fvarId_1231_: *mut LeanObject,
    mut v_a_1232_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_used_1235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: u8 = 0;
    let mut v___x_1237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1238_: *mut LeanObject = core::ptr::null_mut();
    v___x_1234_ = lean_st_ref_get(v_a_1232_);
    v_used_1235_ = lean_ctor_get(v___x_1234_, 1);
    lean_inc_ref(v_used_1235_);
    lean_dec(v___x_1234_);
    v___x_1236_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Simp_isUsed_spec__0___redArg(v_used_1235_, v_fvarId_1231_);
    lean_dec_ref(v_used_1235_);
    v___x_1237_ = lean_box((v___x_1236_) as usize);
    v___x_1238_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1238_, 0, v___x_1237_);
    return v___x_1238_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_isUsed___redArg___boxed(
    mut v_fvarId_1239_: *mut LeanObject,
    mut v_a_1240_: *mut LeanObject,
    mut v_a_1241_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1242_: *mut LeanObject = core::ptr::null_mut();
    v_res_1242_ = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(v_fvarId_1239_, v_a_1240_);
    lean_dec(v_a_1240_);
    lean_dec(v_fvarId_1239_);
    return v_res_1242_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_isUsed(
    mut v_fvarId_1243_: *mut LeanObject,
    mut v_a_1244_: *mut LeanObject,
    mut v_a_1245_: *mut LeanObject,
    mut v_a_1246_: *mut LeanObject,
    mut v_a_1247_: *mut LeanObject,
    mut v_a_1248_: *mut LeanObject,
    mut v_a_1249_: *mut LeanObject,
    mut v_a_1250_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1252_: *mut LeanObject = core::ptr::null_mut();
    v___x_1252_ = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(v_fvarId_1243_, v_a_1245_);
    return v___x_1252_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_isUsed___boxed(
    mut v_fvarId_1253_: *mut LeanObject,
    mut v_a_1254_: *mut LeanObject,
    mut v_a_1255_: *mut LeanObject,
    mut v_a_1256_: *mut LeanObject,
    mut v_a_1257_: *mut LeanObject,
    mut v_a_1258_: *mut LeanObject,
    mut v_a_1259_: *mut LeanObject,
    mut v_a_1260_: *mut LeanObject,
    mut v_a_1261_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1262_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_1260_);
    lean_dec_ref(v_a_1259_);
    lean_dec(v_a_1258_);
    lean_dec_ref(v_a_1257_);
    lean_dec_ref(v_a_1256_);
    lean_dec(v_a_1255_);
    lean_dec_ref(v_a_1254_);
    lean_dec(v_fvarId_1253_);
    return v_res_1262_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Simp_isUsed_spec__0(
    mut v_00_u03b2_1263_: *mut LeanObject,
    mut v_m_1264_: *mut LeanObject,
    mut v_a_1265_: *mut LeanObject,
) -> u8 {
    let mut v___x_1266_: u8 = 0;
    v___x_1266_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Simp_isUsed_spec__0___redArg(v_m_1264_, v_a_1265_);
    return v___x_1266_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Simp_isUsed_spec__0___boxed(
    mut v_00_u03b2_1267_: *mut LeanObject,
    mut v_m_1268_: *mut LeanObject,
    mut v_a_1269_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1270_: u8 = 0;
    let mut v_r_1271_: *mut LeanObject = core::ptr::null_mut();
    v_res_1270_ =
        l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Simp_isUsed_spec__0(
            v_00_u03b2_1267_,
            v_m_1268_,
            v_a_1269_,
        );
    lean_dec(v_a_1269_);
    lean_dec_ref(v_m_1268_);
    v_r_1271_ = lean_box((v_res_1270_) as usize);
    return v_r_1271_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__0()
-> *mut LeanObject {
    let mut v___x_1272_: u8 = 0;
    let mut v___x_1273_: *mut LeanObject = core::ptr::null_mut();
    v___x_1272_ = 0;
    v___x_1273_ = l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default(v___x_1272_);
    return v___x_1273_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go(
    mut v_decls_1274_: *mut LeanObject,
    mut v_i_1275_: *mut LeanObject,
    mut v_code_1276_: *mut LeanObject,
    mut v_a_1277_: *mut LeanObject,
    mut v_a_1278_: *mut LeanObject,
    mut v_a_1279_: *mut LeanObject,
    mut v_a_1280_: *mut LeanObject,
    mut v_a_1281_: *mut LeanObject,
    mut v_a_1282_: *mut LeanObject,
    mut v_a_1283_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1286_: u8 = 0;
    let mut v___x_1287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: u8 = 0;
    let mut v___x_1289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decl_1292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: u8 = 0;
    let mut v___x_1297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1302_: u8 = 0;
    let mut v___x_1304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1306_: u8 = 0;
    let mut v_decl_1307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1314_: u8 = 0;
    let mut v___x_1316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1318_: u8 = 0;
    let mut v_decl_1319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1326_: u8 = 0;
    let mut v___x_1328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1330_: u8 = 0;
    let mut v_decl_1331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1338_: u8 = 0;
    let mut v___x_1340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1342_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1285_ = lean_unsigned_to_nat(0);
                v___x_1286_ = lean_nat_dec_lt(v___x_1285_, v_i_1275_);
                if v___x_1286_ == 0 {
                    lean_dec(v_i_1275_);
                    v___x_1287_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1287_, 0, v_code_1276_);
                    return v___x_1287_;
                } else {
                    v___x_1288_ = 0;
                    v___x_1289_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__0_once), _init_l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go___closed__0);
                    v___x_1290_ = lean_unsigned_to_nat(1);
                    v___x_1291_ = lean_nat_sub(v_i_1275_, v___x_1290_);
                    lean_dec(v_i_1275_);
                    v_decl_1292_ = lean_array_get_borrowed(v___x_1289_, v_decls_1274_, v___x_1291_);
                    v___x_1293_ = l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg(v_decl_1292_);
                    v___x_1294_ = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(v___x_1293_, v_a_1278_);
                    lean_dec(v___x_1293_);
                    v_a_1295_ = lean_ctor_get(v___x_1294_, 0);
                    lean_inc(v_a_1295_);
                    lean_dec_ref(v___x_1294_);
                    v___x_1296_ = (lean_unbox(v_a_1295_) as u8);
                    lean_dec(v_a_1295_);
                    if v___x_1296_ == 0 {
                        v___x_1297_ = l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(
                            v___x_1288_,
                            v_decl_1292_,
                            v_a_1281_,
                        );
                        if lean_obj_tag(v___x_1297_) == 0 {
                            lean_dec_ref_known(v___x_1297_, 1);
                            v_i_1275_ = v___x_1291_;
                            state = 0;
                            continue;
                        } else {
                            lean_dec(v___x_1291_);
                            lean_dec_ref(v_code_1276_);
                            v_a_1299_ = lean_ctor_get(v___x_1297_, 0);
                            v_isSharedCheck_1306_ = (!lean_is_exclusive(v___x_1297_)) as u8;
                            if v_isSharedCheck_1306_ == 0 {
                                v___x_1301_ = v___x_1297_;
                                v_isShared_1302_ = v_isSharedCheck_1306_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_1299_);
                                lean_dec(v___x_1297_);
                                v___x_1301_ = lean_box(0);
                                v_isShared_1302_ = v_isSharedCheck_1306_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        match lean_obj_tag(v_decl_1292_) {
                            0 => {
                                v_decl_1307_ = lean_ctor_get(v_decl_1292_, 0);
                                lean_inc_ref(v_decl_1307_);
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
                                if lean_obj_tag(v___x_1308_) == 0 {
                                    lean_dec_ref_known(v___x_1308_, 1);
                                    lean_inc_ref(v_decl_1307_);
                                    v___x_1309_ = lean_alloc_ctor(0, 2, (0) as u32);
                                    lean_ctor_set(v___x_1309_, 0, v_decl_1307_);
                                    lean_ctor_set(v___x_1309_, 1, v_code_1276_);
                                    v_i_1275_ = v___x_1291_;
                                    v_code_1276_ = v___x_1309_;
                                    state = 0;
                                    continue;
                                } else {
                                    lean_dec(v___x_1291_);
                                    lean_dec_ref(v_code_1276_);
                                    v_a_1311_ = lean_ctor_get(v___x_1308_, 0);
                                    v_isSharedCheck_1318_ = (!lean_is_exclusive(v___x_1308_)) as u8;
                                    if v_isSharedCheck_1318_ == 0 {
                                        v___x_1313_ = v___x_1308_;
                                        v_isShared_1314_ = v_isSharedCheck_1318_;
                                        state = 3;
                                        continue;
                                    } else {
                                        lean_inc(v_a_1311_);
                                        lean_dec(v___x_1308_);
                                        v___x_1313_ = lean_box(0);
                                        v_isShared_1314_ = v_isSharedCheck_1318_;
                                        state = 3;
                                        continue;
                                    }
                                }
                            }
                            1 => {
                                v_decl_1319_ = lean_ctor_get(v_decl_1292_, 0);
                                lean_inc_ref(v_decl_1319_);
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
                                if lean_obj_tag(v___x_1320_) == 0 {
                                    lean_dec_ref_known(v___x_1320_, 1);
                                    lean_inc_ref(v_decl_1319_);
                                    v___x_1321_ = lean_alloc_ctor(1, 2, (0) as u32);
                                    lean_ctor_set(v___x_1321_, 0, v_decl_1319_);
                                    lean_ctor_set(v___x_1321_, 1, v_code_1276_);
                                    v_i_1275_ = v___x_1291_;
                                    v_code_1276_ = v___x_1321_;
                                    state = 0;
                                    continue;
                                } else {
                                    lean_dec(v___x_1291_);
                                    lean_dec_ref(v_code_1276_);
                                    v_a_1323_ = lean_ctor_get(v___x_1320_, 0);
                                    v_isSharedCheck_1330_ = (!lean_is_exclusive(v___x_1320_)) as u8;
                                    if v_isSharedCheck_1330_ == 0 {
                                        v___x_1325_ = v___x_1320_;
                                        v_isShared_1326_ = v_isSharedCheck_1330_;
                                        state = 5;
                                        continue;
                                    } else {
                                        lean_inc(v_a_1323_);
                                        lean_dec(v___x_1320_);
                                        v___x_1325_ = lean_box(0);
                                        v_isShared_1326_ = v_isSharedCheck_1330_;
                                        state = 5;
                                        continue;
                                    }
                                }
                            }
                            _ => {
                                v_decl_1331_ = lean_ctor_get(v_decl_1292_, 0);
                                lean_inc_ref(v_decl_1331_);
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
                                if lean_obj_tag(v___x_1332_) == 0 {
                                    lean_dec_ref_known(v___x_1332_, 1);
                                    lean_inc_ref(v_decl_1331_);
                                    v___x_1333_ = lean_alloc_ctor(2, 2, (0) as u32);
                                    lean_ctor_set(v___x_1333_, 0, v_decl_1331_);
                                    lean_ctor_set(v___x_1333_, 1, v_code_1276_);
                                    v_i_1275_ = v___x_1291_;
                                    v_code_1276_ = v___x_1333_;
                                    state = 0;
                                    continue;
                                } else {
                                    lean_dec(v___x_1291_);
                                    lean_dec_ref(v_code_1276_);
                                    v_a_1335_ = lean_ctor_get(v___x_1332_, 0);
                                    v_isSharedCheck_1342_ = (!lean_is_exclusive(v___x_1332_)) as u8;
                                    if v_isSharedCheck_1342_ == 0 {
                                        v___x_1337_ = v___x_1332_;
                                        v_isShared_1338_ = v_isSharedCheck_1342_;
                                        state = 7;
                                        continue;
                                    } else {
                                        lean_inc(v_a_1335_);
                                        lean_dec(v___x_1332_);
                                        v___x_1337_ = lean_box(0);
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
                    v_reuseFailAlloc_1305_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1305_, 0, v_a_1299_);
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
                    v_reuseFailAlloc_1317_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1317_, 0, v_a_1311_);
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
                    v_reuseFailAlloc_1329_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1329_, 0, v_a_1323_);
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
                    v_reuseFailAlloc_1341_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1341_, 0, v_a_1335_);
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
    mut v_decls_1343_: *mut LeanObject,
    mut v_i_1344_: *mut LeanObject,
    mut v_code_1345_: *mut LeanObject,
    mut v_a_1346_: *mut LeanObject,
    mut v_a_1347_: *mut LeanObject,
    mut v_a_1348_: *mut LeanObject,
    mut v_a_1349_: *mut LeanObject,
    mut v_a_1350_: *mut LeanObject,
    mut v_a_1351_: *mut LeanObject,
    mut v_a_1352_: *mut LeanObject,
    mut v_a_1353_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1354_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_1352_);
    lean_dec_ref(v_a_1351_);
    lean_dec(v_a_1350_);
    lean_dec_ref(v_a_1349_);
    lean_dec_ref(v_a_1348_);
    lean_dec(v_a_1347_);
    lean_dec_ref(v_a_1346_);
    lean_dec_ref(v_decls_1343_);
    return v_res_1354_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go_match__1_splitter___redArg(
    mut v_decl_1355_: *mut LeanObject,
    mut v_h__1_1356_: *mut LeanObject,
    mut v_h__2_1357_: *mut LeanObject,
    mut v_h__3_1358_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_decl_1355_) {
        0 => {
            let mut v_decl_1359_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1360_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1358_);
            lean_dec(v_h__2_1357_);
            v_decl_1359_ = lean_ctor_get(v_decl_1355_, 0);
            lean_inc_ref(v_decl_1359_);
            lean_dec_ref_known(v_decl_1355_, 1);
            v___x_1360_ = lean_apply_1(v_h__1_1356_, v_decl_1359_);
            return v___x_1360_;
        }
        1 => {
            let mut v_decl_1361_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1362_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1358_);
            lean_dec(v_h__1_1356_);
            v_decl_1361_ = lean_ctor_get(v_decl_1355_, 0);
            lean_inc_ref(v_decl_1361_);
            lean_dec_ref_known(v_decl_1355_, 1);
            v___x_1362_ = lean_apply_1(v_h__2_1357_, v_decl_1361_);
            return v___x_1362_;
        }
        _ => {
            let mut v_decl_1363_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1364_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_1357_);
            lean_dec(v_h__1_1356_);
            v_decl_1363_ = lean_ctor_get(v_decl_1355_, 0);
            lean_inc_ref(v_decl_1363_);
            lean_dec_ref_known(v_decl_1355_, 1);
            v___x_1364_ = lean_apply_1(v_h__3_1358_, v_decl_1363_);
            return v___x_1364_;
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Simp_Used_0__Lean_Compiler_LCNF_Simp_attachCodeDecls_go_match__1_splitter(
    mut v_motive_1365_: *mut LeanObject,
    mut v_decl_1366_: *mut LeanObject,
    mut v_h__1_1367_: *mut LeanObject,
    mut v_h__2_1368_: *mut LeanObject,
    mut v_h__3_1369_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_decl_1366_) {
        0 => {
            let mut v_decl_1370_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1371_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1369_);
            lean_dec(v_h__2_1368_);
            v_decl_1370_ = lean_ctor_get(v_decl_1366_, 0);
            lean_inc_ref(v_decl_1370_);
            lean_dec_ref_known(v_decl_1366_, 1);
            v___x_1371_ = lean_apply_1(v_h__1_1367_, v_decl_1370_);
            return v___x_1371_;
        }
        1 => {
            let mut v_decl_1372_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1373_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1369_);
            lean_dec(v_h__1_1367_);
            v_decl_1372_ = lean_ctor_get(v_decl_1366_, 0);
            lean_inc_ref(v_decl_1372_);
            lean_dec_ref_known(v_decl_1366_, 1);
            v___x_1373_ = lean_apply_1(v_h__2_1368_, v_decl_1372_);
            return v___x_1373_;
        }
        _ => {
            let mut v_decl_1374_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1375_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_1368_);
            lean_dec(v_h__1_1367_);
            v_decl_1374_ = lean_ctor_get(v_decl_1366_, 0);
            lean_inc_ref(v_decl_1374_);
            lean_dec_ref_known(v_decl_1366_, 1);
            v___x_1375_ = lean_apply_1(v_h__3_1369_, v_decl_1374_);
            return v___x_1375_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_attachCodeDecls(
    mut v_decls_1376_: *mut LeanObject,
    mut v_code_1377_: *mut LeanObject,
    mut v_a_1378_: *mut LeanObject,
    mut v_a_1379_: *mut LeanObject,
    mut v_a_1380_: *mut LeanObject,
    mut v_a_1381_: *mut LeanObject,
    mut v_a_1382_: *mut LeanObject,
    mut v_a_1383_: *mut LeanObject,
    mut v_a_1384_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_decls_1388_: *mut LeanObject,
    mut v_code_1389_: *mut LeanObject,
    mut v_a_1390_: *mut LeanObject,
    mut v_a_1391_: *mut LeanObject,
    mut v_a_1392_: *mut LeanObject,
    mut v_a_1393_: *mut LeanObject,
    mut v_a_1394_: *mut LeanObject,
    mut v_a_1395_: *mut LeanObject,
    mut v_a_1396_: *mut LeanObject,
    mut v_a_1397_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1398_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_1396_);
    lean_dec_ref(v_a_1395_);
    lean_dec(v_a_1394_);
    lean_dec_ref(v_a_1393_);
    lean_dec_ref(v_a_1392_);
    lean_dec(v_a_1391_);
    lean_dec_ref(v_a_1390_);
    lean_dec_ref(v_decls_1388_);
    return v_res_1398_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_Simp_Used(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_Simp_SimpM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_Simp_Used(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_LCNF_Simp_Used(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_Simp_SimpM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Simp_Used(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_Simp_Used(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_Simp_Used(builtin);
}
