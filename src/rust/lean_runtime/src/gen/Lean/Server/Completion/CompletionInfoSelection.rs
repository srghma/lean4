// Lean compiler output
// Module: Lean.Server.Completion.CompletionInfoSelection
// Imports: Lean.Server.Completion.SyntheticCompletion
use crate::r#gen::Init::Data::Array::Basic::l_Array_zipIdx___redArg;
use crate::r#gen::Init::Data::String::Hashable::l_String_instHashableRaw_hash;
use crate::r#gen::Init::Prelude::{l_Lean_Syntax_getArg, l_Lean_Syntax_isMissing};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Data::Position::l_Lean_FileMap_toPosition;
use crate::r#gen::Lean::Server::Completion::SyntheticCompletion::{
    initialize_Lean_Server_Completion_SyntheticCompletion,
    l_Lean_Server_Completion_findSyntheticCompletions,
    runtime_initialize_Lean_Server_Completion_SyntheticCompletion,
};
use crate::r#gen::Lean::Server::InfoUtils::{
    l_Lean_Elab_Info_occursInOrOnBoundary, l_Lean_Elab_Info_pos_x3f, l_Lean_Elab_Info_size_x3f,
    l_Lean_Elab_Info_tailPos_x3f, l_Lean_Elab_InfoTree_foldInfo___redArg,
};
use crate::r#gen::Lean::Syntax::{
    l_Lean_Syntax_Range_contains, l_Lean_Syntax_eqWithInfo, l_Lean_Syntax_getRangeWithTrailing_x3f,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_fswap, lean_array_size, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::Nat::Bitwise::Basic::lean_nat_shiftr;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_size, lean_array_push,
    lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_sub,
    lean_panic_fn_borrowed, lean_uint64_mix_hash, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Lean::Expr::lean_expr_eqv;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unbox,
    lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__0_value: LeanStringObject<26> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [73, 110, 105, 116, 46, 68, 97, 116, 97, 46, 79, 112, 116, 105, 111, 110, 46, 66, 97, 115, 105, 99, 65, 117, 120, 0]};
static mut l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__1_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [79, 112, 116, 105, 111, 110, 46, 103, 101, 116, 33, 0]};
static mut l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__2_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [118, 97, 108, 117, 101, 32, 105, 115, 32, 110, 111, 110, 101, 0]};
static mut l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__2_value) as *mut LeanObject;
static mut l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6___redArg___lam__0___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6___redArg___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6___redArg___lam__0___closed__0_value) as *mut LeanObject;
static mut l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions___lam__0 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions___closed__0_value) as *mut LeanObject;
pub unsafe fn l_Option_instBEq_beq___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_eq_spec__0(
    mut v_x_804_: *mut LeanObject,
    mut v_x_805_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_804_) == 0 {
        if lean_obj_tag(v_x_805_) == 0 {
            let mut v___x_806_: u8 = 0;
            v___x_806_ = 1;
            return v___x_806_;
        } else {
            let mut v___x_807_: u8 = 0;
            v___x_807_ = 0;
            return v___x_807_;
        }
    } else {
        if lean_obj_tag(v_x_805_) == 0 {
            let mut v___x_808_: u8 = 0;
            v___x_808_ = 0;
            return v___x_808_;
        } else {
            let mut v_val_809_: *mut LeanObject = core::ptr::null_mut();
            let mut v_val_810_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_811_: u8 = 0;
            v_val_809_ = lean_ctor_get(v_x_804_, 0);
            v_val_810_ = lean_ctor_get(v_x_805_, 0);
            v___x_811_ = lean_name_eq(v_val_809_, v_val_810_);
            return v___x_811_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_eq_spec__0___boxed(
    mut v_x_812_: *mut LeanObject,
    mut v_x_813_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_814_: u8 = 0;
    let mut v_r_815_: *mut LeanObject = core::ptr::null_mut();
    v_res_814_ = l_Option_instBEq_beq___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_eq_spec__0(v_x_812_, v_x_813_);
    lean_dec(v_x_813_);
    lean_dec(v_x_812_);
    v_r_815_ = lean_box((v_res_814_) as usize);
    return v_r_815_;
}
pub unsafe fn l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_eq(
    mut v_a_816_: *mut LeanObject,
    mut v_a_817_: *mut LeanObject,
) -> u8 {
    let mut v_termInfo_818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toElabInfo_819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_termInfo_820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toElabInfo_821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stx_823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stx_825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_826_: u8 = 0;
    let mut v___x_827_: u8 = 0;
    let mut v___x_828_: u8 = 0;
    let mut v_stx_829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_structName_831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stx_832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_structName_834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_836_: u8 = 0;
    let mut v___x_837_: u8 = 0;
    let mut v___x_838_: u8 = 0;
    let mut v___x_839_: u8 = 0;
    let mut v___x_840_: u8 = 0;
    let mut v_stx_841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stx_842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_843_: u8 = 0;
    let mut v___x_844_: u8 = 0;
    let mut v_stx_845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stx_846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_847_: u8 = 0;
    let mut v___x_848_: u8 = 0;
    let mut v_stx_849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stx_850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_851_: u8 = 0;
    let mut v___x_852_: u8 = 0;
    let mut v_stx_853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stx_854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_855_: u8 = 0;
    let mut v___x_856_: u8 = 0;
    let mut v_stx_857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stx_858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_859_: u8 = 0;
    let mut v___x_860_: u8 = 0;
    let mut v_stx_861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stx_863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_865_: u8 = 0;
    let mut v___x_866_: u8 = 0;
    let mut v___x_867_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_a_816_) {
                0 => {
                    if lean_obj_tag(v_a_817_) == 0 {
                        v_termInfo_818_ = lean_ctor_get(v_a_816_, 0);
                        lean_inc_ref(v_termInfo_818_);
                        lean_dec_ref_known(v_a_816_, 2);
                        v_toElabInfo_819_ = lean_ctor_get(v_termInfo_818_, 0);
                        lean_inc_ref(v_toElabInfo_819_);
                        v_termInfo_820_ = lean_ctor_get(v_a_817_, 0);
                        lean_inc_ref(v_termInfo_820_);
                        lean_dec_ref_known(v_a_817_, 2);
                        v_toElabInfo_821_ = lean_ctor_get(v_termInfo_820_, 0);
                        lean_inc_ref(v_toElabInfo_821_);
                        v_expr_822_ = lean_ctor_get(v_termInfo_818_, 3);
                        lean_inc_ref(v_expr_822_);
                        lean_dec_ref(v_termInfo_818_);
                        v_stx_823_ = lean_ctor_get(v_toElabInfo_819_, 1);
                        lean_inc(v_stx_823_);
                        lean_dec_ref(v_toElabInfo_819_);
                        v_expr_824_ = lean_ctor_get(v_termInfo_820_, 3);
                        lean_inc_ref(v_expr_824_);
                        lean_dec_ref(v_termInfo_820_);
                        v_stx_825_ = lean_ctor_get(v_toElabInfo_821_, 1);
                        lean_inc(v_stx_825_);
                        lean_dec_ref(v_toElabInfo_821_);
                        v___x_826_ = l_Lean_Syntax_eqWithInfo(v_stx_823_, v_stx_825_);
                        if v___x_826_ == 0 {
                            lean_dec_ref(v_expr_824_);
                            lean_dec_ref(v_expr_822_);
                            return v___x_826_;
                        } else {
                            v___x_827_ = lean_expr_eqv(v_expr_822_, v_expr_824_);
                            lean_dec_ref(v_expr_824_);
                            lean_dec_ref(v_expr_822_);
                            return v___x_827_;
                        }
                    } else {
                        lean_dec_ref_known(v_a_816_, 2);
                        lean_dec_ref(v_a_817_);
                        v___x_828_ = 0;
                        return v___x_828_;
                    }
                }
                3 => {
                    if lean_obj_tag(v_a_817_) == 3 {
                        v_stx_829_ = lean_ctor_get(v_a_816_, 0);
                        lean_inc(v_stx_829_);
                        v_id_830_ = lean_ctor_get(v_a_816_, 1);
                        lean_inc(v_id_830_);
                        v_structName_831_ = lean_ctor_get(v_a_816_, 3);
                        lean_inc(v_structName_831_);
                        lean_dec_ref_known(v_a_816_, 4);
                        v_stx_832_ = lean_ctor_get(v_a_817_, 0);
                        lean_inc(v_stx_832_);
                        v_id_833_ = lean_ctor_get(v_a_817_, 1);
                        lean_inc(v_id_833_);
                        v_structName_834_ = lean_ctor_get(v_a_817_, 3);
                        lean_inc(v_structName_834_);
                        lean_dec_ref_known(v_a_817_, 4);
                        v___x_838_ = l_Lean_Syntax_eqWithInfo(v_stx_829_, v_stx_832_);
                        if v___x_838_ == 0 {
                            lean_dec(v_id_833_);
                            lean_dec(v_id_830_);
                            v___y_836_ = v___x_838_;
                            state = 1;
                            continue;
                        } else {
                            v___x_839_ = l_Option_instBEq_beq___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_eq_spec__0(v_id_830_, v_id_833_);
                            lean_dec(v_id_833_);
                            lean_dec(v_id_830_);
                            v___y_836_ = v___x_839_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v_a_816_, 4);
                        lean_dec_ref(v_a_817_);
                        v___x_840_ = 0;
                        return v___x_840_;
                    }
                }
                4 => {
                    if lean_obj_tag(v_a_817_) == 4 {
                        v_stx_841_ = lean_ctor_get(v_a_816_, 0);
                        lean_inc(v_stx_841_);
                        lean_dec_ref_known(v_a_816_, 1);
                        v_stx_842_ = lean_ctor_get(v_a_817_, 0);
                        lean_inc(v_stx_842_);
                        lean_dec_ref_known(v_a_817_, 1);
                        v___x_843_ = l_Lean_Syntax_eqWithInfo(v_stx_841_, v_stx_842_);
                        return v___x_843_;
                    } else {
                        lean_dec_ref_known(v_a_816_, 1);
                        lean_dec_ref(v_a_817_);
                        v___x_844_ = 0;
                        return v___x_844_;
                    }
                }
                5 => {
                    if lean_obj_tag(v_a_817_) == 5 {
                        v_stx_845_ = lean_ctor_get(v_a_816_, 0);
                        lean_inc(v_stx_845_);
                        lean_dec_ref_known(v_a_816_, 1);
                        v_stx_846_ = lean_ctor_get(v_a_817_, 0);
                        lean_inc(v_stx_846_);
                        lean_dec_ref_known(v_a_817_, 1);
                        v___x_847_ = l_Lean_Syntax_eqWithInfo(v_stx_845_, v_stx_846_);
                        return v___x_847_;
                    } else {
                        lean_dec_ref_known(v_a_816_, 1);
                        lean_dec_ref(v_a_817_);
                        v___x_848_ = 0;
                        return v___x_848_;
                    }
                }
                6 => {
                    if lean_obj_tag(v_a_817_) == 6 {
                        v_stx_849_ = lean_ctor_get(v_a_816_, 0);
                        lean_inc(v_stx_849_);
                        lean_dec_ref_known(v_a_816_, 2);
                        v_stx_850_ = lean_ctor_get(v_a_817_, 0);
                        lean_inc(v_stx_850_);
                        lean_dec_ref_known(v_a_817_, 2);
                        v___x_851_ = l_Lean_Syntax_eqWithInfo(v_stx_849_, v_stx_850_);
                        return v___x_851_;
                    } else {
                        lean_dec_ref_known(v_a_816_, 2);
                        lean_dec_ref(v_a_817_);
                        v___x_852_ = 0;
                        return v___x_852_;
                    }
                }
                7 => {
                    if lean_obj_tag(v_a_817_) == 7 {
                        v_stx_853_ = lean_ctor_get(v_a_816_, 0);
                        lean_inc(v_stx_853_);
                        lean_dec_ref_known(v_a_816_, 3);
                        v_stx_854_ = lean_ctor_get(v_a_817_, 0);
                        lean_inc(v_stx_854_);
                        lean_dec_ref_known(v_a_817_, 3);
                        v___x_855_ = l_Lean_Syntax_eqWithInfo(v_stx_853_, v_stx_854_);
                        return v___x_855_;
                    } else {
                        lean_dec_ref_known(v_a_816_, 3);
                        lean_dec_ref(v_a_817_);
                        v___x_856_ = 0;
                        return v___x_856_;
                    }
                }
                8 => {
                    if lean_obj_tag(v_a_817_) == 8 {
                        v_stx_857_ = lean_ctor_get(v_a_816_, 0);
                        lean_inc(v_stx_857_);
                        lean_dec_ref_known(v_a_816_, 1);
                        v_stx_858_ = lean_ctor_get(v_a_817_, 0);
                        lean_inc(v_stx_858_);
                        lean_dec_ref_known(v_a_817_, 1);
                        v___x_859_ = l_Lean_Syntax_eqWithInfo(v_stx_857_, v_stx_858_);
                        return v___x_859_;
                    } else {
                        lean_dec_ref_known(v_a_816_, 1);
                        lean_dec_ref(v_a_817_);
                        v___x_860_ = 0;
                        return v___x_860_;
                    }
                }
                _ => {
                    if lean_obj_tag(v_a_817_) == 1 {
                        v_stx_861_ = lean_ctor_get(v_a_816_, 0);
                        lean_inc(v_stx_861_);
                        v_id_862_ = lean_ctor_get(v_a_816_, 1);
                        lean_inc(v_id_862_);
                        lean_dec_ref(v_a_816_);
                        v_stx_863_ = lean_ctor_get(v_a_817_, 0);
                        lean_inc(v_stx_863_);
                        v_id_864_ = lean_ctor_get(v_a_817_, 1);
                        lean_inc(v_id_864_);
                        lean_dec_ref_known(v_a_817_, 4);
                        v___x_865_ = l_Lean_Syntax_eqWithInfo(v_stx_861_, v_stx_863_);
                        if v___x_865_ == 0 {
                            lean_dec(v_id_864_);
                            lean_dec(v_id_862_);
                            return v___x_865_;
                        } else {
                            v___x_866_ = lean_name_eq(v_id_862_, v_id_864_);
                            lean_dec(v_id_864_);
                            lean_dec(v_id_862_);
                            return v___x_866_;
                        }
                    } else {
                        lean_dec_ref(v_a_817_);
                        lean_dec_ref(v_a_816_);
                        v___x_867_ = 0;
                        return v___x_867_;
                    }
                }
            },
            1 => {
                if v___y_836_ == 0 {
                    lean_dec(v_structName_834_);
                    lean_dec(v_structName_831_);
                    return v___y_836_;
                } else {
                    v___x_837_ = lean_name_eq(v_structName_831_, v_structName_834_);
                    lean_dec(v_structName_834_);
                    lean_dec(v_structName_831_);
                    return v___x_837_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_eq___boxed(
    mut v_a_868_: *mut LeanObject,
    mut v_a_869_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_870_: u8 = 0;
    let mut v_r_871_: *mut LeanObject = core::ptr::null_mut();
    v_res_870_ = l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_eq(v_a_868_, v_a_869_);
    v_r_871_ = lean_box((v_res_870_) as usize);
    return v_r_871_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_spec__0(
    mut v_a_872_: *mut LeanObject,
    mut v_as_873_: *mut LeanObject,
    mut v_i_874_: usize,
    mut v_stop_875_: usize,
) -> u8 {
    let mut v___x_876_: u8 = 0;
    let mut v___x_877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_info_878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_info_879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_880_: u8 = 0;
    let mut v___x_881_: usize = 0;
    let mut v___x_882_: usize = 0;
    let mut v___x_884_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_876_ = lean_usize_dec_eq(v_i_874_, v_stop_875_);
                if v___x_876_ == 0 {
                    v___x_877_ = lean_array_uget_borrowed(v_as_873_, v_i_874_);
                    v_info_878_ = lean_ctor_get(v___x_877_, 2);
                    v_info_879_ = lean_ctor_get(v_a_872_, 2);
                    lean_inc_ref(v_info_879_);
                    lean_inc_ref(v_info_878_);
                    v___x_880_ = l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_eq(v_info_878_, v_info_879_);
                    if v___x_880_ == 0 {
                        v___x_881_ = 1usize;
                        v___x_882_ = lean_usize_add(v_i_874_, v___x_881_);
                        v_i_874_ = v___x_882_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_a_872_);
                        return v___x_880_;
                    }
                } else {
                    lean_dec_ref(v_a_872_);
                    v___x_884_ = 0;
                    return v___x_884_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_spec__0___boxed(
    mut v_a_885_: *mut LeanObject,
    mut v_as_886_: *mut LeanObject,
    mut v_i_887_: *mut LeanObject,
    mut v_stop_888_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_889_: usize = 0;
    let mut v_stop_boxed_890_: usize = 0;
    let mut v_res_891_: u8 = 0;
    let mut v_r_892_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_889_ = lean_unbox_usize(v_i_887_);
    lean_dec(v_i_887_);
    v_stop_boxed_890_ = lean_unbox_usize(v_stop_888_);
    lean_dec(v_stop_888_);
    v_res_891_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_spec__0(v_a_885_, v_as_886_, v_i_boxed_889_, v_stop_boxed_890_);
    lean_dec_ref(v_as_886_);
    v_r_892_ = lean_box((v_res_891_) as usize);
    return v_r_892_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_spec__1(
    mut v_as_893_: *mut LeanObject,
    mut v_sz_894_: usize,
    mut v_i_895_: usize,
    mut v_b_896_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_899_: usize = 0;
    let mut v___x_900_: usize = 0;
    let mut v___x_902_: u8 = 0;
    let mut v_a_903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_908_: u8 = 0;
    let mut v___x_909_: usize = 0;
    let mut v___x_910_: usize = 0;
    let mut v___x_911_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_902_ = lean_usize_dec_lt(v_i_895_, v_sz_894_);
                if v___x_902_ == 0 {
                    return v_b_896_;
                } else {
                    v_a_903_ = lean_array_uget_borrowed(v_as_893_, v_i_895_);
                    v___x_906_ = lean_unsigned_to_nat(0);
                    v___x_907_ = lean_array_get_size(v_b_896_);
                    v___x_908_ = lean_nat_dec_lt(v___x_906_, v___x_907_);
                    if v___x_908_ == 0 {
                        state = 2;
                        continue;
                    } else {
                        if v___x_908_ == 0 {
                            state = 2;
                            continue;
                        } else {
                            v___x_909_ = 0usize;
                            v___x_910_ = lean_usize_of_nat(v___x_907_);
                            lean_inc(v_a_903_);
                            v___x_911_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_spec__0(v_a_903_, v_b_896_, v___x_909_, v___x_910_);
                            if v___x_911_ == 0 {
                                state = 2;
                                continue;
                            } else {
                                v_a_898_ = v_b_896_;
                                state = 1;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_899_ = 1usize;
                v___x_900_ = lean_usize_add(v_i_895_, v___x_899_);
                v_i_895_ = v___x_900_;
                v_b_896_ = v_a_898_;
                state = 0;
                continue;
            }
            2 => {
                lean_inc(v_a_903_);
                v___x_905_ = lean_array_push(v_b_896_, v_a_903_);
                v_a_898_ = v___x_905_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_spec__1___boxed(
    mut v_as_912_: *mut LeanObject,
    mut v_sz_913_: *mut LeanObject,
    mut v_i_914_: *mut LeanObject,
    mut v_b_915_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_916_: usize = 0;
    let mut v_i_boxed_917_: usize = 0;
    let mut v_res_918_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_916_ = lean_unbox_usize(v_sz_913_);
    lean_dec(v_sz_913_);
    v_i_boxed_917_ = lean_unbox_usize(v_i_914_);
    lean_dec(v_i_914_);
    v_res_918_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_spec__1(v_as_912_, v_sz_boxed_916_, v_i_boxed_917_, v_b_915_);
    lean_dec_ref(v_as_912_);
    return v_res_918_;
}
pub unsafe fn l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos(
    mut v_infos_921_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_deduplicatedInfos_922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_923_: usize = 0;
    let mut v___x_924_: usize = 0;
    let mut v___x_925_: *mut LeanObject = core::ptr::null_mut();
    v_deduplicatedInfos_922_ = l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos___closed__0;
    v_sz_923_ = lean_array_size(v_infos_921_);
    v___x_924_ = 0usize;
    v___x_925_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_spec__1(v_infos_921_, v_sz_923_, v___x_924_, v_deduplicatedInfos_922_);
    return v___x_925_;
}
pub unsafe fn l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos___boxed(
    mut v_infos_926_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_927_: *mut LeanObject = core::ptr::null_mut();
    v_res_927_ = l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos(v_infos_926_);
    lean_dec_ref(v_infos_926_);
    return v_res_927_;
}
pub unsafe fn l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_containsHoverPos(
    mut v_hoverPos_928_: *mut LeanObject,
    mut v_i_929_: *mut LeanObject,
) -> u8 {
    let mut v___x_931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_932_: u8 = 0;
    let mut v_id_x3f_934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stx_935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_936_: u8 = 0;
    let mut v___x_937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_939_: u8 = 0;
    let mut v___x_940_: u8 = 0;
    let mut v___x_941_: u8 = 0;
    let mut v_stx_942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_945_: u8 = 0;
    let mut v___x_946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_948_: u8 = 0;
    let mut v___x_949_: u8 = 0;
    let mut v___x_950_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_i_929_) == 5 {
                    v_stx_942_ = lean_ctor_get(v_i_929_, 0);
                    v___x_943_ = lean_unsigned_to_nat(1);
                    v___x_944_ = l_Lean_Syntax_getArg(v_stx_942_, v___x_943_);
                    v___x_945_ = l_Lean_Syntax_isMissing(v___x_944_);
                    lean_dec(v___x_944_);
                    if v___x_945_ == 0 {
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_stx_942_);
                        lean_dec_ref_known(v_i_929_, 1);
                        v___x_946_ = l_Lean_Syntax_getRangeWithTrailing_x3f(v_stx_942_, v___x_945_);
                        lean_dec(v_stx_942_);
                        if lean_obj_tag(v___x_946_) == 1 {
                            v_val_947_ = lean_ctor_get(v___x_946_, 0);
                            lean_inc(v_val_947_);
                            lean_dec_ref_known(v___x_946_, 1);
                            v___x_948_ = 0;
                            v___x_949_ = l_Lean_Syntax_Range_contains(
                                v_val_947_,
                                v_hoverPos_928_,
                                v___x_948_,
                            );
                            lean_dec(v_val_947_);
                            return v___x_949_;
                        } else {
                            lean_dec(v___x_946_);
                            v___x_950_ = 0;
                            return v___x_950_;
                        }
                    }
                } else {
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_931_ = lean_alloc_ctor(8, 1, (0) as u32);
                lean_ctor_set(v___x_931_, 0, v_i_929_);
                v___x_932_ = l_Lean_Elab_Info_occursInOrOnBoundary(v___x_931_, v_hoverPos_928_);
                lean_dec_ref_known(v___x_931_, 1);
                return v___x_932_;
            }
            2 => {
                if lean_obj_tag(v_i_929_) == 7 {
                    v_id_x3f_934_ = lean_ctor_get(v_i_929_, 1);
                    if lean_obj_tag(v_id_x3f_934_) == 0 {
                        v_stx_935_ = lean_ctor_get(v_i_929_, 0);
                        lean_inc(v_stx_935_);
                        lean_dec_ref_known(v_i_929_, 3);
                        v___x_936_ = 1;
                        v___x_937_ = l_Lean_Syntax_getRangeWithTrailing_x3f(v_stx_935_, v___x_936_);
                        lean_dec(v_stx_935_);
                        if lean_obj_tag(v___x_937_) == 1 {
                            v_val_938_ = lean_ctor_get(v___x_937_, 0);
                            lean_inc(v_val_938_);
                            lean_dec_ref_known(v___x_937_, 1);
                            v___x_939_ = 0;
                            v___x_940_ = l_Lean_Syntax_Range_contains(
                                v_val_938_,
                                v_hoverPos_928_,
                                v___x_939_,
                            );
                            lean_dec(v_val_938_);
                            return v___x_940_;
                        } else {
                            lean_dec(v___x_937_);
                            v___x_941_ = 0;
                            return v___x_941_;
                        }
                    } else {
                        state = 1;
                        continue;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_containsHoverPos___boxed(
    mut v_hoverPos_951_: *mut LeanObject,
    mut v_i_952_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_953_: u8 = 0;
    let mut v_r_954_: *mut LeanObject = core::ptr::null_mut();
    v_res_953_ = l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_containsHoverPos(v_hoverPos_951_, v_i_952_);
    lean_dec(v_hoverPos_951_);
    v_r_954_ = lean_box((v_res_953_) as usize);
    return v_r_954_;
}
pub unsafe fn l_panic___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go_spec__0(
    mut v_msg_955_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut LeanObject = core::ptr::null_mut();
    v___x_956_ = lean_unsigned_to_nat(0);
    v___x_957_ = lean_panic_fn_borrowed(v___x_956_, v_msg_955_);
    return v___x_957_;
}
pub unsafe fn _init_l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__3()
-> *mut LeanObject {
    let mut v___x_961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_966_: *mut LeanObject = core::ptr::null_mut();
    v___x_961_ = l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__2;
    v___x_962_ = lean_unsigned_to_nat(14);
    v___x_963_ = lean_unsigned_to_nat(22);
    v___x_964_ = l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__1;
    v___x_965_ = l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__0;
    v___x_966_ =
        l_mkPanicMessageWithDecl(v___x_965_, v___x_964_, v___x_963_, v___x_962_, v___x_961_);
    return v___x_966_;
}
pub unsafe fn l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go(
    mut v_fileMap_967_: *mut LeanObject,
    mut v_hoverPos_968_: *mut LeanObject,
    mut v_hoverLine_969_: *mut LeanObject,
    mut v_ctx_970_: *mut LeanObject,
    mut v_info_971_: *mut LeanObject,
    mut v_best_972_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_978_: u8 = 0;
    let mut v___x_979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_981_: u8 = 0;
    let mut v___y_983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_line_987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_line_989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_990_: u8 = 0;
    let mut v___y_992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_994_: u8 = 0;
    let mut v___x_995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1007_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_info_971_) == 8 {
                    v_i_973_ = lean_ctor_get(v_info_971_, 0);
                    lean_inc_ref_n(v_i_973_, 2);
                    v___x_981_ = l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_containsHoverPos(v_hoverPos_968_, v_i_973_);
                    if v___x_981_ == 0 {
                        lean_dec_ref(v_i_973_);
                        lean_dec_ref_known(v_info_971_, 1);
                        lean_dec_ref(v_ctx_970_);
                        lean_dec_ref(v_fileMap_967_);
                        return v_best_972_;
                    } else {
                        v___x_1004_ = l_Lean_Elab_Info_pos_x3f(v_info_971_);
                        if lean_obj_tag(v___x_1004_) == 0 {
                            v___x_1005_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__3_once), _init_l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__3);
                            v___x_1006_ = l_panic___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go_spec__0(v___x_1005_);
                            v___y_999_ = v___x_1006_;
                            state = 4;
                            continue;
                        } else {
                            v_val_1007_ = lean_ctor_get(v___x_1004_, 0);
                            lean_inc(v_val_1007_);
                            lean_dec_ref_known(v___x_1004_, 1);
                            v___y_999_ = v_val_1007_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_info_971_);
                    lean_dec_ref(v_ctx_970_);
                    lean_dec_ref(v_fileMap_967_);
                    return v_best_972_;
                }
            }
            1 => {
                v___x_978_ = lean_nat_dec_eq(v___y_977_, v___y_976_);
                lean_dec(v___y_976_);
                lean_dec(v___y_977_);
                if v___x_978_ == 0 {
                    lean_dec(v___y_975_);
                    lean_dec_ref(v_i_973_);
                    lean_dec_ref(v_ctx_970_);
                    return v_best_972_;
                } else {
                    v___x_979_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_979_, 0, v___y_975_);
                    lean_ctor_set(v___x_979_, 1, v_ctx_970_);
                    lean_ctor_set(v___x_979_, 2, v_i_973_);
                    v___x_980_ = lean_array_push(v_best_972_, v___x_979_);
                    return v___x_980_;
                }
            }
            2 => {
                lean_inc_ref(v_fileMap_967_);
                v___x_986_ = l_Lean_FileMap_toPosition(v_fileMap_967_, v___y_984_);
                lean_dec(v___y_984_);
                v_line_987_ = lean_ctor_get(v___x_986_, 0);
                lean_inc(v_line_987_);
                lean_dec_ref(v___x_986_);
                v___x_988_ = l_Lean_FileMap_toPosition(v_fileMap_967_, v___y_983_);
                lean_dec(v___y_983_);
                v_line_989_ = lean_ctor_get(v___x_988_, 0);
                lean_inc(v_line_989_);
                lean_dec_ref(v___x_988_);
                v___x_990_ = lean_nat_dec_eq(v_line_987_, v_hoverLine_969_);
                if v___x_990_ == 0 {
                    if v___x_981_ == 0 {
                        v___y_975_ = v___y_985_;
                        v___y_976_ = v_line_989_;
                        v___y_977_ = v_line_987_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_line_989_);
                        lean_dec(v_line_987_);
                        lean_dec(v___y_985_);
                        lean_dec_ref(v_i_973_);
                        lean_dec_ref(v_ctx_970_);
                        return v_best_972_;
                    }
                } else {
                    v___y_975_ = v___y_985_;
                    v___y_976_ = v_line_989_;
                    v___y_977_ = v_line_987_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_994_ = lean_nat_dec_lt(v_hoverPos_968_, v___y_993_);
                if v___x_994_ == 0 {
                    v___x_995_ = lean_box(0);
                    v___y_983_ = v___y_993_;
                    v___y_984_ = v___y_992_;
                    v___y_985_ = v___x_995_;
                    state = 2;
                    continue;
                } else {
                    v___x_996_ = lean_nat_sub(v_hoverPos_968_, v___y_992_);
                    v___x_997_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_997_, 0, v___x_996_);
                    v___y_983_ = v___y_993_;
                    v___y_984_ = v___y_992_;
                    v___y_985_ = v___x_997_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                v___x_1000_ = l_Lean_Elab_Info_tailPos_x3f(v_info_971_);
                lean_dec_ref_known(v_info_971_, 1);
                if lean_obj_tag(v___x_1000_) == 0 {
                    v___x_1001_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__3_once), _init_l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__3);
                    v___x_1002_ = l_panic___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go_spec__0(v___x_1001_);
                    v___y_992_ = v___y_999_;
                    v___y_993_ = v___x_1002_;
                    state = 3;
                    continue;
                } else {
                    v_val_1003_ = lean_ctor_get(v___x_1000_, 0);
                    lean_inc(v_val_1003_);
                    lean_dec_ref_known(v___x_1000_, 1);
                    v___y_992_ = v___y_999_;
                    v___y_993_ = v_val_1003_;
                    state = 3;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___boxed(
    mut v_fileMap_1008_: *mut LeanObject,
    mut v_hoverPos_1009_: *mut LeanObject,
    mut v_hoverLine_1010_: *mut LeanObject,
    mut v_ctx_1011_: *mut LeanObject,
    mut v_info_1012_: *mut LeanObject,
    mut v_best_1013_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1014_: *mut LeanObject = core::ptr::null_mut();
    v_res_1014_ = l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go(v_fileMap_1008_, v_hoverPos_1009_, v_hoverLine_1010_, v_ctx_1011_, v_info_1012_, v_best_1013_);
    lean_dec(v_hoverLine_1010_);
    lean_dec(v_hoverPos_1009_);
    return v_res_1014_;
}
pub unsafe fn l_Lean_Server_Completion_findCompletionInfosAt(
    mut v_fileMap_1015_: *mut LeanObject,
    mut v_hoverPos_1016_: *mut LeanObject,
    mut v_cmdStx_1017_: *mut LeanObject,
    mut v_infoTree_1018_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isComplete_1020_: u8 = 0;
    let mut v_completionInfoCandidates_1021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_line_1026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_completionInfoCandidates_1030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1032_: u8 = 0;
    let mut v_isComplete_1033_: u8 = 0;
    let mut v_completionInfoCandidates_1034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isComplete_1035_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref_n(v_fileMap_1015_, 2);
                v___x_1025_ = l_Lean_FileMap_toPosition(v_fileMap_1015_, v_hoverPos_1016_);
                v_line_1026_ = lean_ctor_get(v___x_1025_, 0);
                lean_inc(v_line_1026_);
                lean_dec_ref(v___x_1025_);
                lean_inc(v_hoverPos_1016_);
                v___x_1027_ = lean_alloc_closure(l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___boxed as *mut core::ffi::c_void, 6, 3);
                lean_closure_set(v___x_1027_, 0, v_fileMap_1015_);
                lean_closure_set(v___x_1027_, 1, v_hoverPos_1016_);
                lean_closure_set(v___x_1027_, 2, v_line_1026_);
                v___x_1028_ = lean_unsigned_to_nat(0);
                v___x_1029_ = l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos___closed__0;
                lean_inc_ref(v_infoTree_1018_);
                v_completionInfoCandidates_1030_ = l_Lean_Elab_InfoTree_foldInfo___redArg(
                    v___x_1027_,
                    v___x_1029_,
                    v_infoTree_1018_,
                );
                v___x_1031_ = lean_array_get_size(v_completionInfoCandidates_1030_);
                v___x_1032_ = lean_nat_dec_eq(v___x_1031_, v___x_1028_);
                if v___x_1032_ == 0 {
                    lean_dec_ref(v_infoTree_1018_);
                    lean_dec(v_cmdStx_1017_);
                    lean_dec(v_hoverPos_1016_);
                    lean_dec_ref(v_fileMap_1015_);
                    v_isComplete_1033_ = 1;
                    v_isComplete_1020_ = v_isComplete_1033_;
                    v_completionInfoCandidates_1021_ = v_completionInfoCandidates_1030_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v_completionInfoCandidates_1030_);
                    v_completionInfoCandidates_1034_ =
                        l_Lean_Server_Completion_findSyntheticCompletions(
                            v_fileMap_1015_,
                            v_hoverPos_1016_,
                            v_cmdStx_1017_,
                            v_infoTree_1018_,
                        );
                    v_isComplete_1035_ = 0;
                    v_isComplete_1020_ = v_isComplete_1035_;
                    v_completionInfoCandidates_1021_ = v_completionInfoCandidates_1034_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1022_ = l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos(v_completionInfoCandidates_1021_);
                lean_dec_ref(v_completionInfoCandidates_1021_);
                v___x_1023_ = lean_box((v_isComplete_1020_) as usize);
                v___x_1024_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1024_, 0, v___x_1022_);
                lean_ctor_set(v___x_1024_, 1, v___x_1023_);
                return v___x_1024_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions___lam__0(
    mut v_x_1036_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_1037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1040_: u8 = 0;
    let mut v_info_1041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1043_: u8 = 0;
    let mut v___x_1044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x3f_1045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1050_: u8 = 0;
    let mut v___x_1051_: u8 = 0;
    let mut v_isSharedCheck_1052_: u8 = 0;
    let mut v_unused_1053_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_1037_ = lean_ctor_get(v_x_1036_, 0);
                v_isSharedCheck_1052_ = (!lean_is_exclusive(v_x_1036_)) as u8;
                if v_isSharedCheck_1052_ == 0 {
                    v_unused_1053_ = lean_ctor_get(v_x_1036_, 1);
                    lean_dec(v_unused_1053_);
                    v___x_1039_ = v_x_1036_;
                    v_isShared_1040_ = v_isSharedCheck_1052_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_fst_1037_);
                    lean_dec(v_x_1036_);
                    v___x_1039_ = lean_box(0);
                    v_isShared_1040_ = v_isSharedCheck_1052_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_info_1041_ = lean_ctor_get(v_fst_1037_, 2);
                lean_inc_ref(v_info_1041_);
                lean_dec(v_fst_1037_);
                if lean_obj_tag(v_info_1041_) == 1 {
                    v___x_1050_ = 1;
                    v___y_1043_ = v___x_1050_;
                    state = 2;
                    continue;
                } else {
                    v___x_1051_ = 0;
                    v___y_1043_ = v___x_1051_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1044_ = lean_alloc_ctor(8, 1, (0) as u32);
                lean_ctor_set(v___x_1044_, 0, v_info_1041_);
                v_size_x3f_1045_ = l_Lean_Elab_Info_size_x3f(v___x_1044_);
                lean_dec_ref_known(v___x_1044_, 1);
                v___x_1046_ = lean_box((v___y_1043_) as usize);
                if v_isShared_1040_ == 0 {
                    lean_ctor_set(v___x_1039_, 1, v_size_x3f_1045_);
                    lean_ctor_set(v___x_1039_, 0, v___x_1046_);
                    v___x_1048_ = v___x_1039_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1049_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1049_, 0, v___x_1046_);
                    lean_ctor_set(v_reuseFailAlloc_1049_, 1, v_size_x3f_1045_);
                    v___x_1048_ = v_reuseFailAlloc_1049_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1048_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__3(
    mut v_x_1054_: *mut LeanObject,
    mut v_x_1055_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_1056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1060_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1055_) == 0 {
                    return v_x_1054_;
                } else {
                    v_key_1056_ = lean_ctor_get(v_x_1055_, 0);
                    v_value_1057_ = lean_ctor_get(v_x_1055_, 1);
                    v_tail_1058_ = lean_ctor_get(v_x_1055_, 2);
                    lean_inc(v_value_1057_);
                    lean_inc(v_key_1056_);
                    v___x_1059_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1059_, 0, v_key_1056_);
                    lean_ctor_set(v___x_1059_, 1, v_value_1057_);
                    v___x_1060_ = lean_array_push(v_x_1054_, v___x_1059_);
                    v_x_1054_ = v___x_1060_;
                    v_x_1055_ = v_tail_1058_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__3___boxed(
    mut v_x_1062_: *mut LeanObject,
    mut v_x_1063_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1064_: *mut LeanObject = core::ptr::null_mut();
    v_res_1064_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__3(v_x_1062_, v_x_1063_);
    lean_dec(v_x_1063_);
    return v_res_1064_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__4(
    mut v_as_1065_: *mut LeanObject,
    mut v_i_1066_: usize,
    mut v_stop_1067_: usize,
    mut v_b_1068_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1069_: u8 = 0;
    let mut v___x_1070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: usize = 0;
    let mut v___x_1073_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1069_ = lean_usize_dec_eq(v_i_1066_, v_stop_1067_);
                if v___x_1069_ == 0 {
                    v___x_1070_ = lean_array_uget_borrowed(v_as_1065_, v_i_1066_);
                    v___x_1071_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__3(v_b_1068_, v___x_1070_);
                    v___x_1072_ = 1usize;
                    v___x_1073_ = lean_usize_add(v_i_1066_, v___x_1072_);
                    v_i_1066_ = v___x_1073_;
                    v_b_1068_ = v___x_1071_;
                    state = 0;
                    continue;
                } else {
                    return v_b_1068_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__4___boxed(
    mut v_as_1075_: *mut LeanObject,
    mut v_i_1076_: *mut LeanObject,
    mut v_stop_1077_: *mut LeanObject,
    mut v_b_1078_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1079_: usize = 0;
    let mut v_stop_boxed_1080_: usize = 0;
    let mut v_res_1081_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1079_ = lean_unbox_usize(v_i_1076_);
    lean_dec(v_i_1076_);
    v_stop_boxed_1080_ = lean_unbox_usize(v_stop_1077_);
    lean_dec(v_stop_1077_);
    v_res_1081_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__4(v_as_1075_, v_i_boxed_1079_, v_stop_boxed_1080_, v_b_1078_);
    lean_dec_ref(v_as_1075_);
    return v_res_1081_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__0(
    mut v_sz_1082_: usize,
    mut v_i_1083_: usize,
    mut v_bs_1084_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1085_: u8 = 0;
    let mut v_v_1086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: usize = 0;
    let mut v___x_1091_: usize = 0;
    let mut v___x_1092_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1085_ = lean_usize_dec_lt(v_i_1083_, v_sz_1082_);
                if v___x_1085_ == 0 {
                    return v_bs_1084_;
                } else {
                    v_v_1086_ = lean_array_uget_borrowed(v_bs_1084_, v_i_1083_);
                    v_snd_1087_ = lean_ctor_get(v_v_1086_, 1);
                    lean_inc(v_snd_1087_);
                    v___x_1088_ = lean_unsigned_to_nat(0);
                    v_bs_x27_1089_ = lean_array_uset(v_bs_1084_, v_i_1083_, v___x_1088_);
                    v___x_1090_ = 1usize;
                    v___x_1091_ = lean_usize_add(v_i_1083_, v___x_1090_);
                    v___x_1092_ = lean_array_uset(v_bs_x27_1089_, v_i_1083_, v_snd_1087_);
                    v_i_1083_ = v___x_1091_;
                    v_bs_1084_ = v___x_1092_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__0___boxed(
    mut v_sz_1094_: *mut LeanObject,
    mut v_i_1095_: *mut LeanObject,
    mut v_bs_1096_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1097_: usize = 0;
    let mut v_i_boxed_1098_: usize = 0;
    let mut v_res_1099_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1097_ = lean_unbox_usize(v_sz_1094_);
    lean_dec(v_sz_1094_);
    v_i_boxed_1098_ = lean_unbox_usize(v_i_1095_);
    lean_dec(v_i_1095_);
    v_res_1099_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__0(v_sz_boxed_1097_, v_i_boxed_1098_, v_bs_1096_);
    return v_res_1099_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1___redArg(
    mut v_hi_1100_: *mut LeanObject,
    mut v_pivot_1101_: *mut LeanObject,
    mut v_as_1102_: *mut LeanObject,
    mut v_i_1103_: *mut LeanObject,
    mut v_k_1104_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1115_: u8 = 0;
    let mut v___x_1116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1128_: u8 = 0;
    let mut v___x_1130_: u8 = 0;
    let mut v___x_1131_: u8 = 0;
    let mut v___x_1132_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1115_ = lean_nat_dec_lt(v_k_1104_, v_hi_1100_);
                if v___x_1115_ == 0 {
                    lean_dec(v_k_1104_);
                    v___x_1116_ = lean_array_fswap(v_as_1102_, v_i_1103_, v_hi_1100_);
                    v___x_1117_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1117_, 0, v_i_1103_);
                    lean_ctor_set(v___x_1117_, 1, v___x_1116_);
                    return v___x_1117_;
                } else {
                    v___x_1118_ = lean_array_fget_borrowed(v_as_1102_, v_k_1104_);
                    v_fst_1119_ = lean_ctor_get(v___x_1118_, 0);
                    v_fst_1120_ = lean_ctor_get(v_pivot_1101_, 0);
                    v_fst_1121_ = lean_ctor_get(v_fst_1119_, 0);
                    v_snd_1122_ = lean_ctor_get(v_fst_1119_, 1);
                    v_fst_1123_ = lean_ctor_get(v_fst_1120_, 0);
                    v_snd_1124_ = lean_ctor_get(v_fst_1120_, 1);
                    if lean_obj_tag(v_snd_1122_) == 0 {
                        if lean_obj_tag(v_snd_1124_) == 1 {
                            state = 1;
                            continue;
                        } else {
                            state = 4;
                            continue;
                        }
                    } else {
                        if lean_obj_tag(v_snd_1124_) == 0 {
                            state = 2;
                            continue;
                        } else {
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1106_ = lean_unsigned_to_nat(1);
                v___x_1107_ = lean_nat_add(v_k_1104_, v___x_1106_);
                lean_dec(v_k_1104_);
                v_k_1104_ = v___x_1107_;
                state = 0;
                continue;
            }
            2 => {
                v___x_1110_ = lean_array_fswap(v_as_1102_, v_i_1103_, v_k_1104_);
                v___x_1111_ = lean_unsigned_to_nat(1);
                v___x_1112_ = lean_nat_add(v_i_1103_, v___x_1111_);
                lean_dec(v_i_1103_);
                v___x_1113_ = lean_nat_add(v_k_1104_, v___x_1111_);
                lean_dec(v_k_1104_);
                v_as_1102_ = v___x_1110_;
                v_i_1103_ = v___x_1112_;
                v_k_1104_ = v___x_1113_;
                state = 0;
                continue;
            }
            3 => {
                if lean_obj_tag(v_snd_1122_) == 1 {
                    if lean_obj_tag(v_snd_1124_) == 1 {
                        v_val_1126_ = lean_ctor_get(v_snd_1122_, 0);
                        v_val_1127_ = lean_ctor_get(v_snd_1124_, 0);
                        v___x_1128_ = lean_nat_dec_lt(v_val_1126_, v_val_1127_);
                        if v___x_1128_ == 0 {
                            state = 1;
                            continue;
                        } else {
                            state = 2;
                            continue;
                        }
                    } else {
                        state = 1;
                        continue;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            4 => {
                v___x_1130_ = (lean_unbox(v_fst_1121_) as u8);
                if v___x_1130_ == 0 {
                    v___x_1131_ = (lean_unbox(v_fst_1123_) as u8);
                    if v___x_1131_ == 1 {
                        state = 2;
                        continue;
                    } else {
                        state = 3;
                        continue;
                    }
                } else {
                    v___x_1132_ = (lean_unbox(v_fst_1123_) as u8);
                    if v___x_1132_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        state = 3;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1___redArg___boxed(
    mut v_hi_1133_: *mut LeanObject,
    mut v_pivot_1134_: *mut LeanObject,
    mut v_as_1135_: *mut LeanObject,
    mut v_i_1136_: *mut LeanObject,
    mut v_k_1137_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1138_: *mut LeanObject = core::ptr::null_mut();
    v_res_1138_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1___redArg(v_hi_1133_, v_pivot_1134_, v_as_1135_, v_i_1136_, v_k_1137_);
    lean_dec_ref(v_pivot_1134_);
    lean_dec(v_hi_1133_);
    return v_res_1138_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg___lam__0(
    mut v___x_1139_: u8,
    mut v_x_1140_: *mut LeanObject,
    mut v_x_1141_: *mut LeanObject,
) -> u8 {
    let mut v_fst_1142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: u8 = 0;
    let mut v___x_1152_: u8 = 0;
    let mut v___x_1153_: u8 = 0;
    let mut v___x_1155_: u8 = 0;
    let mut v___x_1156_: u8 = 0;
    let mut v___x_1157_: u8 = 0;
    let mut v___x_1158_: u8 = 0;
    let mut v___x_1159_: u8 = 0;
    let mut v___x_1160_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_1142_ = lean_ctor_get(v_x_1140_, 0);
                v_fst_1143_ = lean_ctor_get(v_x_1141_, 0);
                v_fst_1144_ = lean_ctor_get(v_fst_1142_, 0);
                v_snd_1145_ = lean_ctor_get(v_fst_1142_, 1);
                v_fst_1146_ = lean_ctor_get(v_fst_1143_, 0);
                v_snd_1147_ = lean_ctor_get(v_fst_1143_, 1);
                if lean_obj_tag(v_snd_1145_) == 0 {
                    if lean_obj_tag(v_snd_1147_) == 1 {
                        v___x_1160_ = 0;
                        return v___x_1160_;
                    } else {
                        state = 2;
                        continue;
                    }
                } else {
                    if lean_obj_tag(v_snd_1147_) == 0 {
                        return v___x_1139_;
                    } else {
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_snd_1145_) == 1 {
                    if lean_obj_tag(v_snd_1147_) == 1 {
                        v_val_1149_ = lean_ctor_get(v_snd_1145_, 0);
                        v_val_1150_ = lean_ctor_get(v_snd_1147_, 0);
                        v___x_1151_ = lean_nat_dec_lt(v_val_1149_, v_val_1150_);
                        return v___x_1151_;
                    } else {
                        v___x_1152_ = 0;
                        return v___x_1152_;
                    }
                } else {
                    v___x_1153_ = 0;
                    return v___x_1153_;
                }
            }
            2 => {
                v___x_1155_ = (lean_unbox(v_fst_1144_) as u8);
                if v___x_1155_ == 0 {
                    v___x_1156_ = (lean_unbox(v_fst_1146_) as u8);
                    if v___x_1156_ == 1 {
                        v___x_1157_ = (lean_unbox(v_fst_1146_) as u8);
                        return v___x_1157_;
                    } else {
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_1158_ = (lean_unbox(v_fst_1146_) as u8);
                    if v___x_1158_ == 0 {
                        v___x_1159_ = (lean_unbox(v_fst_1146_) as u8);
                        return v___x_1159_;
                    } else {
                        state = 1;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg___lam__0___boxed(
    mut v___x_1161_: *mut LeanObject,
    mut v_x_1162_: *mut LeanObject,
    mut v_x_1163_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2350__boxed_1164_: u8 = 0;
    let mut v_res_1165_: u8 = 0;
    let mut v_r_1166_: *mut LeanObject = core::ptr::null_mut();
    v___x_2350__boxed_1164_ = (lean_unbox(v___x_1161_) as u8);
    v_res_1165_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg___lam__0(v___x_2350__boxed_1164_, v_x_1162_, v_x_1163_);
    lean_dec_ref(v_x_1163_);
    lean_dec_ref(v_x_1162_);
    v_r_1166_ = lean_box((v_res_1165_) as usize);
    return v_r_1166_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg(
    mut v_n_1167_: *mut LeanObject,
    mut v_as_1168_: *mut LeanObject,
    mut v_lo_1169_: *mut LeanObject,
    mut v_hi_1170_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pivot_1173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1177_: u8 = 0;
    let mut v___x_1178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1182_: u8 = 0;
    let mut v___x_1183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mid_1185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: u8 = 0;
    let mut v___x_1191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1196_: u8 = 0;
    let mut v___x_1197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: u8 = 0;
    let mut v___x_1201_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1182_ = lean_nat_dec_lt(v_lo_1169_, v_hi_1170_);
                if v___x_1182_ == 0 {
                    lean_dec(v_lo_1169_);
                    return v_as_1168_;
                } else {
                    v___x_1183_ = lean_nat_add(v_lo_1169_, v_hi_1170_);
                    v___x_1184_ = lean_unsigned_to_nat(1);
                    v_mid_1185_ = lean_nat_shiftr(v___x_1183_, v___x_1184_);
                    lean_dec(v___x_1183_);
                    v___x_1198_ = lean_array_fget_borrowed(v_as_1168_, v_mid_1185_);
                    v___x_1199_ = lean_array_fget_borrowed(v_as_1168_, v_lo_1169_);
                    v___x_1200_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg___lam__0(v___x_1182_, v___x_1198_, v___x_1199_);
                    if v___x_1200_ == 0 {
                        v___y_1193_ = v_as_1168_;
                        state = 3;
                        continue;
                    } else {
                        v___x_1201_ = lean_array_fswap(v_as_1168_, v_lo_1169_, v_mid_1185_);
                        v___y_1193_ = v___x_1201_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_pivot_1173_ = lean_array_fget(v___y_1172_, v_hi_1170_);
                lean_inc_n(v_lo_1169_, 2);
                v___x_1174_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1___redArg(v_hi_1170_, v_pivot_1173_, v___y_1172_, v_lo_1169_, v_lo_1169_);
                lean_dec(v_pivot_1173_);
                v_fst_1175_ = lean_ctor_get(v___x_1174_, 0);
                lean_inc(v_fst_1175_);
                v_snd_1176_ = lean_ctor_get(v___x_1174_, 1);
                lean_inc(v_snd_1176_);
                lean_dec_ref(v___x_1174_);
                v___x_1177_ = lean_nat_dec_le(v_hi_1170_, v_fst_1175_);
                if v___x_1177_ == 0 {
                    v___x_1178_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg(v_n_1167_, v_snd_1176_, v_lo_1169_, v_fst_1175_);
                    v___x_1179_ = lean_unsigned_to_nat(1);
                    v___x_1180_ = lean_nat_add(v_fst_1175_, v___x_1179_);
                    lean_dec(v_fst_1175_);
                    v_as_1168_ = v___x_1178_;
                    v_lo_1169_ = v___x_1180_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_fst_1175_);
                    lean_dec(v_lo_1169_);
                    return v_snd_1176_;
                }
            }
            2 => {
                v___x_1188_ = lean_array_fget_borrowed(v___y_1187_, v_mid_1185_);
                v___x_1189_ = lean_array_fget_borrowed(v___y_1187_, v_hi_1170_);
                v___x_1190_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg___lam__0(v___x_1182_, v___x_1188_, v___x_1189_);
                if v___x_1190_ == 0 {
                    lean_dec(v_mid_1185_);
                    v___y_1172_ = v___y_1187_;
                    state = 1;
                    continue;
                } else {
                    v___x_1191_ = lean_array_fswap(v___y_1187_, v_mid_1185_, v_hi_1170_);
                    lean_dec(v_mid_1185_);
                    v___y_1172_ = v___x_1191_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_1194_ = lean_array_fget_borrowed(v___y_1193_, v_hi_1170_);
                v___x_1195_ = lean_array_fget_borrowed(v___y_1193_, v_lo_1169_);
                v___x_1196_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg___lam__0(v___x_1182_, v___x_1194_, v___x_1195_);
                if v___x_1196_ == 0 {
                    v___y_1187_ = v___y_1193_;
                    state = 2;
                    continue;
                } else {
                    v___x_1197_ = lean_array_fswap(v___y_1193_, v_lo_1169_, v_hi_1170_);
                    v___y_1187_ = v___x_1197_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg___boxed(
    mut v_n_1202_: *mut LeanObject,
    mut v_as_1203_: *mut LeanObject,
    mut v_lo_1204_: *mut LeanObject,
    mut v_hi_1205_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1206_: *mut LeanObject = core::ptr::null_mut();
    v_res_1206_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg(v_n_1202_, v_as_1203_, v_lo_1204_, v_hi_1205_);
    lean_dec(v_hi_1205_);
    lean_dec(v_n_1202_);
    return v_res_1206_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5_spec__9_spec__11___redArg(
    mut v_x_1207_: *mut LeanObject,
    mut v_x_1208_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_1209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1214_: u8 = 0;
    let mut v_fst_1215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1219_: u64 = 0;
    let mut v___y_1220_: u64 = 0;
    let mut v___x_1221_: u64 = 0;
    let mut v___x_1222_: u64 = 0;
    let mut v___x_1223_: u64 = 0;
    let mut v_fold_1224_: u64 = 0;
    let mut v___x_1225_: u64 = 0;
    let mut v___x_1226_: u64 = 0;
    let mut v___x_1227_: u64 = 0;
    let mut v___x_1228_: usize = 0;
    let mut v___x_1229_: usize = 0;
    let mut v___x_1230_: usize = 0;
    let mut v___x_1231_: usize = 0;
    let mut v___x_1232_: usize = 0;
    let mut v___x_1233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1240_: u64 = 0;
    let mut v___x_1241_: u64 = 0;
    let mut v_val_1242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1243_: u64 = 0;
    let mut v___x_1244_: u64 = 0;
    let mut v___x_1245_: u64 = 0;
    let mut v___x_1246_: u8 = 0;
    let mut v___x_1247_: u64 = 0;
    let mut v___x_1248_: u64 = 0;
    let mut v_isSharedCheck_1249_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1208_) == 0 {
                    return v_x_1207_;
                } else {
                    v_key_1209_ = lean_ctor_get(v_x_1208_, 0);
                    v_value_1210_ = lean_ctor_get(v_x_1208_, 1);
                    v_tail_1211_ = lean_ctor_get(v_x_1208_, 2);
                    v_isSharedCheck_1249_ = (!lean_is_exclusive(v_x_1208_)) as u8;
                    if v_isSharedCheck_1249_ == 0 {
                        v___x_1213_ = v_x_1208_;
                        v_isShared_1214_ = v_isSharedCheck_1249_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1211_);
                        lean_inc(v_value_1210_);
                        lean_inc(v_key_1209_);
                        lean_dec(v_x_1208_);
                        v___x_1213_ = lean_box(0);
                        v_isShared_1214_ = v_isSharedCheck_1249_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1215_ = lean_ctor_get(v_key_1209_, 0);
                v_snd_1216_ = lean_ctor_get(v_key_1209_, 1);
                v___x_1217_ = lean_array_get_size(v_x_1207_);
                v___x_1246_ = (lean_unbox(v_fst_1215_) as u8);
                if v___x_1246_ == 0 {
                    v___x_1247_ = 13u64;
                    v___y_1240_ = v___x_1247_;
                    state = 4;
                    continue;
                } else {
                    v___x_1248_ = 11u64;
                    v___y_1240_ = v___x_1248_;
                    state = 4;
                    continue;
                }
            }
            2 => {
                v___x_1221_ = lean_uint64_mix_hash(v___y_1219_, v___y_1220_);
                v___x_1222_ = 32u64;
                v___x_1223_ = lean_uint64_shift_right(v___x_1221_, v___x_1222_);
                v_fold_1224_ = lean_uint64_xor(v___x_1221_, v___x_1223_);
                v___x_1225_ = 16u64;
                v___x_1226_ = lean_uint64_shift_right(v_fold_1224_, v___x_1225_);
                v___x_1227_ = lean_uint64_xor(v_fold_1224_, v___x_1226_);
                v___x_1228_ = lean_uint64_to_usize(v___x_1227_);
                v___x_1229_ = lean_usize_of_nat(v___x_1217_);
                v___x_1230_ = 1usize;
                v___x_1231_ = lean_usize_sub(v___x_1229_, v___x_1230_);
                v___x_1232_ = lean_usize_land(v___x_1228_, v___x_1231_);
                v___x_1233_ = lean_array_uget_borrowed(v_x_1207_, v___x_1232_);
                lean_inc(v___x_1233_);
                if v_isShared_1214_ == 0 {
                    lean_ctor_set(v___x_1213_, 2, v___x_1233_);
                    v___x_1235_ = v___x_1213_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1238_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1238_, 0, v_key_1209_);
                    lean_ctor_set(v_reuseFailAlloc_1238_, 1, v_value_1210_);
                    lean_ctor_set(v_reuseFailAlloc_1238_, 2, v___x_1233_);
                    v___x_1235_ = v_reuseFailAlloc_1238_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1236_ = lean_array_uset(v_x_1207_, v___x_1232_, v___x_1235_);
                v_x_1207_ = v___x_1236_;
                v_x_1208_ = v_tail_1211_;
                state = 0;
                continue;
            }
            4 => {
                if lean_obj_tag(v_snd_1216_) == 0 {
                    v___x_1241_ = 11u64;
                    v___y_1219_ = v___y_1240_;
                    v___y_1220_ = v___x_1241_;
                    state = 2;
                    continue;
                } else {
                    v_val_1242_ = lean_ctor_get(v_snd_1216_, 0);
                    v___x_1243_ = l_String_instHashableRaw_hash(v_val_1242_);
                    v___x_1244_ = 13u64;
                    v___x_1245_ = lean_uint64_mix_hash(v___x_1243_, v___x_1244_);
                    v___y_1219_ = v___y_1240_;
                    v___y_1220_ = v___x_1245_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5_spec__9___redArg(
    mut v_i_1250_: *mut LeanObject,
    mut v_source_1251_: *mut LeanObject,
    mut v_target_1252_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: u8 = 0;
    let mut v_es_1255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_1257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_1258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1253_ = lean_array_get_size(v_source_1251_);
                v___x_1254_ = lean_nat_dec_lt(v_i_1250_, v___x_1253_);
                if v___x_1254_ == 0 {
                    lean_dec_ref(v_source_1251_);
                    lean_dec(v_i_1250_);
                    return v_target_1252_;
                } else {
                    v_es_1255_ = lean_array_fget(v_source_1251_, v_i_1250_);
                    v___x_1256_ = lean_box(0);
                    v_source_1257_ = lean_array_fset(v_source_1251_, v_i_1250_, v___x_1256_);
                    v_target_1258_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5_spec__9_spec__11___redArg(v_target_1252_, v_es_1255_);
                    v___x_1259_ = lean_unsigned_to_nat(1);
                    v___x_1260_ = lean_nat_add(v_i_1250_, v___x_1259_);
                    lean_dec(v_i_1250_);
                    v_i_1250_ = v___x_1260_;
                    v_source_1251_ = v_source_1257_;
                    v_target_1252_ = v_target_1258_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5___redArg(
    mut v_data_1262_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_1265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1269_: *mut LeanObject = core::ptr::null_mut();
    v___x_1263_ = lean_array_get_size(v_data_1262_);
    v___x_1264_ = lean_unsigned_to_nat(2);
    v_nbuckets_1265_ = lean_nat_mul(v___x_1263_, v___x_1264_);
    v___x_1266_ = lean_unsigned_to_nat(0);
    v___x_1267_ = lean_box(0);
    v___x_1268_ = lean_mk_array(v_nbuckets_1265_, v___x_1267_);
    v___x_1269_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5_spec__9___redArg(v___x_1266_, v_data_1262_, v___x_1268_);
    return v___x_1269_;
}
pub unsafe fn l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4_spec__7(
    mut v_x_1270_: *mut LeanObject,
    mut v_x_1271_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_1270_) == 0 {
        if lean_obj_tag(v_x_1271_) == 0 {
            let mut v___x_1272_: u8 = 0;
            v___x_1272_ = 1;
            return v___x_1272_;
        } else {
            let mut v___x_1273_: u8 = 0;
            v___x_1273_ = 0;
            return v___x_1273_;
        }
    } else {
        if lean_obj_tag(v_x_1271_) == 0 {
            let mut v___x_1274_: u8 = 0;
            v___x_1274_ = 0;
            return v___x_1274_;
        } else {
            let mut v_val_1275_: *mut LeanObject = core::ptr::null_mut();
            let mut v_val_1276_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1277_: u8 = 0;
            v_val_1275_ = lean_ctor_get(v_x_1270_, 0);
            v_val_1276_ = lean_ctor_get(v_x_1271_, 0);
            v___x_1277_ = lean_nat_dec_eq(v_val_1275_, v_val_1276_);
            return v___x_1277_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4_spec__7___boxed(
    mut v_x_1278_: *mut LeanObject,
    mut v_x_1279_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1280_: u8 = 0;
    let mut v_r_1281_: *mut LeanObject = core::ptr::null_mut();
    v_res_1280_ = l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4_spec__7(v_x_1278_, v_x_1279_);
    lean_dec(v_x_1279_);
    lean_dec(v_x_1278_);
    v_r_1281_ = lean_box((v_res_1280_) as usize);
    return v_r_1281_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4___redArg(
    mut v_a_1282_: *mut LeanObject,
    mut v_x_1283_: *mut LeanObject,
) -> u8 {
    let mut v___x_1284_: u8 = 0;
    let mut v_key_1285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: u8 = 0;
    let mut v___x_1294_: u8 = 0;
    let mut v___x_1295_: u8 = 0;
    let mut v___x_1297_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1283_) == 0 {
                    v___x_1284_ = 0;
                    return v___x_1284_;
                } else {
                    v_key_1285_ = lean_ctor_get(v_x_1283_, 0);
                    v_tail_1286_ = lean_ctor_get(v_x_1283_, 2);
                    v_fst_1287_ = lean_ctor_get(v_key_1285_, 0);
                    v_snd_1288_ = lean_ctor_get(v_key_1285_, 1);
                    v_fst_1289_ = lean_ctor_get(v_a_1282_, 0);
                    v_snd_1290_ = lean_ctor_get(v_a_1282_, 1);
                    v___x_1294_ = (lean_unbox(v_fst_1287_) as u8);
                    if v___x_1294_ == 0 {
                        v___x_1295_ = (lean_unbox(v_fst_1289_) as u8);
                        if v___x_1295_ == 0 {
                            state = 1;
                            continue;
                        } else {
                            v_x_1283_ = v_tail_1286_;
                            state = 0;
                            continue;
                        }
                    } else {
                        v___x_1297_ = (lean_unbox(v_fst_1289_) as u8);
                        if v___x_1297_ == 0 {
                            v_x_1283_ = v_tail_1286_;
                            state = 0;
                            continue;
                        } else {
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1292_ = l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4_spec__7(v_snd_1288_, v_snd_1290_);
                if v___x_1292_ == 0 {
                    v_x_1283_ = v_tail_1286_;
                    state = 0;
                    continue;
                } else {
                    return v___x_1292_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4___redArg___boxed(
    mut v_a_1299_: *mut LeanObject,
    mut v_x_1300_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1301_: u8 = 0;
    let mut v_r_1302_: *mut LeanObject = core::ptr::null_mut();
    v_res_1301_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4___redArg(v_a_1299_, v_x_1300_);
    lean_dec(v_x_1300_);
    lean_dec_ref(v_a_1299_);
    v_r_1302_ = lean_box((v_res_1301_) as usize);
    return v_r_1302_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6___redArg___lam__0(
    mut v_a_1305_: *mut LeanObject,
    mut v_x_1306_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1312_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1306_) == 0 {
                    v___x_1311_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6___redArg___lam__0___closed__0;
                    v___y_1308_ = v___x_1311_;
                    state = 1;
                    continue;
                } else {
                    v_val_1312_ = lean_ctor_get(v_x_1306_, 0);
                    lean_inc(v_val_1312_);
                    lean_dec_ref_known(v_x_1306_, 1);
                    v___y_1308_ = v_val_1312_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1309_ = lean_array_push(v___y_1308_, v_a_1305_);
                v___x_1310_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1310_, 0, v___x_1309_);
                return v___x_1310_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6___redArg(
    mut v_a_1313_: *mut LeanObject,
    mut v_a_1314_: *mut LeanObject,
    mut v_x_1315_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_1320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1325_: u8 = 0;
    let mut v_tail_1327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: u8 = 0;
    let mut v___x_1337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: u8 = 0;
    let mut v___x_1342_: u8 = 0;
    let mut v___x_1343_: u8 = 0;
    let mut v_isSharedCheck_1344_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1315_) == 0 {
                    v___x_1316_ = lean_box(0);
                    v___x_1317_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6___redArg___lam__0(v_a_1313_, v___x_1316_);
                    v_val_1318_ = lean_ctor_get(v___x_1317_, 0);
                    lean_inc(v_val_1318_);
                    lean_dec(v___x_1317_);
                    v___x_1319_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_1319_, 0, v_a_1314_);
                    lean_ctor_set(v___x_1319_, 1, v_val_1318_);
                    lean_ctor_set(v___x_1319_, 2, v_x_1315_);
                    return v___x_1319_;
                } else {
                    v_key_1320_ = lean_ctor_get(v_x_1315_, 0);
                    v_value_1321_ = lean_ctor_get(v_x_1315_, 1);
                    v_tail_1322_ = lean_ctor_get(v_x_1315_, 2);
                    v_isSharedCheck_1344_ = (!lean_is_exclusive(v_x_1315_)) as u8;
                    if v_isSharedCheck_1344_ == 0 {
                        v___x_1324_ = v_x_1315_;
                        v_isShared_1325_ = v_isSharedCheck_1344_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1322_);
                        lean_inc(v_value_1321_);
                        lean_inc(v_key_1320_);
                        lean_dec(v_x_1315_);
                        v___x_1324_ = lean_box(0);
                        v_isShared_1325_ = v_isSharedCheck_1344_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1331_ = lean_ctor_get(v_key_1320_, 0);
                v_snd_1332_ = lean_ctor_get(v_key_1320_, 1);
                v_fst_1333_ = lean_ctor_get(v_a_1314_, 0);
                v_snd_1334_ = lean_ctor_get(v_a_1314_, 1);
                v___x_1341_ = (lean_unbox(v_fst_1331_) as u8);
                if v___x_1341_ == 0 {
                    v___x_1342_ = (lean_unbox(v_fst_1333_) as u8);
                    if v___x_1342_ == 0 {
                        state = 4;
                        continue;
                    } else {
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1343_ = (lean_unbox(v_fst_1333_) as u8);
                    if v___x_1343_ == 0 {
                        state = 2;
                        continue;
                    } else {
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v_tail_1327_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6___redArg(v_a_1313_, v_a_1314_, v_tail_1322_);
                if v_isShared_1325_ == 0 {
                    lean_ctor_set(v___x_1324_, 2, v_tail_1327_);
                    v___x_1329_ = v___x_1324_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1330_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1330_, 0, v_key_1320_);
                    lean_ctor_set(v_reuseFailAlloc_1330_, 1, v_value_1321_);
                    lean_ctor_set(v_reuseFailAlloc_1330_, 2, v_tail_1327_);
                    v___x_1329_ = v_reuseFailAlloc_1330_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1329_;
            }
            4 => {
                v___x_1336_ = l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4_spec__7(v_snd_1332_, v_snd_1334_);
                if v___x_1336_ == 0 {
                    state = 2;
                    continue;
                } else {
                    lean_del_object(v___x_1324_);
                    lean_dec(v_key_1320_);
                    v___x_1337_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1337_, 0, v_value_1321_);
                    v___x_1338_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6___redArg___lam__0(v_a_1313_, v___x_1337_);
                    v_val_1339_ = lean_ctor_get(v___x_1338_, 0);
                    lean_inc(v_val_1339_);
                    lean_dec(v___x_1338_);
                    v___x_1340_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_1340_, 0, v_a_1314_);
                    lean_ctor_set(v___x_1340_, 1, v_val_1339_);
                    lean_ctor_set(v___x_1340_, 2, v_tail_1322_);
                    return v___x_1340_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3___redArg(
    mut v_a_1345_: *mut LeanObject,
    mut v_m_1346_: *mut LeanObject,
    mut v_a_1347_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1351_: usize = 0;
    let mut v___y_1352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_1356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1359_: u8 = 0;
    let mut v_fst_1360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1364_: u64 = 0;
    let mut v___y_1365_: u64 = 0;
    let mut v___x_1366_: u64 = 0;
    let mut v___x_1367_: u64 = 0;
    let mut v___x_1368_: u64 = 0;
    let mut v_fold_1369_: u64 = 0;
    let mut v___x_1370_: u64 = 0;
    let mut v___x_1371_: u64 = 0;
    let mut v___x_1372_: u64 = 0;
    let mut v___x_1373_: usize = 0;
    let mut v___x_1374_: usize = 0;
    let mut v___x_1375_: usize = 0;
    let mut v___x_1376_: usize = 0;
    let mut v___x_1377_: usize = 0;
    let mut v_bkt_1378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: u8 = 0;
    let mut v___x_1380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: u8 = 0;
    let mut v_val_1392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bkt_x27_1401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: u8 = 0;
    let mut v___x_1403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1406_: u64 = 0;
    let mut v___x_1407_: u64 = 0;
    let mut v_val_1408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: u64 = 0;
    let mut v___x_1410_: u64 = 0;
    let mut v___x_1411_: u64 = 0;
    let mut v___x_1412_: u8 = 0;
    let mut v___x_1413_: u64 = 0;
    let mut v___x_1414_: u64 = 0;
    let mut v_isSharedCheck_1415_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1355_ = lean_ctor_get(v_m_1346_, 0);
                v_buckets_1356_ = lean_ctor_get(v_m_1346_, 1);
                v_isSharedCheck_1415_ = (!lean_is_exclusive(v_m_1346_)) as u8;
                if v_isSharedCheck_1415_ == 0 {
                    v___x_1358_ = v_m_1346_;
                    v_isShared_1359_ = v_isSharedCheck_1415_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_buckets_1356_);
                    lean_inc(v_size_1355_);
                    lean_dec(v_m_1346_);
                    v___x_1358_ = lean_box(0);
                    v_isShared_1359_ = v_isSharedCheck_1415_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_1353_ = lean_array_uset(v___y_1350_, v___y_1351_, v___y_1349_);
                v___x_1354_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1354_, 0, v___y_1352_);
                lean_ctor_set(v___x_1354_, 1, v___x_1353_);
                return v___x_1354_;
            }
            2 => {
                v_fst_1360_ = lean_ctor_get(v_a_1347_, 0);
                v_snd_1361_ = lean_ctor_get(v_a_1347_, 1);
                v___x_1362_ = lean_array_get_size(v_buckets_1356_);
                v___x_1412_ = (lean_unbox(v_fst_1360_) as u8);
                if v___x_1412_ == 0 {
                    v___x_1413_ = 13u64;
                    v___y_1406_ = v___x_1413_;
                    state = 6;
                    continue;
                } else {
                    v___x_1414_ = 11u64;
                    v___y_1406_ = v___x_1414_;
                    state = 6;
                    continue;
                }
            }
            3 => {
                v___x_1366_ = lean_uint64_mix_hash(v___y_1364_, v___y_1365_);
                v___x_1367_ = 32u64;
                v___x_1368_ = lean_uint64_shift_right(v___x_1366_, v___x_1367_);
                v_fold_1369_ = lean_uint64_xor(v___x_1366_, v___x_1368_);
                v___x_1370_ = 16u64;
                v___x_1371_ = lean_uint64_shift_right(v_fold_1369_, v___x_1370_);
                v___x_1372_ = lean_uint64_xor(v_fold_1369_, v___x_1371_);
                v___x_1373_ = lean_uint64_to_usize(v___x_1372_);
                v___x_1374_ = lean_usize_of_nat(v___x_1362_);
                v___x_1375_ = 1usize;
                v___x_1376_ = lean_usize_sub(v___x_1374_, v___x_1375_);
                v___x_1377_ = lean_usize_land(v___x_1373_, v___x_1376_);
                v_bkt_1378_ = lean_array_uget_borrowed(v_buckets_1356_, v___x_1377_);
                v___x_1379_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4___redArg(v_a_1347_, v_bkt_1378_);
                if v___x_1379_ == 0 {
                    v___x_1380_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6___redArg___lam__0___closed__0;
                    v___x_1381_ = lean_array_push(v___x_1380_, v_a_1345_);
                    v___x_1382_ = lean_unsigned_to_nat(1);
                    v_size_x27_1383_ = lean_nat_add(v_size_1355_, v___x_1382_);
                    lean_dec(v_size_1355_);
                    lean_inc(v_bkt_1378_);
                    v___x_1384_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_1384_, 0, v_a_1347_);
                    lean_ctor_set(v___x_1384_, 1, v___x_1381_);
                    lean_ctor_set(v___x_1384_, 2, v_bkt_1378_);
                    v_buckets_x27_1385_ =
                        lean_array_uset(v_buckets_1356_, v___x_1377_, v___x_1384_);
                    v___x_1386_ = lean_unsigned_to_nat(4);
                    v___x_1387_ = lean_nat_mul(v_size_x27_1383_, v___x_1386_);
                    v___x_1388_ = lean_unsigned_to_nat(3);
                    v___x_1389_ = lean_nat_div(v___x_1387_, v___x_1388_);
                    lean_dec(v___x_1387_);
                    v___x_1390_ = lean_array_get_size(v_buckets_x27_1385_);
                    v___x_1391_ = lean_nat_dec_le(v___x_1389_, v___x_1390_);
                    lean_dec(v___x_1389_);
                    if v___x_1391_ == 0 {
                        v_val_1392_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5___redArg(v_buckets_x27_1385_);
                        if v_isShared_1359_ == 0 {
                            lean_ctor_set(v___x_1358_, 1, v_val_1392_);
                            lean_ctor_set(v___x_1358_, 0, v_size_x27_1383_);
                            v___x_1394_ = v___x_1358_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1395_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1395_, 0, v_size_x27_1383_);
                            lean_ctor_set(v_reuseFailAlloc_1395_, 1, v_val_1392_);
                            v___x_1394_ = v_reuseFailAlloc_1395_;
                            state = 4;
                            continue;
                        }
                    } else {
                        if v_isShared_1359_ == 0 {
                            lean_ctor_set(v___x_1358_, 1, v_buckets_x27_1385_);
                            lean_ctor_set(v___x_1358_, 0, v_size_x27_1383_);
                            v___x_1397_ = v___x_1358_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_1398_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1398_, 0, v_size_x27_1383_);
                            lean_ctor_set(v_reuseFailAlloc_1398_, 1, v_buckets_x27_1385_);
                            v___x_1397_ = v_reuseFailAlloc_1398_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    lean_inc(v_bkt_1378_);
                    lean_del_object(v___x_1358_);
                    v___x_1399_ = lean_box(0);
                    v_buckets_x27_1400_ =
                        lean_array_uset(v_buckets_1356_, v___x_1377_, v___x_1399_);
                    lean_inc_ref(v_a_1347_);
                    v_bkt_x27_1401_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6___redArg(v_a_1345_, v_a_1347_, v_bkt_1378_);
                    v___x_1402_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4___redArg(v_a_1347_, v_bkt_x27_1401_);
                    lean_dec_ref(v_a_1347_);
                    if v___x_1402_ == 0 {
                        v___x_1403_ = lean_unsigned_to_nat(1);
                        v___x_1404_ = lean_nat_sub(v_size_1355_, v___x_1403_);
                        lean_dec(v_size_1355_);
                        v___y_1349_ = v_bkt_x27_1401_;
                        v___y_1350_ = v_buckets_x27_1400_;
                        v___y_1351_ = v___x_1377_;
                        v___y_1352_ = v___x_1404_;
                        state = 1;
                        continue;
                    } else {
                        v___y_1349_ = v_bkt_x27_1401_;
                        v___y_1350_ = v_buckets_x27_1400_;
                        v___y_1351_ = v___x_1377_;
                        v___y_1352_ = v_size_1355_;
                        state = 1;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_1394_;
            }
            5 => {
                return v___x_1397_;
            }
            6 => {
                if lean_obj_tag(v_snd_1361_) == 0 {
                    v___x_1407_ = 11u64;
                    v___y_1364_ = v___y_1406_;
                    v___y_1365_ = v___x_1407_;
                    state = 3;
                    continue;
                } else {
                    v_val_1408_ = lean_ctor_get(v_snd_1361_, 0);
                    v___x_1409_ = l_String_instHashableRaw_hash(v_val_1408_);
                    v___x_1410_ = 13u64;
                    v___x_1411_ = lean_uint64_mix_hash(v___x_1409_, v___x_1410_);
                    v___y_1364_ = v___y_1406_;
                    v___y_1365_ = v___x_1411_;
                    state = 3;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__4___redArg(
    mut v_key_1416_: *mut LeanObject,
    mut v_as_1417_: *mut LeanObject,
    mut v_sz_1418_: usize,
    mut v_i_1419_: usize,
    mut v_b_1420_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1421_: u8 = 0;
    let mut v_a_1422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: usize = 0;
    let mut v___x_1426_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1421_ = lean_usize_dec_lt(v_i_1419_, v_sz_1418_);
                if v___x_1421_ == 0 {
                    lean_dec_ref(v_key_1416_);
                    return v_b_1420_;
                } else {
                    v_a_1422_ = lean_array_uget_borrowed(v_as_1417_, v_i_1419_);
                    lean_inc_ref(v_key_1416_);
                    lean_inc_n(v_a_1422_, 2);
                    v___x_1423_ = lean_apply_1(v_key_1416_, v_a_1422_);
                    v___x_1424_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3___redArg(v_a_1422_, v_b_1420_, v___x_1423_);
                    v___x_1425_ = 1usize;
                    v___x_1426_ = lean_usize_add(v_i_1419_, v___x_1425_);
                    v_i_1419_ = v___x_1426_;
                    v_b_1420_ = v___x_1424_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__4___redArg___boxed(
    mut v_key_1428_: *mut LeanObject,
    mut v_as_1429_: *mut LeanObject,
    mut v_sz_1430_: *mut LeanObject,
    mut v_i_1431_: *mut LeanObject,
    mut v_b_1432_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1433_: usize = 0;
    let mut v_i_boxed_1434_: usize = 0;
    let mut v_res_1435_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1433_ = lean_unbox_usize(v_sz_1430_);
    lean_dec(v_sz_1430_);
    v_i_boxed_1434_ = lean_unbox_usize(v_i_1431_);
    lean_dec(v_i_1431_);
    v_res_1435_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__4___redArg(v_key_1428_, v_as_1429_, v_sz_boxed_1433_, v_i_boxed_1434_, v_b_1432_);
    lean_dec_ref(v_as_1429_);
    return v_res_1435_;
}
pub unsafe fn _init_l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_1436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut LeanObject = core::ptr::null_mut();
    v___x_1436_ = lean_box(0);
    v___x_1437_ = lean_unsigned_to_nat(16);
    v___x_1438_ = lean_mk_array(v___x_1437_, v___x_1436_);
    return v___x_1438_;
}
pub unsafe fn _init_l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_1439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_groups_1441_: *mut LeanObject = core::ptr::null_mut();
    v___x_1439_ = lean_obj_once(core::ptr::addr_of_mut!(l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___closed__0_once), _init_l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___closed__0);
    v___x_1440_ = lean_unsigned_to_nat(0);
    v_groups_1441_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v_groups_1441_, 0, v___x_1440_);
    lean_ctor_set(v_groups_1441_, 1, v___x_1439_);
    return v_groups_1441_;
}
pub unsafe fn l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg(
    mut v_key_1442_: *mut LeanObject,
    mut v_xs_1443_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_groups_1444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1445_: usize = 0;
    let mut v___x_1446_: usize = 0;
    let mut v___x_1447_: *mut LeanObject = core::ptr::null_mut();
    v_groups_1444_ = lean_obj_once(core::ptr::addr_of_mut!(l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___closed__1_once), _init_l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___closed__1);
    v_sz_1445_ = lean_array_size(v_xs_1443_);
    v___x_1446_ = 0usize;
    v___x_1447_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__4___redArg(v_key_1442_, v_xs_1443_, v_sz_1445_, v___x_1446_, v_groups_1444_);
    return v___x_1447_;
}
pub unsafe fn l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___boxed(
    mut v_key_1448_: *mut LeanObject,
    mut v_xs_1449_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1450_: *mut LeanObject = core::ptr::null_mut();
    v_res_1450_ = l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg(v_key_1448_, v_xs_1449_);
    lean_dec_ref(v_xs_1449_);
    return v_res_1450_;
}
pub unsafe fn l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions(
    mut v_items_1452_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1455_: usize = 0;
    let mut v___x_1456_: usize = 0;
    let mut v___x_1457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: u8 = 0;
    let mut v___y_1471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: u8 = 0;
    let mut v___x_1475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: u8 = 0;
    let mut v___f_1478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_partitions_1479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_1481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: u8 = 0;
    let mut v___x_1486_: u8 = 0;
    let mut v___x_1487_: usize = 0;
    let mut v___x_1488_: usize = 0;
    let mut v___x_1489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: usize = 0;
    let mut v___x_1491_: usize = 0;
    let mut v___x_1492_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1478_ = l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions___closed__0;
                v_partitions_1479_ = l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg(v___f_1478_, v_items_1452_);
                v_size_1480_ = lean_ctor_get(v_partitions_1479_, 0);
                lean_inc(v_size_1480_);
                v_buckets_1481_ = lean_ctor_get(v_partitions_1479_, 1);
                lean_inc_ref(v_buckets_1481_);
                lean_dec_ref(v_partitions_1479_);
                v___x_1482_ = lean_mk_empty_array_with_capacity(v_size_1480_);
                lean_dec(v_size_1480_);
                v___x_1483_ = lean_unsigned_to_nat(0);
                v___x_1484_ = lean_array_get_size(v_buckets_1481_);
                v___x_1485_ = lean_nat_dec_lt(v___x_1483_, v___x_1484_);
                if v___x_1485_ == 0 {
                    lean_dec_ref(v_buckets_1481_);
                    v___y_1471_ = v___x_1482_;
                    state = 4;
                    continue;
                } else {
                    v___x_1486_ = lean_nat_dec_le(v___x_1484_, v___x_1484_);
                    if v___x_1486_ == 0 {
                        if v___x_1485_ == 0 {
                            lean_dec_ref(v_buckets_1481_);
                            v___y_1471_ = v___x_1482_;
                            state = 4;
                            continue;
                        } else {
                            v___x_1487_ = 0usize;
                            v___x_1488_ = lean_usize_of_nat(v___x_1484_);
                            v___x_1489_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__4(v_buckets_1481_, v___x_1487_, v___x_1488_, v___x_1482_);
                            lean_dec_ref(v_buckets_1481_);
                            v___y_1471_ = v___x_1489_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v___x_1490_ = 0usize;
                        v___x_1491_ = lean_usize_of_nat(v___x_1484_);
                        v___x_1492_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__4(v_buckets_1481_, v___x_1490_, v___x_1491_, v___x_1482_);
                        lean_dec_ref(v_buckets_1481_);
                        v___y_1471_ = v___x_1492_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_sz_1455_ = lean_array_size(v___y_1454_);
                v___x_1456_ = 0usize;
                v___x_1457_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__0(v_sz_1455_, v___x_1456_, v___y_1454_);
                return v___x_1457_;
            }
            2 => {
                v___x_1463_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg(v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_);
                lean_dec(v___y_1462_);
                lean_dec(v___y_1459_);
                v___y_1454_ = v___x_1463_;
                state = 1;
                continue;
            }
            3 => {
                v___x_1469_ = lean_nat_dec_le(v___y_1468_, v___y_1467_);
                if v___x_1469_ == 0 {
                    lean_dec(v___y_1467_);
                    lean_inc(v___y_1468_);
                    v___y_1459_ = v___y_1465_;
                    v___y_1460_ = v___y_1466_;
                    v___y_1461_ = v___y_1468_;
                    v___y_1462_ = v___y_1468_;
                    state = 2;
                    continue;
                } else {
                    v___y_1459_ = v___y_1465_;
                    v___y_1460_ = v___y_1466_;
                    v___y_1461_ = v___y_1468_;
                    v___y_1462_ = v___y_1467_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                v___x_1472_ = lean_array_get_size(v___y_1471_);
                v___x_1473_ = lean_unsigned_to_nat(0);
                v___x_1474_ = lean_nat_dec_eq(v___x_1472_, v___x_1473_);
                if v___x_1474_ == 0 {
                    v___x_1475_ = lean_unsigned_to_nat(1);
                    v___x_1476_ = lean_nat_sub(v___x_1472_, v___x_1475_);
                    v___x_1477_ = lean_nat_dec_le(v___x_1473_, v___x_1476_);
                    if v___x_1477_ == 0 {
                        lean_inc(v___x_1476_);
                        v___y_1465_ = v___x_1472_;
                        v___y_1466_ = v___y_1471_;
                        v___y_1467_ = v___x_1476_;
                        v___y_1468_ = v___x_1476_;
                        state = 3;
                        continue;
                    } else {
                        v___y_1465_ = v___x_1472_;
                        v___y_1466_ = v___y_1471_;
                        v___y_1467_ = v___x_1476_;
                        v___y_1468_ = v___x_1473_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___y_1454_ = v___y_1471_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions___boxed(
    mut v_items_1493_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1494_: *mut LeanObject = core::ptr::null_mut();
    v_res_1494_ = l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions(v_items_1493_);
    lean_dec_ref(v_items_1493_);
    return v_res_1494_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1(
    mut v_n_1495_: *mut LeanObject,
    mut v_as_1496_: *mut LeanObject,
    mut v_lo_1497_: *mut LeanObject,
    mut v_hi_1498_: *mut LeanObject,
    mut v_w_1499_: *mut LeanObject,
    mut v_hlo_1500_: *mut LeanObject,
    mut v_hhi_1501_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1502_: *mut LeanObject = core::ptr::null_mut();
    v___x_1502_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg(v_n_1495_, v_as_1496_, v_lo_1497_, v_hi_1498_);
    return v___x_1502_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___boxed(
    mut v_n_1503_: *mut LeanObject,
    mut v_as_1504_: *mut LeanObject,
    mut v_lo_1505_: *mut LeanObject,
    mut v_hi_1506_: *mut LeanObject,
    mut v_w_1507_: *mut LeanObject,
    mut v_hlo_1508_: *mut LeanObject,
    mut v_hhi_1509_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1510_: *mut LeanObject = core::ptr::null_mut();
    v_res_1510_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1(v_n_1503_, v_as_1504_, v_lo_1505_, v_hi_1506_, v_w_1507_, v_hlo_1508_, v_hhi_1509_);
    lean_dec(v_hi_1506_);
    lean_dec(v_n_1503_);
    return v_res_1510_;
}
pub unsafe fn l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2(
    mut v_00_u03b2_1511_: *mut LeanObject,
    mut v_key_1512_: *mut LeanObject,
    mut v_xs_1513_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1514_: *mut LeanObject = core::ptr::null_mut();
    v___x_1514_ = l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg(v_key_1512_, v_xs_1513_);
    return v___x_1514_;
}
pub unsafe fn l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___boxed(
    mut v_00_u03b2_1515_: *mut LeanObject,
    mut v_key_1516_: *mut LeanObject,
    mut v_xs_1517_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1518_: *mut LeanObject = core::ptr::null_mut();
    v_res_1518_ = l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2(v_00_u03b2_1515_, v_key_1516_, v_xs_1517_);
    lean_dec_ref(v_xs_1517_);
    return v_res_1518_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1(
    mut v_n_1519_: *mut LeanObject,
    mut v_lo_1520_: *mut LeanObject,
    mut v_hi_1521_: *mut LeanObject,
    mut v_hhi_1522_: *mut LeanObject,
    mut v_pivot_1523_: *mut LeanObject,
    mut v_as_1524_: *mut LeanObject,
    mut v_i_1525_: *mut LeanObject,
    mut v_k_1526_: *mut LeanObject,
    mut v_ilo_1527_: *mut LeanObject,
    mut v_ik_1528_: *mut LeanObject,
    mut v_w_1529_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1530_: *mut LeanObject = core::ptr::null_mut();
    v___x_1530_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1___redArg(v_hi_1521_, v_pivot_1523_, v_as_1524_, v_i_1525_, v_k_1526_);
    return v___x_1530_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1___boxed(
    mut v_n_1531_: *mut LeanObject,
    mut v_lo_1532_: *mut LeanObject,
    mut v_hi_1533_: *mut LeanObject,
    mut v_hhi_1534_: *mut LeanObject,
    mut v_pivot_1535_: *mut LeanObject,
    mut v_as_1536_: *mut LeanObject,
    mut v_i_1537_: *mut LeanObject,
    mut v_k_1538_: *mut LeanObject,
    mut v_ilo_1539_: *mut LeanObject,
    mut v_ik_1540_: *mut LeanObject,
    mut v_w_1541_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1542_: *mut LeanObject = core::ptr::null_mut();
    v_res_1542_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1(v_n_1531_, v_lo_1532_, v_hi_1533_, v_hhi_1534_, v_pivot_1535_, v_as_1536_, v_i_1537_, v_k_1538_, v_ilo_1539_, v_ik_1540_, v_w_1541_);
    lean_dec_ref(v_pivot_1535_);
    lean_dec(v_hi_1533_);
    lean_dec(v_lo_1532_);
    lean_dec(v_n_1531_);
    return v_res_1542_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3(
    mut v_00_u03b2_1543_: *mut LeanObject,
    mut v_a_1544_: *mut LeanObject,
    mut v_m_1545_: *mut LeanObject,
    mut v_a_1546_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1547_: *mut LeanObject = core::ptr::null_mut();
    v___x_1547_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3___redArg(v_a_1544_, v_m_1545_, v_a_1546_);
    return v___x_1547_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__4(
    mut v_00_u03b2_1548_: *mut LeanObject,
    mut v_key_1549_: *mut LeanObject,
    mut v_as_1550_: *mut LeanObject,
    mut v_sz_1551_: usize,
    mut v_i_1552_: usize,
    mut v_b_1553_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1554_: *mut LeanObject = core::ptr::null_mut();
    v___x_1554_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__4___redArg(v_key_1549_, v_as_1550_, v_sz_1551_, v_i_1552_, v_b_1553_);
    return v___x_1554_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__4___boxed(
    mut v_00_u03b2_1555_: *mut LeanObject,
    mut v_key_1556_: *mut LeanObject,
    mut v_as_1557_: *mut LeanObject,
    mut v_sz_1558_: *mut LeanObject,
    mut v_i_1559_: *mut LeanObject,
    mut v_b_1560_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1561_: usize = 0;
    let mut v_i_boxed_1562_: usize = 0;
    let mut v_res_1563_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1561_ = lean_unbox_usize(v_sz_1558_);
    lean_dec(v_sz_1558_);
    v_i_boxed_1562_ = lean_unbox_usize(v_i_1559_);
    lean_dec(v_i_1559_);
    v_res_1563_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__4(v_00_u03b2_1555_, v_key_1556_, v_as_1557_, v_sz_boxed_1561_, v_i_boxed_1562_, v_b_1560_);
    lean_dec_ref(v_as_1557_);
    return v_res_1563_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4(
    mut v_00_u03b2_1564_: *mut LeanObject,
    mut v_a_1565_: *mut LeanObject,
    mut v_x_1566_: *mut LeanObject,
) -> u8 {
    let mut v___x_1567_: u8 = 0;
    v___x_1567_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4___redArg(v_a_1565_, v_x_1566_);
    return v___x_1567_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4___boxed(
    mut v_00_u03b2_1568_: *mut LeanObject,
    mut v_a_1569_: *mut LeanObject,
    mut v_x_1570_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1571_: u8 = 0;
    let mut v_r_1572_: *mut LeanObject = core::ptr::null_mut();
    v_res_1571_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4(v_00_u03b2_1568_, v_a_1569_, v_x_1570_);
    lean_dec(v_x_1570_);
    lean_dec_ref(v_a_1569_);
    v_r_1572_ = lean_box((v_res_1571_) as usize);
    return v_r_1572_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5(
    mut v_00_u03b2_1573_: *mut LeanObject,
    mut v_data_1574_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1575_: *mut LeanObject = core::ptr::null_mut();
    v___x_1575_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5___redArg(v_data_1574_);
    return v___x_1575_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6(
    mut v_00_u03b2_1576_: *mut LeanObject,
    mut v_a_1577_: *mut LeanObject,
    mut v_a_1578_: *mut LeanObject,
    mut v_x_1579_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1580_: *mut LeanObject = core::ptr::null_mut();
    v___x_1580_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6___redArg(v_a_1577_, v_a_1578_, v_x_1579_);
    return v___x_1580_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5_spec__9(
    mut v_00_u03b2_1581_: *mut LeanObject,
    mut v_i_1582_: *mut LeanObject,
    mut v_source_1583_: *mut LeanObject,
    mut v_target_1584_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1585_: *mut LeanObject = core::ptr::null_mut();
    v___x_1585_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5_spec__9___redArg(v_i_1582_, v_source_1583_, v_target_1584_);
    return v___x_1585_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5_spec__9_spec__11(
    mut v_00_u03b2_1586_: *mut LeanObject,
    mut v_x_1587_: *mut LeanObject,
    mut v_x_1588_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1589_: *mut LeanObject = core::ptr::null_mut();
    v___x_1589_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5_spec__9_spec__11___redArg(v_x_1587_, v_x_1588_);
    return v___x_1589_;
}
pub unsafe fn l_Lean_Server_Completion_findPrioritizedCompletionPartitionsAt(
    mut v_fileMap_1590_: *mut LeanObject,
    mut v_hoverPos_1591_: *mut LeanObject,
    mut v_cmdStx_1592_: *mut LeanObject,
    mut v_infoTree_1593_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1599_: u8 = 0;
    let mut v___x_1600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_partitions_1602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1606_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1594_ = l_Lean_Server_Completion_findCompletionInfosAt(
                    v_fileMap_1590_,
                    v_hoverPos_1591_,
                    v_cmdStx_1592_,
                    v_infoTree_1593_,
                );
                v_fst_1595_ = lean_ctor_get(v___x_1594_, 0);
                v_snd_1596_ = lean_ctor_get(v___x_1594_, 1);
                v_isSharedCheck_1606_ = (!lean_is_exclusive(v___x_1594_)) as u8;
                if v_isSharedCheck_1606_ == 0 {
                    v___x_1598_ = v___x_1594_;
                    v_isShared_1599_ = v_isSharedCheck_1606_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_1596_);
                    lean_inc(v_fst_1595_);
                    lean_dec(v___x_1594_);
                    v___x_1598_ = lean_box(0);
                    v_isShared_1599_ = v_isSharedCheck_1606_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1600_ = lean_unsigned_to_nat(0);
                v___x_1601_ = l_Array_zipIdx___redArg(v_fst_1595_, v___x_1600_);
                lean_dec(v_fst_1595_);
                v_partitions_1602_ = l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions(v___x_1601_);
                lean_dec_ref(v___x_1601_);
                if v_isShared_1599_ == 0 {
                    lean_ctor_set(v___x_1598_, 0, v_partitions_1602_);
                    v___x_1604_ = v___x_1598_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1605_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_partitions_1602_);
                    lean_ctor_set(v_reuseFailAlloc_1605_, 1, v_snd_1596_);
                    v___x_1604_ = v_reuseFailAlloc_1605_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1604_;
            }
            _ => {}
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Server_Completion_CompletionInfoSelection(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Server_Completion_SyntheticCompletion(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Server_Completion_CompletionInfoSelection(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Server_Completion_CompletionInfoSelection(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Server_Completion_SyntheticCompletion(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Server_Completion_CompletionInfoSelection(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Server_Completion_CompletionInfoSelection(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Server_Completion_CompletionInfoSelection(builtin);
}
