// Lean compiler output
// Module: Lean.Server.Completion.CompletionInfoSelection
// Imports: Lean.Server.Completion.SyntheticCompletion
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_fswap,
    lean_array_get_size, lean_array_push, lean_array_size, lean_array_uget_borrowed,
    lean_array_uset, lean_expr_eqv, lean_mk_array, lean_mk_empty_array_with_capacity, lean_name_eq,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul,
    lean_nat_shiftr, lean_nat_sub, lean_panic_fn_borrowed, lean_uint64_mix_hash,
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_add,
    lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_land, lean_usize_of_nat, lean_usize_sub,
};
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
pub static l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__0_value: crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [73, 110, 105, 116, 46, 68, 97, 116, 97, 46, 79, 112, 116, 105, 111, 110, 46, 66, 97, 115, 105, 99, 65, 117, 120, 0]};
static mut l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__1_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [79, 112, 116, 105, 111, 110, 46, 103, 101, 116, 33, 0]};
static mut l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__2_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [118, 97, 108, 117, 101, 32, 105, 115, 32, 110, 111, 110, 101, 0]};
static mut l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6___redArg___lam__0___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6___redArg___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6___redArg___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions___lam__0 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions___closed__0_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Option_instBEq_beq___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_eq_spec__0(
    mut v_x_804_: *mut crate::leanh::LeanObject,
    mut v_x_805_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_804_) == 0 {
        if crate::leanh::lean_obj_tag(v_x_805_) == 0 {
            let mut v___x_806_: u8 = 0;
            v___x_806_ = 1;
            return v___x_806_;
        } else {
            let mut v___x_807_: u8 = 0;
            v___x_807_ = 0;
            return v___x_807_;
        }
    } else {
        if crate::leanh::lean_obj_tag(v_x_805_) == 0 {
            let mut v___x_808_: u8 = 0;
            v___x_808_ = 0;
            return v___x_808_;
        } else {
            let mut v_val_809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_811_: u8 = 0;
            v_val_809_ = crate::leanh::lean_ctor_get(v_x_804_, 0);
            v_val_810_ = crate::leanh::lean_ctor_get(v_x_805_, 0);
            v___x_811_ = lean_name_eq(v_val_809_, v_val_810_);
            return v___x_811_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_eq_spec__0___boxed(
    mut v_x_812_: *mut crate::leanh::LeanObject,
    mut v_x_813_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_814_: u8 = 0;
    let mut v_r_815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_814_ = l_Option_instBEq_beq___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_eq_spec__0(v_x_812_, v_x_813_);
    crate::leanh::lean_dec(v_x_813_);
    crate::leanh::lean_dec(v_x_812_);
    v_r_815_ = crate::leanh::lean_box((v_res_814_) as usize);
    return v_r_815_;
}
pub unsafe fn l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_eq(
    mut v_a_816_: *mut crate::leanh::LeanObject,
    mut v_a_817_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_termInfo_818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toElabInfo_819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_termInfo_820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toElabInfo_821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_826_: u8 = 0;
    let mut v___x_827_: u8 = 0;
    let mut v___x_828_: u8 = 0;
    let mut v_stx_829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_structName_831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_structName_834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_836_: u8 = 0;
    let mut v___x_837_: u8 = 0;
    let mut v___x_838_: u8 = 0;
    let mut v___x_839_: u8 = 0;
    let mut v___x_840_: u8 = 0;
    let mut v_stx_841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_843_: u8 = 0;
    let mut v___x_844_: u8 = 0;
    let mut v_stx_845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_847_: u8 = 0;
    let mut v___x_848_: u8 = 0;
    let mut v_stx_849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_851_: u8 = 0;
    let mut v___x_852_: u8 = 0;
    let mut v_stx_853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_855_: u8 = 0;
    let mut v___x_856_: u8 = 0;
    let mut v_stx_857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_859_: u8 = 0;
    let mut v___x_860_: u8 = 0;
    let mut v_stx_861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_865_: u8 = 0;
    let mut v___x_866_: u8 = 0;
    let mut v___x_867_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_a_816_) {
                0 => {
                    if crate::leanh::lean_obj_tag(v_a_817_) == 0 {
                        v_termInfo_818_ = crate::leanh::lean_ctor_get(v_a_816_, 0);
                        crate::leanh::lean_inc_ref(v_termInfo_818_);
                        crate::leanh::lean_dec_ref_known(v_a_816_, 2);
                        v_toElabInfo_819_ = crate::leanh::lean_ctor_get(v_termInfo_818_, 0);
                        crate::leanh::lean_inc_ref(v_toElabInfo_819_);
                        v_termInfo_820_ = crate::leanh::lean_ctor_get(v_a_817_, 0);
                        crate::leanh::lean_inc_ref(v_termInfo_820_);
                        crate::leanh::lean_dec_ref_known(v_a_817_, 2);
                        v_toElabInfo_821_ = crate::leanh::lean_ctor_get(v_termInfo_820_, 0);
                        crate::leanh::lean_inc_ref(v_toElabInfo_821_);
                        v_expr_822_ = crate::leanh::lean_ctor_get(v_termInfo_818_, 3);
                        crate::leanh::lean_inc_ref(v_expr_822_);
                        crate::leanh::lean_dec_ref(v_termInfo_818_);
                        v_stx_823_ = crate::leanh::lean_ctor_get(v_toElabInfo_819_, 1);
                        crate::leanh::lean_inc(v_stx_823_);
                        crate::leanh::lean_dec_ref(v_toElabInfo_819_);
                        v_expr_824_ = crate::leanh::lean_ctor_get(v_termInfo_820_, 3);
                        crate::leanh::lean_inc_ref(v_expr_824_);
                        crate::leanh::lean_dec_ref(v_termInfo_820_);
                        v_stx_825_ = crate::leanh::lean_ctor_get(v_toElabInfo_821_, 1);
                        crate::leanh::lean_inc(v_stx_825_);
                        crate::leanh::lean_dec_ref(v_toElabInfo_821_);
                        v___x_826_ = l_Lean_Syntax_eqWithInfo(v_stx_823_, v_stx_825_);
                        if v___x_826_ == 0 {
                            crate::leanh::lean_dec_ref(v_expr_824_);
                            crate::leanh::lean_dec_ref(v_expr_822_);
                            return v___x_826_;
                        } else {
                            v___x_827_ = lean_expr_eqv(v_expr_822_, v_expr_824_);
                            crate::leanh::lean_dec_ref(v_expr_824_);
                            crate::leanh::lean_dec_ref(v_expr_822_);
                            return v___x_827_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_a_816_, 2);
                        crate::leanh::lean_dec_ref(v_a_817_);
                        v___x_828_ = 0;
                        return v___x_828_;
                    }
                }
                3 => {
                    if crate::leanh::lean_obj_tag(v_a_817_) == 3 {
                        v_stx_829_ = crate::leanh::lean_ctor_get(v_a_816_, 0);
                        crate::leanh::lean_inc(v_stx_829_);
                        v_id_830_ = crate::leanh::lean_ctor_get(v_a_816_, 1);
                        crate::leanh::lean_inc(v_id_830_);
                        v_structName_831_ = crate::leanh::lean_ctor_get(v_a_816_, 3);
                        crate::leanh::lean_inc(v_structName_831_);
                        crate::leanh::lean_dec_ref_known(v_a_816_, 4);
                        v_stx_832_ = crate::leanh::lean_ctor_get(v_a_817_, 0);
                        crate::leanh::lean_inc(v_stx_832_);
                        v_id_833_ = crate::leanh::lean_ctor_get(v_a_817_, 1);
                        crate::leanh::lean_inc(v_id_833_);
                        v_structName_834_ = crate::leanh::lean_ctor_get(v_a_817_, 3);
                        crate::leanh::lean_inc(v_structName_834_);
                        crate::leanh::lean_dec_ref_known(v_a_817_, 4);
                        v___x_838_ = l_Lean_Syntax_eqWithInfo(v_stx_829_, v_stx_832_);
                        if v___x_838_ == 0 {
                            crate::leanh::lean_dec(v_id_833_);
                            crate::leanh::lean_dec(v_id_830_);
                            v___y_836_ = v___x_838_;
                            state = 1;
                            continue;
                        } else {
                            v___x_839_ = l_Option_instBEq_beq___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_eq_spec__0(v_id_830_, v_id_833_);
                            crate::leanh::lean_dec(v_id_833_);
                            crate::leanh::lean_dec(v_id_830_);
                            v___y_836_ = v___x_839_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_a_816_, 4);
                        crate::leanh::lean_dec_ref(v_a_817_);
                        v___x_840_ = 0;
                        return v___x_840_;
                    }
                }
                4 => {
                    if crate::leanh::lean_obj_tag(v_a_817_) == 4 {
                        v_stx_841_ = crate::leanh::lean_ctor_get(v_a_816_, 0);
                        crate::leanh::lean_inc(v_stx_841_);
                        crate::leanh::lean_dec_ref_known(v_a_816_, 1);
                        v_stx_842_ = crate::leanh::lean_ctor_get(v_a_817_, 0);
                        crate::leanh::lean_inc(v_stx_842_);
                        crate::leanh::lean_dec_ref_known(v_a_817_, 1);
                        v___x_843_ = l_Lean_Syntax_eqWithInfo(v_stx_841_, v_stx_842_);
                        return v___x_843_;
                    } else {
                        crate::leanh::lean_dec_ref_known(v_a_816_, 1);
                        crate::leanh::lean_dec_ref(v_a_817_);
                        v___x_844_ = 0;
                        return v___x_844_;
                    }
                }
                5 => {
                    if crate::leanh::lean_obj_tag(v_a_817_) == 5 {
                        v_stx_845_ = crate::leanh::lean_ctor_get(v_a_816_, 0);
                        crate::leanh::lean_inc(v_stx_845_);
                        crate::leanh::lean_dec_ref_known(v_a_816_, 1);
                        v_stx_846_ = crate::leanh::lean_ctor_get(v_a_817_, 0);
                        crate::leanh::lean_inc(v_stx_846_);
                        crate::leanh::lean_dec_ref_known(v_a_817_, 1);
                        v___x_847_ = l_Lean_Syntax_eqWithInfo(v_stx_845_, v_stx_846_);
                        return v___x_847_;
                    } else {
                        crate::leanh::lean_dec_ref_known(v_a_816_, 1);
                        crate::leanh::lean_dec_ref(v_a_817_);
                        v___x_848_ = 0;
                        return v___x_848_;
                    }
                }
                6 => {
                    if crate::leanh::lean_obj_tag(v_a_817_) == 6 {
                        v_stx_849_ = crate::leanh::lean_ctor_get(v_a_816_, 0);
                        crate::leanh::lean_inc(v_stx_849_);
                        crate::leanh::lean_dec_ref_known(v_a_816_, 2);
                        v_stx_850_ = crate::leanh::lean_ctor_get(v_a_817_, 0);
                        crate::leanh::lean_inc(v_stx_850_);
                        crate::leanh::lean_dec_ref_known(v_a_817_, 2);
                        v___x_851_ = l_Lean_Syntax_eqWithInfo(v_stx_849_, v_stx_850_);
                        return v___x_851_;
                    } else {
                        crate::leanh::lean_dec_ref_known(v_a_816_, 2);
                        crate::leanh::lean_dec_ref(v_a_817_);
                        v___x_852_ = 0;
                        return v___x_852_;
                    }
                }
                7 => {
                    if crate::leanh::lean_obj_tag(v_a_817_) == 7 {
                        v_stx_853_ = crate::leanh::lean_ctor_get(v_a_816_, 0);
                        crate::leanh::lean_inc(v_stx_853_);
                        crate::leanh::lean_dec_ref_known(v_a_816_, 3);
                        v_stx_854_ = crate::leanh::lean_ctor_get(v_a_817_, 0);
                        crate::leanh::lean_inc(v_stx_854_);
                        crate::leanh::lean_dec_ref_known(v_a_817_, 3);
                        v___x_855_ = l_Lean_Syntax_eqWithInfo(v_stx_853_, v_stx_854_);
                        return v___x_855_;
                    } else {
                        crate::leanh::lean_dec_ref_known(v_a_816_, 3);
                        crate::leanh::lean_dec_ref(v_a_817_);
                        v___x_856_ = 0;
                        return v___x_856_;
                    }
                }
                8 => {
                    if crate::leanh::lean_obj_tag(v_a_817_) == 8 {
                        v_stx_857_ = crate::leanh::lean_ctor_get(v_a_816_, 0);
                        crate::leanh::lean_inc(v_stx_857_);
                        crate::leanh::lean_dec_ref_known(v_a_816_, 1);
                        v_stx_858_ = crate::leanh::lean_ctor_get(v_a_817_, 0);
                        crate::leanh::lean_inc(v_stx_858_);
                        crate::leanh::lean_dec_ref_known(v_a_817_, 1);
                        v___x_859_ = l_Lean_Syntax_eqWithInfo(v_stx_857_, v_stx_858_);
                        return v___x_859_;
                    } else {
                        crate::leanh::lean_dec_ref_known(v_a_816_, 1);
                        crate::leanh::lean_dec_ref(v_a_817_);
                        v___x_860_ = 0;
                        return v___x_860_;
                    }
                }
                _ => {
                    if crate::leanh::lean_obj_tag(v_a_817_) == 1 {
                        v_stx_861_ = crate::leanh::lean_ctor_get(v_a_816_, 0);
                        crate::leanh::lean_inc(v_stx_861_);
                        v_id_862_ = crate::leanh::lean_ctor_get(v_a_816_, 1);
                        crate::leanh::lean_inc(v_id_862_);
                        crate::leanh::lean_dec_ref(v_a_816_);
                        v_stx_863_ = crate::leanh::lean_ctor_get(v_a_817_, 0);
                        crate::leanh::lean_inc(v_stx_863_);
                        v_id_864_ = crate::leanh::lean_ctor_get(v_a_817_, 1);
                        crate::leanh::lean_inc(v_id_864_);
                        crate::leanh::lean_dec_ref_known(v_a_817_, 4);
                        v___x_865_ = l_Lean_Syntax_eqWithInfo(v_stx_861_, v_stx_863_);
                        if v___x_865_ == 0 {
                            crate::leanh::lean_dec(v_id_864_);
                            crate::leanh::lean_dec(v_id_862_);
                            return v___x_865_;
                        } else {
                            v___x_866_ = lean_name_eq(v_id_862_, v_id_864_);
                            crate::leanh::lean_dec(v_id_864_);
                            crate::leanh::lean_dec(v_id_862_);
                            return v___x_866_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_a_817_);
                        crate::leanh::lean_dec_ref(v_a_816_);
                        v___x_867_ = 0;
                        return v___x_867_;
                    }
                }
            },
            1 => {
                if v___y_836_ == 0 {
                    crate::leanh::lean_dec(v_structName_834_);
                    crate::leanh::lean_dec(v_structName_831_);
                    return v___y_836_;
                } else {
                    v___x_837_ = lean_name_eq(v_structName_831_, v_structName_834_);
                    crate::leanh::lean_dec(v_structName_834_);
                    crate::leanh::lean_dec(v_structName_831_);
                    return v___x_837_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_eq___boxed(
    mut v_a_868_: *mut crate::leanh::LeanObject,
    mut v_a_869_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_870_: u8 = 0;
    let mut v_r_871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_870_ = l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_eq(v_a_868_, v_a_869_);
    v_r_871_ = crate::leanh::lean_box((v_res_870_) as usize);
    return v_r_871_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_spec__0(
    mut v_a_872_: *mut crate::leanh::LeanObject,
    mut v_as_873_: *mut crate::leanh::LeanObject,
    mut v_i_874_: usize,
    mut v_stop_875_: usize,
) -> u8 {
    let mut v___x_876_: u8 = 0;
    let mut v___x_877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_info_878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_info_879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
                    v_info_878_ = crate::leanh::lean_ctor_get(v___x_877_, 2);
                    v_info_879_ = crate::leanh::lean_ctor_get(v_a_872_, 2);
                    crate::leanh::lean_inc_ref(v_info_879_);
                    crate::leanh::lean_inc_ref(v_info_878_);
                    v___x_880_ = l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_eq(v_info_878_, v_info_879_);
                    if v___x_880_ == 0 {
                        v___x_881_ = 1usize;
                        v___x_882_ = lean_usize_add(v_i_874_, v___x_881_);
                        v_i_874_ = v___x_882_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_a_872_);
                        return v___x_880_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_a_872_);
                    v___x_884_ = 0;
                    return v___x_884_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_spec__0___boxed(
    mut v_a_885_: *mut crate::leanh::LeanObject,
    mut v_as_886_: *mut crate::leanh::LeanObject,
    mut v_i_887_: *mut crate::leanh::LeanObject,
    mut v_stop_888_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_889_: usize = 0;
    let mut v_stop_boxed_890_: usize = 0;
    let mut v_res_891_: u8 = 0;
    let mut v_r_892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_889_ = crate::leanh::lean_unbox_usize(v_i_887_);
    crate::leanh::lean_dec(v_i_887_);
    v_stop_boxed_890_ = crate::leanh::lean_unbox_usize(v_stop_888_);
    crate::leanh::lean_dec(v_stop_888_);
    v_res_891_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_spec__0(v_a_885_, v_as_886_, v_i_boxed_889_, v_stop_boxed_890_);
    crate::leanh::lean_dec_ref(v_as_886_);
    v_r_892_ = crate::leanh::lean_box((v_res_891_) as usize);
    return v_r_892_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_spec__1(
    mut v_as_893_: *mut crate::leanh::LeanObject,
    mut v_sz_894_: usize,
    mut v_i_895_: usize,
    mut v_b_896_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_899_: usize = 0;
    let mut v___x_900_: usize = 0;
    let mut v___x_902_: u8 = 0;
    let mut v_a_903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
                    v___x_906_ = crate::leanh::lean_unsigned_to_nat(0);
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
                            crate::leanh::lean_inc(v_a_903_);
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
                crate::leanh::lean_inc(v_a_903_);
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
    mut v_as_912_: *mut crate::leanh::LeanObject,
    mut v_sz_913_: *mut crate::leanh::LeanObject,
    mut v_i_914_: *mut crate::leanh::LeanObject,
    mut v_b_915_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_916_: usize = 0;
    let mut v_i_boxed_917_: usize = 0;
    let mut v_res_918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_916_ = crate::leanh::lean_unbox_usize(v_sz_913_);
    crate::leanh::lean_dec(v_sz_913_);
    v_i_boxed_917_ = crate::leanh::lean_unbox_usize(v_i_914_);
    crate::leanh::lean_dec(v_i_914_);
    v_res_918_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_spec__1(v_as_912_, v_sz_boxed_916_, v_i_boxed_917_, v_b_915_);
    crate::leanh::lean_dec_ref(v_as_912_);
    return v_res_918_;
}
pub unsafe fn l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos(
    mut v_infos_921_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_deduplicatedInfos_922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_923_: usize = 0;
    let mut v___x_924_: usize = 0;
    let mut v___x_925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_deduplicatedInfos_922_ = l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos___closed__0;
    v_sz_923_ = lean_array_size(v_infos_921_);
    v___x_924_ = 0usize;
    v___x_925_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos_spec__1(v_infos_921_, v_sz_923_, v___x_924_, v_deduplicatedInfos_922_);
    return v___x_925_;
}
pub unsafe fn l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos___boxed(
    mut v_infos_926_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_927_ = l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos(v_infos_926_);
    crate::leanh::lean_dec_ref(v_infos_926_);
    return v_res_927_;
}
pub unsafe fn l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_containsHoverPos(
    mut v_hoverPos_928_: *mut crate::leanh::LeanObject,
    mut v_i_929_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_932_: u8 = 0;
    let mut v_id_x3f_934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_936_: u8 = 0;
    let mut v___x_937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_939_: u8 = 0;
    let mut v___x_940_: u8 = 0;
    let mut v___x_941_: u8 = 0;
    let mut v_stx_942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_945_: u8 = 0;
    let mut v___x_946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_948_: u8 = 0;
    let mut v___x_949_: u8 = 0;
    let mut v___x_950_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_i_929_) == 5 {
                    v_stx_942_ = crate::leanh::lean_ctor_get(v_i_929_, 0);
                    v___x_943_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_944_ = l_Lean_Syntax_getArg(v_stx_942_, v___x_943_);
                    v___x_945_ = l_Lean_Syntax_isMissing(v___x_944_);
                    crate::leanh::lean_dec(v___x_944_);
                    if v___x_945_ == 0 {
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_stx_942_);
                        crate::leanh::lean_dec_ref_known(v_i_929_, 1);
                        v___x_946_ = l_Lean_Syntax_getRangeWithTrailing_x3f(v_stx_942_, v___x_945_);
                        crate::leanh::lean_dec(v_stx_942_);
                        if crate::leanh::lean_obj_tag(v___x_946_) == 1 {
                            v_val_947_ = crate::leanh::lean_ctor_get(v___x_946_, 0);
                            crate::leanh::lean_inc(v_val_947_);
                            crate::leanh::lean_dec_ref_known(v___x_946_, 1);
                            v___x_948_ = 0;
                            v___x_949_ = l_Lean_Syntax_Range_contains(
                                v_val_947_,
                                v_hoverPos_928_,
                                v___x_948_,
                            );
                            crate::leanh::lean_dec(v_val_947_);
                            return v___x_949_;
                        } else {
                            crate::leanh::lean_dec(v___x_946_);
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
                v___x_931_ = crate::leanh::lean_alloc_ctor(8, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_931_, 0, v_i_929_);
                v___x_932_ = l_Lean_Elab_Info_occursInOrOnBoundary(v___x_931_, v_hoverPos_928_);
                crate::leanh::lean_dec_ref_known(v___x_931_, 1);
                return v___x_932_;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_i_929_) == 7 {
                    v_id_x3f_934_ = crate::leanh::lean_ctor_get(v_i_929_, 1);
                    if crate::leanh::lean_obj_tag(v_id_x3f_934_) == 0 {
                        v_stx_935_ = crate::leanh::lean_ctor_get(v_i_929_, 0);
                        crate::leanh::lean_inc(v_stx_935_);
                        crate::leanh::lean_dec_ref_known(v_i_929_, 3);
                        v___x_936_ = 1;
                        v___x_937_ = l_Lean_Syntax_getRangeWithTrailing_x3f(v_stx_935_, v___x_936_);
                        crate::leanh::lean_dec(v_stx_935_);
                        if crate::leanh::lean_obj_tag(v___x_937_) == 1 {
                            v_val_938_ = crate::leanh::lean_ctor_get(v___x_937_, 0);
                            crate::leanh::lean_inc(v_val_938_);
                            crate::leanh::lean_dec_ref_known(v___x_937_, 1);
                            v___x_939_ = 0;
                            v___x_940_ = l_Lean_Syntax_Range_contains(
                                v_val_938_,
                                v_hoverPos_928_,
                                v___x_939_,
                            );
                            crate::leanh::lean_dec(v_val_938_);
                            return v___x_940_;
                        } else {
                            crate::leanh::lean_dec(v___x_937_);
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
    mut v_hoverPos_951_: *mut crate::leanh::LeanObject,
    mut v_i_952_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_953_: u8 = 0;
    let mut v_r_954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_953_ = l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_containsHoverPos(v_hoverPos_951_, v_i_952_);
    crate::leanh::lean_dec(v_hoverPos_951_);
    v_r_954_ = crate::leanh::lean_box((v_res_953_) as usize);
    return v_r_954_;
}
pub unsafe fn l_panic___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go_spec__0(
    mut v_msg_955_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_956_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_957_ = lean_panic_fn_borrowed(v___x_956_, v_msg_955_);
    return v___x_957_;
}
pub unsafe fn _init_l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_961_ = l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__2;
    v___x_962_ = crate::leanh::lean_unsigned_to_nat(14);
    v___x_963_ = crate::leanh::lean_unsigned_to_nat(22);
    v___x_964_ = l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__1;
    v___x_965_ = l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__0;
    v___x_966_ =
        l_mkPanicMessageWithDecl(v___x_965_, v___x_964_, v___x_963_, v___x_962_, v___x_961_);
    return v___x_966_;
}
pub unsafe fn l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go(
    mut v_fileMap_967_: *mut crate::leanh::LeanObject,
    mut v_hoverPos_968_: *mut crate::leanh::LeanObject,
    mut v_hoverLine_969_: *mut crate::leanh::LeanObject,
    mut v_ctx_970_: *mut crate::leanh::LeanObject,
    mut v_info_971_: *mut crate::leanh::LeanObject,
    mut v_best_972_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_978_: u8 = 0;
    let mut v___x_979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_981_: u8 = 0;
    let mut v___y_983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_line_987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_line_989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_990_: u8 = 0;
    let mut v___y_992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_994_: u8 = 0;
    let mut v___x_995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_info_971_) == 8 {
                    v_i_973_ = crate::leanh::lean_ctor_get(v_info_971_, 0);
                    crate::leanh::lean_inc_ref_n(v_i_973_, 2);
                    v___x_981_ = l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_containsHoverPos(v_hoverPos_968_, v_i_973_);
                    if v___x_981_ == 0 {
                        crate::leanh::lean_dec_ref(v_i_973_);
                        crate::leanh::lean_dec_ref_known(v_info_971_, 1);
                        crate::leanh::lean_dec_ref(v_ctx_970_);
                        crate::leanh::lean_dec_ref(v_fileMap_967_);
                        return v_best_972_;
                    } else {
                        v___x_1004_ = l_Lean_Elab_Info_pos_x3f(v_info_971_);
                        if crate::leanh::lean_obj_tag(v___x_1004_) == 0 {
                            v___x_1005_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__3_once), _init_l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__3);
                            v___x_1006_ = l_panic___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go_spec__0(v___x_1005_);
                            v___y_999_ = v___x_1006_;
                            state = 4;
                            continue;
                        } else {
                            v_val_1007_ = crate::leanh::lean_ctor_get(v___x_1004_, 0);
                            crate::leanh::lean_inc(v_val_1007_);
                            crate::leanh::lean_dec_ref_known(v___x_1004_, 1);
                            v___y_999_ = v_val_1007_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_info_971_);
                    crate::leanh::lean_dec_ref(v_ctx_970_);
                    crate::leanh::lean_dec_ref(v_fileMap_967_);
                    return v_best_972_;
                }
            }
            1 => {
                v___x_978_ = lean_nat_dec_eq(v___y_977_, v___y_976_);
                crate::leanh::lean_dec(v___y_976_);
                crate::leanh::lean_dec(v___y_977_);
                if v___x_978_ == 0 {
                    crate::leanh::lean_dec(v___y_975_);
                    crate::leanh::lean_dec_ref(v_i_973_);
                    crate::leanh::lean_dec_ref(v_ctx_970_);
                    return v_best_972_;
                } else {
                    v___x_979_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_979_, 0, v___y_975_);
                    crate::leanh::lean_ctor_set(v___x_979_, 1, v_ctx_970_);
                    crate::leanh::lean_ctor_set(v___x_979_, 2, v_i_973_);
                    v___x_980_ = lean_array_push(v_best_972_, v___x_979_);
                    return v___x_980_;
                }
            }
            2 => {
                crate::leanh::lean_inc_ref(v_fileMap_967_);
                v___x_986_ = l_Lean_FileMap_toPosition(v_fileMap_967_, v___y_984_);
                crate::leanh::lean_dec(v___y_984_);
                v_line_987_ = crate::leanh::lean_ctor_get(v___x_986_, 0);
                crate::leanh::lean_inc(v_line_987_);
                crate::leanh::lean_dec_ref(v___x_986_);
                v___x_988_ = l_Lean_FileMap_toPosition(v_fileMap_967_, v___y_983_);
                crate::leanh::lean_dec(v___y_983_);
                v_line_989_ = crate::leanh::lean_ctor_get(v___x_988_, 0);
                crate::leanh::lean_inc(v_line_989_);
                crate::leanh::lean_dec_ref(v___x_988_);
                v___x_990_ = lean_nat_dec_eq(v_line_987_, v_hoverLine_969_);
                if v___x_990_ == 0 {
                    if v___x_981_ == 0 {
                        v___y_975_ = v___y_985_;
                        v___y_976_ = v_line_989_;
                        v___y_977_ = v_line_987_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_line_989_);
                        crate::leanh::lean_dec(v_line_987_);
                        crate::leanh::lean_dec(v___y_985_);
                        crate::leanh::lean_dec_ref(v_i_973_);
                        crate::leanh::lean_dec_ref(v_ctx_970_);
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
                    v___x_995_ = crate::leanh::lean_box(0);
                    v___y_983_ = v___y_993_;
                    v___y_984_ = v___y_992_;
                    v___y_985_ = v___x_995_;
                    state = 2;
                    continue;
                } else {
                    v___x_996_ = lean_nat_sub(v_hoverPos_968_, v___y_992_);
                    v___x_997_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_997_, 0, v___x_996_);
                    v___y_983_ = v___y_993_;
                    v___y_984_ = v___y_992_;
                    v___y_985_ = v___x_997_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                v___x_1000_ = l_Lean_Elab_Info_tailPos_x3f(v_info_971_);
                crate::leanh::lean_dec_ref_known(v_info_971_, 1);
                if crate::leanh::lean_obj_tag(v___x_1000_) == 0 {
                    v___x_1001_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__3_once), _init_l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___closed__3);
                    v___x_1002_ = l_panic___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go_spec__0(v___x_1001_);
                    v___y_992_ = v___y_999_;
                    v___y_993_ = v___x_1002_;
                    state = 3;
                    continue;
                } else {
                    v_val_1003_ = crate::leanh::lean_ctor_get(v___x_1000_, 0);
                    crate::leanh::lean_inc(v_val_1003_);
                    crate::leanh::lean_dec_ref_known(v___x_1000_, 1);
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
    mut v_fileMap_1008_: *mut crate::leanh::LeanObject,
    mut v_hoverPos_1009_: *mut crate::leanh::LeanObject,
    mut v_hoverLine_1010_: *mut crate::leanh::LeanObject,
    mut v_ctx_1011_: *mut crate::leanh::LeanObject,
    mut v_info_1012_: *mut crate::leanh::LeanObject,
    mut v_best_1013_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1014_ = l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go(v_fileMap_1008_, v_hoverPos_1009_, v_hoverLine_1010_, v_ctx_1011_, v_info_1012_, v_best_1013_);
    crate::leanh::lean_dec(v_hoverLine_1010_);
    crate::leanh::lean_dec(v_hoverPos_1009_);
    return v_res_1014_;
}
pub unsafe fn l_Lean_Server_Completion_findCompletionInfosAt(
    mut v_fileMap_1015_: *mut crate::leanh::LeanObject,
    mut v_hoverPos_1016_: *mut crate::leanh::LeanObject,
    mut v_cmdStx_1017_: *mut crate::leanh::LeanObject,
    mut v_infoTree_1018_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isComplete_1020_: u8 = 0;
    let mut v_completionInfoCandidates_1021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_line_1026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_completionInfoCandidates_1030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1032_: u8 = 0;
    let mut v_isComplete_1033_: u8 = 0;
    let mut v_completionInfoCandidates_1034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isComplete_1035_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref_n(v_fileMap_1015_, 2);
                v___x_1025_ = l_Lean_FileMap_toPosition(v_fileMap_1015_, v_hoverPos_1016_);
                v_line_1026_ = crate::leanh::lean_ctor_get(v___x_1025_, 0);
                crate::leanh::lean_inc(v_line_1026_);
                crate::leanh::lean_dec_ref(v___x_1025_);
                crate::leanh::lean_inc(v_hoverPos_1016_);
                v___x_1027_ = crate::leanh::lean_alloc_closure(l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_findCompletionInfosAt_go___boxed as *mut core::ffi::c_void, 6, 3);
                crate::leanh::lean_closure_set(v___x_1027_, 0, v_fileMap_1015_);
                crate::leanh::lean_closure_set(v___x_1027_, 1, v_hoverPos_1016_);
                crate::leanh::lean_closure_set(v___x_1027_, 2, v_line_1026_);
                v___x_1028_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1029_ = l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_filterDuplicateCompletionInfos___closed__0;
                crate::leanh::lean_inc_ref(v_infoTree_1018_);
                v_completionInfoCandidates_1030_ = l_Lean_Elab_InfoTree_foldInfo___redArg(
                    v___x_1027_,
                    v___x_1029_,
                    v_infoTree_1018_,
                );
                v___x_1031_ = lean_array_get_size(v_completionInfoCandidates_1030_);
                v___x_1032_ = lean_nat_dec_eq(v___x_1031_, v___x_1028_);
                if v___x_1032_ == 0 {
                    crate::leanh::lean_dec_ref(v_infoTree_1018_);
                    crate::leanh::lean_dec(v_cmdStx_1017_);
                    crate::leanh::lean_dec(v_hoverPos_1016_);
                    crate::leanh::lean_dec_ref(v_fileMap_1015_);
                    v_isComplete_1033_ = 1;
                    v_isComplete_1020_ = v_isComplete_1033_;
                    v_completionInfoCandidates_1021_ = v_completionInfoCandidates_1030_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_completionInfoCandidates_1030_);
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
                crate::leanh::lean_dec_ref(v_completionInfoCandidates_1021_);
                v___x_1023_ = crate::leanh::lean_box((v_isComplete_1020_) as usize);
                v___x_1024_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1024_, 0, v___x_1022_);
                crate::leanh::lean_ctor_set(v___x_1024_, 1, v___x_1023_);
                return v___x_1024_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions___lam__0(
    mut v_x_1036_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_1037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1040_: u8 = 0;
    let mut v_info_1041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1043_: u8 = 0;
    let mut v___x_1044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x3f_1045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1050_: u8 = 0;
    let mut v___x_1051_: u8 = 0;
    let mut v_isSharedCheck_1052_: u8 = 0;
    let mut v_unused_1053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_1037_ = crate::leanh::lean_ctor_get(v_x_1036_, 0);
                v_isSharedCheck_1052_ = (!crate::leanh::lean_is_exclusive(v_x_1036_)) as u8;
                if v_isSharedCheck_1052_ == 0 {
                    v_unused_1053_ = crate::leanh::lean_ctor_get(v_x_1036_, 1);
                    crate::leanh::lean_dec(v_unused_1053_);
                    v___x_1039_ = v_x_1036_;
                    v_isShared_1040_ = v_isSharedCheck_1052_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_1037_);
                    crate::leanh::lean_dec(v_x_1036_);
                    v___x_1039_ = crate::leanh::lean_box(0);
                    v_isShared_1040_ = v_isSharedCheck_1052_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_info_1041_ = crate::leanh::lean_ctor_get(v_fst_1037_, 2);
                crate::leanh::lean_inc_ref(v_info_1041_);
                crate::leanh::lean_dec(v_fst_1037_);
                if crate::leanh::lean_obj_tag(v_info_1041_) == 1 {
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
                v___x_1044_ = crate::leanh::lean_alloc_ctor(8, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1044_, 0, v_info_1041_);
                v_size_x3f_1045_ = l_Lean_Elab_Info_size_x3f(v___x_1044_);
                crate::leanh::lean_dec_ref_known(v___x_1044_, 1);
                v___x_1046_ = crate::leanh::lean_box((v___y_1043_) as usize);
                if v_isShared_1040_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1039_, 1, v_size_x3f_1045_);
                    crate::leanh::lean_ctor_set(v___x_1039_, 0, v___x_1046_);
                    v___x_1048_ = v___x_1039_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1049_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1049_, 0, v___x_1046_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1049_, 1, v_size_x3f_1045_);
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
    mut v_x_1054_: *mut crate::leanh::LeanObject,
    mut v_x_1055_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_1056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1055_) == 0 {
                    return v_x_1054_;
                } else {
                    v_key_1056_ = crate::leanh::lean_ctor_get(v_x_1055_, 0);
                    v_value_1057_ = crate::leanh::lean_ctor_get(v_x_1055_, 1);
                    v_tail_1058_ = crate::leanh::lean_ctor_get(v_x_1055_, 2);
                    crate::leanh::lean_inc(v_value_1057_);
                    crate::leanh::lean_inc(v_key_1056_);
                    v___x_1059_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1059_, 0, v_key_1056_);
                    crate::leanh::lean_ctor_set(v___x_1059_, 1, v_value_1057_);
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
    mut v_x_1062_: *mut crate::leanh::LeanObject,
    mut v_x_1063_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1064_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__3(v_x_1062_, v_x_1063_);
    crate::leanh::lean_dec(v_x_1063_);
    return v_res_1064_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__4(
    mut v_as_1065_: *mut crate::leanh::LeanObject,
    mut v_i_1066_: usize,
    mut v_stop_1067_: usize,
    mut v_b_1068_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1069_: u8 = 0;
    let mut v___x_1070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_as_1075_: *mut crate::leanh::LeanObject,
    mut v_i_1076_: *mut crate::leanh::LeanObject,
    mut v_stop_1077_: *mut crate::leanh::LeanObject,
    mut v_b_1078_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1079_: usize = 0;
    let mut v_stop_boxed_1080_: usize = 0;
    let mut v_res_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1079_ = crate::leanh::lean_unbox_usize(v_i_1076_);
    crate::leanh::lean_dec(v_i_1076_);
    v_stop_boxed_1080_ = crate::leanh::lean_unbox_usize(v_stop_1077_);
    crate::leanh::lean_dec(v_stop_1077_);
    v_res_1081_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__4(v_as_1075_, v_i_boxed_1079_, v_stop_boxed_1080_, v_b_1078_);
    crate::leanh::lean_dec_ref(v_as_1075_);
    return v_res_1081_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__0(
    mut v_sz_1082_: usize,
    mut v_i_1083_: usize,
    mut v_bs_1084_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1085_: u8 = 0;
    let mut v_v_1086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: usize = 0;
    let mut v___x_1091_: usize = 0;
    let mut v___x_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1085_ = lean_usize_dec_lt(v_i_1083_, v_sz_1082_);
                if v___x_1085_ == 0 {
                    return v_bs_1084_;
                } else {
                    v_v_1086_ = lean_array_uget_borrowed(v_bs_1084_, v_i_1083_);
                    v_snd_1087_ = crate::leanh::lean_ctor_get(v_v_1086_, 1);
                    crate::leanh::lean_inc(v_snd_1087_);
                    v___x_1088_ = crate::leanh::lean_unsigned_to_nat(0);
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
    mut v_sz_1094_: *mut crate::leanh::LeanObject,
    mut v_i_1095_: *mut crate::leanh::LeanObject,
    mut v_bs_1096_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1097_: usize = 0;
    let mut v_i_boxed_1098_: usize = 0;
    let mut v_res_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1097_ = crate::leanh::lean_unbox_usize(v_sz_1094_);
    crate::leanh::lean_dec(v_sz_1094_);
    v_i_boxed_1098_ = crate::leanh::lean_unbox_usize(v_i_1095_);
    crate::leanh::lean_dec(v_i_1095_);
    v_res_1099_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__0(v_sz_boxed_1097_, v_i_boxed_1098_, v_bs_1096_);
    return v_res_1099_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1___redArg(
    mut v_hi_1100_: *mut crate::leanh::LeanObject,
    mut v_pivot_1101_: *mut crate::leanh::LeanObject,
    mut v_as_1102_: *mut crate::leanh::LeanObject,
    mut v_i_1103_: *mut crate::leanh::LeanObject,
    mut v_k_1104_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1115_: u8 = 0;
    let mut v___x_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
                    crate::leanh::lean_dec(v_k_1104_);
                    v___x_1116_ = lean_array_fswap(v_as_1102_, v_i_1103_, v_hi_1100_);
                    v___x_1117_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1117_, 0, v_i_1103_);
                    crate::leanh::lean_ctor_set(v___x_1117_, 1, v___x_1116_);
                    return v___x_1117_;
                } else {
                    v___x_1118_ = lean_array_fget_borrowed(v_as_1102_, v_k_1104_);
                    v_fst_1119_ = crate::leanh::lean_ctor_get(v___x_1118_, 0);
                    v_fst_1120_ = crate::leanh::lean_ctor_get(v_pivot_1101_, 0);
                    v_fst_1121_ = crate::leanh::lean_ctor_get(v_fst_1119_, 0);
                    v_snd_1122_ = crate::leanh::lean_ctor_get(v_fst_1119_, 1);
                    v_fst_1123_ = crate::leanh::lean_ctor_get(v_fst_1120_, 0);
                    v_snd_1124_ = crate::leanh::lean_ctor_get(v_fst_1120_, 1);
                    if crate::leanh::lean_obj_tag(v_snd_1122_) == 0 {
                        if crate::leanh::lean_obj_tag(v_snd_1124_) == 1 {
                            state = 1;
                            continue;
                        } else {
                            state = 4;
                            continue;
                        }
                    } else {
                        if crate::leanh::lean_obj_tag(v_snd_1124_) == 0 {
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
                v___x_1106_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1107_ = lean_nat_add(v_k_1104_, v___x_1106_);
                crate::leanh::lean_dec(v_k_1104_);
                v_k_1104_ = v___x_1107_;
                state = 0;
                continue;
            }
            2 => {
                v___x_1110_ = lean_array_fswap(v_as_1102_, v_i_1103_, v_k_1104_);
                v___x_1111_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1112_ = lean_nat_add(v_i_1103_, v___x_1111_);
                crate::leanh::lean_dec(v_i_1103_);
                v___x_1113_ = lean_nat_add(v_k_1104_, v___x_1111_);
                crate::leanh::lean_dec(v_k_1104_);
                v_as_1102_ = v___x_1110_;
                v_i_1103_ = v___x_1112_;
                v_k_1104_ = v___x_1113_;
                state = 0;
                continue;
            }
            3 => {
                if crate::leanh::lean_obj_tag(v_snd_1122_) == 1 {
                    if crate::leanh::lean_obj_tag(v_snd_1124_) == 1 {
                        v_val_1126_ = crate::leanh::lean_ctor_get(v_snd_1122_, 0);
                        v_val_1127_ = crate::leanh::lean_ctor_get(v_snd_1124_, 0);
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
                v___x_1130_ = (crate::leanh::lean_unbox(v_fst_1121_) as u8);
                if v___x_1130_ == 0 {
                    v___x_1131_ = (crate::leanh::lean_unbox(v_fst_1123_) as u8);
                    if v___x_1131_ == 1 {
                        state = 2;
                        continue;
                    } else {
                        state = 3;
                        continue;
                    }
                } else {
                    v___x_1132_ = (crate::leanh::lean_unbox(v_fst_1123_) as u8);
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
    mut v_hi_1133_: *mut crate::leanh::LeanObject,
    mut v_pivot_1134_: *mut crate::leanh::LeanObject,
    mut v_as_1135_: *mut crate::leanh::LeanObject,
    mut v_i_1136_: *mut crate::leanh::LeanObject,
    mut v_k_1137_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1138_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1___redArg(v_hi_1133_, v_pivot_1134_, v_as_1135_, v_i_1136_, v_k_1137_);
    crate::leanh::lean_dec_ref(v_pivot_1134_);
    crate::leanh::lean_dec(v_hi_1133_);
    return v_res_1138_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg___lam__0(
    mut v___x_1139_: u8,
    mut v_x_1140_: *mut crate::leanh::LeanObject,
    mut v_x_1141_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_fst_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
                v_fst_1142_ = crate::leanh::lean_ctor_get(v_x_1140_, 0);
                v_fst_1143_ = crate::leanh::lean_ctor_get(v_x_1141_, 0);
                v_fst_1144_ = crate::leanh::lean_ctor_get(v_fst_1142_, 0);
                v_snd_1145_ = crate::leanh::lean_ctor_get(v_fst_1142_, 1);
                v_fst_1146_ = crate::leanh::lean_ctor_get(v_fst_1143_, 0);
                v_snd_1147_ = crate::leanh::lean_ctor_get(v_fst_1143_, 1);
                if crate::leanh::lean_obj_tag(v_snd_1145_) == 0 {
                    if crate::leanh::lean_obj_tag(v_snd_1147_) == 1 {
                        v___x_1160_ = 0;
                        return v___x_1160_;
                    } else {
                        state = 2;
                        continue;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v_snd_1147_) == 0 {
                        return v___x_1139_;
                    } else {
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_snd_1145_) == 1 {
                    if crate::leanh::lean_obj_tag(v_snd_1147_) == 1 {
                        v_val_1149_ = crate::leanh::lean_ctor_get(v_snd_1145_, 0);
                        v_val_1150_ = crate::leanh::lean_ctor_get(v_snd_1147_, 0);
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
                v___x_1155_ = (crate::leanh::lean_unbox(v_fst_1144_) as u8);
                if v___x_1155_ == 0 {
                    v___x_1156_ = (crate::leanh::lean_unbox(v_fst_1146_) as u8);
                    if v___x_1156_ == 1 {
                        v___x_1157_ = (crate::leanh::lean_unbox(v_fst_1146_) as u8);
                        return v___x_1157_;
                    } else {
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_1158_ = (crate::leanh::lean_unbox(v_fst_1146_) as u8);
                    if v___x_1158_ == 0 {
                        v___x_1159_ = (crate::leanh::lean_unbox(v_fst_1146_) as u8);
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
    mut v___x_1161_: *mut crate::leanh::LeanObject,
    mut v_x_1162_: *mut crate::leanh::LeanObject,
    mut v_x_1163_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2350__boxed_1164_: u8 = 0;
    let mut v_res_1165_: u8 = 0;
    let mut v_r_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2350__boxed_1164_ = (crate::leanh::lean_unbox(v___x_1161_) as u8);
    v_res_1165_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg___lam__0(v___x_2350__boxed_1164_, v_x_1162_, v_x_1163_);
    crate::leanh::lean_dec_ref(v_x_1163_);
    crate::leanh::lean_dec_ref(v_x_1162_);
    v_r_1166_ = crate::leanh::lean_box((v_res_1165_) as usize);
    return v_r_1166_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg(
    mut v_n_1167_: *mut crate::leanh::LeanObject,
    mut v_as_1168_: *mut crate::leanh::LeanObject,
    mut v_lo_1169_: *mut crate::leanh::LeanObject,
    mut v_hi_1170_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pivot_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1177_: u8 = 0;
    let mut v___x_1178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1182_: u8 = 0;
    let mut v___x_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mid_1185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: u8 = 0;
    let mut v___x_1191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1196_: u8 = 0;
    let mut v___x_1197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: u8 = 0;
    let mut v___x_1201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1182_ = lean_nat_dec_lt(v_lo_1169_, v_hi_1170_);
                if v___x_1182_ == 0 {
                    crate::leanh::lean_dec(v_lo_1169_);
                    return v_as_1168_;
                } else {
                    v___x_1183_ = lean_nat_add(v_lo_1169_, v_hi_1170_);
                    v___x_1184_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_mid_1185_ = lean_nat_shiftr(v___x_1183_, v___x_1184_);
                    crate::leanh::lean_dec(v___x_1183_);
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
                crate::leanh::lean_inc_n(v_lo_1169_, 2);
                v___x_1174_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1___redArg(v_hi_1170_, v_pivot_1173_, v___y_1172_, v_lo_1169_, v_lo_1169_);
                crate::leanh::lean_dec(v_pivot_1173_);
                v_fst_1175_ = crate::leanh::lean_ctor_get(v___x_1174_, 0);
                crate::leanh::lean_inc(v_fst_1175_);
                v_snd_1176_ = crate::leanh::lean_ctor_get(v___x_1174_, 1);
                crate::leanh::lean_inc(v_snd_1176_);
                crate::leanh::lean_dec_ref(v___x_1174_);
                v___x_1177_ = lean_nat_dec_le(v_hi_1170_, v_fst_1175_);
                if v___x_1177_ == 0 {
                    v___x_1178_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg(v_n_1167_, v_snd_1176_, v_lo_1169_, v_fst_1175_);
                    v___x_1179_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1180_ = lean_nat_add(v_fst_1175_, v___x_1179_);
                    crate::leanh::lean_dec(v_fst_1175_);
                    v_as_1168_ = v___x_1178_;
                    v_lo_1169_ = v___x_1180_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_fst_1175_);
                    crate::leanh::lean_dec(v_lo_1169_);
                    return v_snd_1176_;
                }
            }
            2 => {
                v___x_1188_ = lean_array_fget_borrowed(v___y_1187_, v_mid_1185_);
                v___x_1189_ = lean_array_fget_borrowed(v___y_1187_, v_hi_1170_);
                v___x_1190_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg___lam__0(v___x_1182_, v___x_1188_, v___x_1189_);
                if v___x_1190_ == 0 {
                    crate::leanh::lean_dec(v_mid_1185_);
                    v___y_1172_ = v___y_1187_;
                    state = 1;
                    continue;
                } else {
                    v___x_1191_ = lean_array_fswap(v___y_1187_, v_mid_1185_, v_hi_1170_);
                    crate::leanh::lean_dec(v_mid_1185_);
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
    mut v_n_1202_: *mut crate::leanh::LeanObject,
    mut v_as_1203_: *mut crate::leanh::LeanObject,
    mut v_lo_1204_: *mut crate::leanh::LeanObject,
    mut v_hi_1205_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1206_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg(v_n_1202_, v_as_1203_, v_lo_1204_, v_hi_1205_);
    crate::leanh::lean_dec(v_hi_1205_);
    crate::leanh::lean_dec(v_n_1202_);
    return v_res_1206_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5_spec__9_spec__11___redArg(
    mut v_x_1207_: *mut crate::leanh::LeanObject,
    mut v_x_1208_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1214_: u8 = 0;
    let mut v_fst_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_1233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1240_: u64 = 0;
    let mut v___x_1241_: u64 = 0;
    let mut v_val_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
                if crate::leanh::lean_obj_tag(v_x_1208_) == 0 {
                    return v_x_1207_;
                } else {
                    v_key_1209_ = crate::leanh::lean_ctor_get(v_x_1208_, 0);
                    v_value_1210_ = crate::leanh::lean_ctor_get(v_x_1208_, 1);
                    v_tail_1211_ = crate::leanh::lean_ctor_get(v_x_1208_, 2);
                    v_isSharedCheck_1249_ = (!crate::leanh::lean_is_exclusive(v_x_1208_)) as u8;
                    if v_isSharedCheck_1249_ == 0 {
                        v___x_1213_ = v_x_1208_;
                        v_isShared_1214_ = v_isSharedCheck_1249_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1211_);
                        crate::leanh::lean_inc(v_value_1210_);
                        crate::leanh::lean_inc(v_key_1209_);
                        crate::leanh::lean_dec(v_x_1208_);
                        v___x_1213_ = crate::leanh::lean_box(0);
                        v_isShared_1214_ = v_isSharedCheck_1249_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1215_ = crate::leanh::lean_ctor_get(v_key_1209_, 0);
                v_snd_1216_ = crate::leanh::lean_ctor_get(v_key_1209_, 1);
                v___x_1217_ = lean_array_get_size(v_x_1207_);
                v___x_1246_ = (crate::leanh::lean_unbox(v_fst_1215_) as u8);
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
                crate::leanh::lean_inc(v___x_1233_);
                if v_isShared_1214_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1213_, 2, v___x_1233_);
                    v___x_1235_ = v___x_1213_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1238_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1238_, 0, v_key_1209_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1238_, 1, v_value_1210_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1238_, 2, v___x_1233_);
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
                if crate::leanh::lean_obj_tag(v_snd_1216_) == 0 {
                    v___x_1241_ = 11u64;
                    v___y_1219_ = v___y_1240_;
                    v___y_1220_ = v___x_1241_;
                    state = 2;
                    continue;
                } else {
                    v_val_1242_ = crate::leanh::lean_ctor_get(v_snd_1216_, 0);
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
    mut v_i_1250_: *mut crate::leanh::LeanObject,
    mut v_source_1251_: *mut crate::leanh::LeanObject,
    mut v_target_1252_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: u8 = 0;
    let mut v_es_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1253_ = lean_array_get_size(v_source_1251_);
                v___x_1254_ = lean_nat_dec_lt(v_i_1250_, v___x_1253_);
                if v___x_1254_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_1251_);
                    crate::leanh::lean_dec(v_i_1250_);
                    return v_target_1252_;
                } else {
                    v_es_1255_ = lean_array_fget(v_source_1251_, v_i_1250_);
                    v___x_1256_ = crate::leanh::lean_box(0);
                    v_source_1257_ = lean_array_fset(v_source_1251_, v_i_1250_, v___x_1256_);
                    v_target_1258_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5_spec__9_spec__11___redArg(v_target_1252_, v_es_1255_);
                    v___x_1259_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1260_ = lean_nat_add(v_i_1250_, v___x_1259_);
                    crate::leanh::lean_dec(v_i_1250_);
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
    mut v_data_1262_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1263_ = lean_array_get_size(v_data_1262_);
    v___x_1264_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_1265_ = lean_nat_mul(v___x_1263_, v___x_1264_);
    v___x_1266_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1267_ = crate::leanh::lean_box(0);
    v___x_1268_ = lean_mk_array(v_nbuckets_1265_, v___x_1267_);
    v___x_1269_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5_spec__9___redArg(v___x_1266_, v_data_1262_, v___x_1268_);
    return v___x_1269_;
}
pub unsafe fn l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4_spec__7(
    mut v_x_1270_: *mut crate::leanh::LeanObject,
    mut v_x_1271_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_1270_) == 0 {
        if crate::leanh::lean_obj_tag(v_x_1271_) == 0 {
            let mut v___x_1272_: u8 = 0;
            v___x_1272_ = 1;
            return v___x_1272_;
        } else {
            let mut v___x_1273_: u8 = 0;
            v___x_1273_ = 0;
            return v___x_1273_;
        }
    } else {
        if crate::leanh::lean_obj_tag(v_x_1271_) == 0 {
            let mut v___x_1274_: u8 = 0;
            v___x_1274_ = 0;
            return v___x_1274_;
        } else {
            let mut v_val_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1277_: u8 = 0;
            v_val_1275_ = crate::leanh::lean_ctor_get(v_x_1270_, 0);
            v_val_1276_ = crate::leanh::lean_ctor_get(v_x_1271_, 0);
            v___x_1277_ = lean_nat_dec_eq(v_val_1275_, v_val_1276_);
            return v___x_1277_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4_spec__7___boxed(
    mut v_x_1278_: *mut crate::leanh::LeanObject,
    mut v_x_1279_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1280_: u8 = 0;
    let mut v_r_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1280_ = l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4_spec__7(v_x_1278_, v_x_1279_);
    crate::leanh::lean_dec(v_x_1279_);
    crate::leanh::lean_dec(v_x_1278_);
    v_r_1281_ = crate::leanh::lean_box((v_res_1280_) as usize);
    return v_r_1281_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4___redArg(
    mut v_a_1282_: *mut crate::leanh::LeanObject,
    mut v_x_1283_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1284_: u8 = 0;
    let mut v_key_1285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: u8 = 0;
    let mut v___x_1294_: u8 = 0;
    let mut v___x_1295_: u8 = 0;
    let mut v___x_1297_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1283_) == 0 {
                    v___x_1284_ = 0;
                    return v___x_1284_;
                } else {
                    v_key_1285_ = crate::leanh::lean_ctor_get(v_x_1283_, 0);
                    v_tail_1286_ = crate::leanh::lean_ctor_get(v_x_1283_, 2);
                    v_fst_1287_ = crate::leanh::lean_ctor_get(v_key_1285_, 0);
                    v_snd_1288_ = crate::leanh::lean_ctor_get(v_key_1285_, 1);
                    v_fst_1289_ = crate::leanh::lean_ctor_get(v_a_1282_, 0);
                    v_snd_1290_ = crate::leanh::lean_ctor_get(v_a_1282_, 1);
                    v___x_1294_ = (crate::leanh::lean_unbox(v_fst_1287_) as u8);
                    if v___x_1294_ == 0 {
                        v___x_1295_ = (crate::leanh::lean_unbox(v_fst_1289_) as u8);
                        if v___x_1295_ == 0 {
                            state = 1;
                            continue;
                        } else {
                            v_x_1283_ = v_tail_1286_;
                            state = 0;
                            continue;
                        }
                    } else {
                        v___x_1297_ = (crate::leanh::lean_unbox(v_fst_1289_) as u8);
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
    mut v_a_1299_: *mut crate::leanh::LeanObject,
    mut v_x_1300_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1301_: u8 = 0;
    let mut v_r_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1301_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4___redArg(v_a_1299_, v_x_1300_);
    crate::leanh::lean_dec(v_x_1300_);
    crate::leanh::lean_dec_ref(v_a_1299_);
    v_r_1302_ = crate::leanh::lean_box((v_res_1301_) as usize);
    return v_r_1302_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6___redArg___lam__0(
    mut v_a_1305_: *mut crate::leanh::LeanObject,
    mut v_x_1306_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1306_) == 0 {
                    v___x_1311_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6___redArg___lam__0___closed__0;
                    v___y_1308_ = v___x_1311_;
                    state = 1;
                    continue;
                } else {
                    v_val_1312_ = crate::leanh::lean_ctor_get(v_x_1306_, 0);
                    crate::leanh::lean_inc(v_val_1312_);
                    crate::leanh::lean_dec_ref_known(v_x_1306_, 1);
                    v___y_1308_ = v_val_1312_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1309_ = lean_array_push(v___y_1308_, v_a_1305_);
                v___x_1310_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1310_, 0, v___x_1309_);
                return v___x_1310_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6___redArg(
    mut v_a_1313_: *mut crate::leanh::LeanObject,
    mut v_a_1314_: *mut crate::leanh::LeanObject,
    mut v_x_1315_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1325_: u8 = 0;
    let mut v_tail_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: u8 = 0;
    let mut v___x_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: u8 = 0;
    let mut v___x_1342_: u8 = 0;
    let mut v___x_1343_: u8 = 0;
    let mut v_isSharedCheck_1344_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1315_) == 0 {
                    v___x_1316_ = crate::leanh::lean_box(0);
                    v___x_1317_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6___redArg___lam__0(v_a_1313_, v___x_1316_);
                    v_val_1318_ = crate::leanh::lean_ctor_get(v___x_1317_, 0);
                    crate::leanh::lean_inc(v_val_1318_);
                    crate::leanh::lean_dec(v___x_1317_);
                    v___x_1319_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1319_, 0, v_a_1314_);
                    crate::leanh::lean_ctor_set(v___x_1319_, 1, v_val_1318_);
                    crate::leanh::lean_ctor_set(v___x_1319_, 2, v_x_1315_);
                    return v___x_1319_;
                } else {
                    v_key_1320_ = crate::leanh::lean_ctor_get(v_x_1315_, 0);
                    v_value_1321_ = crate::leanh::lean_ctor_get(v_x_1315_, 1);
                    v_tail_1322_ = crate::leanh::lean_ctor_get(v_x_1315_, 2);
                    v_isSharedCheck_1344_ = (!crate::leanh::lean_is_exclusive(v_x_1315_)) as u8;
                    if v_isSharedCheck_1344_ == 0 {
                        v___x_1324_ = v_x_1315_;
                        v_isShared_1325_ = v_isSharedCheck_1344_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1322_);
                        crate::leanh::lean_inc(v_value_1321_);
                        crate::leanh::lean_inc(v_key_1320_);
                        crate::leanh::lean_dec(v_x_1315_);
                        v___x_1324_ = crate::leanh::lean_box(0);
                        v_isShared_1325_ = v_isSharedCheck_1344_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1331_ = crate::leanh::lean_ctor_get(v_key_1320_, 0);
                v_snd_1332_ = crate::leanh::lean_ctor_get(v_key_1320_, 1);
                v_fst_1333_ = crate::leanh::lean_ctor_get(v_a_1314_, 0);
                v_snd_1334_ = crate::leanh::lean_ctor_get(v_a_1314_, 1);
                v___x_1341_ = (crate::leanh::lean_unbox(v_fst_1331_) as u8);
                if v___x_1341_ == 0 {
                    v___x_1342_ = (crate::leanh::lean_unbox(v_fst_1333_) as u8);
                    if v___x_1342_ == 0 {
                        state = 4;
                        continue;
                    } else {
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1343_ = (crate::leanh::lean_unbox(v_fst_1333_) as u8);
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
                    crate::leanh::lean_ctor_set(v___x_1324_, 2, v_tail_1327_);
                    v___x_1329_ = v___x_1324_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1330_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1330_, 0, v_key_1320_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1330_, 1, v_value_1321_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1330_, 2, v_tail_1327_);
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
                    crate::leanh::lean_del_object(v___x_1324_);
                    crate::leanh::lean_dec(v_key_1320_);
                    v___x_1337_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1337_, 0, v_value_1321_);
                    v___x_1338_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6___redArg___lam__0(v_a_1313_, v___x_1337_);
                    v_val_1339_ = crate::leanh::lean_ctor_get(v___x_1338_, 0);
                    crate::leanh::lean_inc(v_val_1339_);
                    crate::leanh::lean_dec(v___x_1338_);
                    v___x_1340_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1340_, 0, v_a_1314_);
                    crate::leanh::lean_ctor_set(v___x_1340_, 1, v_val_1339_);
                    crate::leanh::lean_ctor_set(v___x_1340_, 2, v_tail_1322_);
                    return v___x_1340_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3___redArg(
    mut v_a_1345_: *mut crate::leanh::LeanObject,
    mut v_m_1346_: *mut crate::leanh::LeanObject,
    mut v_a_1347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1351_: usize = 0;
    let mut v___y_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1359_: u8 = 0;
    let mut v_fst_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: u8 = 0;
    let mut v___x_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: u8 = 0;
    let mut v_val_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bkt_x27_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: u8 = 0;
    let mut v___x_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1406_: u64 = 0;
    let mut v___x_1407_: u64 = 0;
    let mut v_val_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
                v_size_1355_ = crate::leanh::lean_ctor_get(v_m_1346_, 0);
                v_buckets_1356_ = crate::leanh::lean_ctor_get(v_m_1346_, 1);
                v_isSharedCheck_1415_ = (!crate::leanh::lean_is_exclusive(v_m_1346_)) as u8;
                if v_isSharedCheck_1415_ == 0 {
                    v___x_1358_ = v_m_1346_;
                    v_isShared_1359_ = v_isSharedCheck_1415_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_1356_);
                    crate::leanh::lean_inc(v_size_1355_);
                    crate::leanh::lean_dec(v_m_1346_);
                    v___x_1358_ = crate::leanh::lean_box(0);
                    v_isShared_1359_ = v_isSharedCheck_1415_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_1353_ = lean_array_uset(v___y_1350_, v___y_1351_, v___y_1349_);
                v___x_1354_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1354_, 0, v___y_1352_);
                crate::leanh::lean_ctor_set(v___x_1354_, 1, v___x_1353_);
                return v___x_1354_;
            }
            2 => {
                v_fst_1360_ = crate::leanh::lean_ctor_get(v_a_1347_, 0);
                v_snd_1361_ = crate::leanh::lean_ctor_get(v_a_1347_, 1);
                v___x_1362_ = lean_array_get_size(v_buckets_1356_);
                v___x_1412_ = (crate::leanh::lean_unbox(v_fst_1360_) as u8);
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
                    v___x_1382_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_1383_ = lean_nat_add(v_size_1355_, v___x_1382_);
                    crate::leanh::lean_dec(v_size_1355_);
                    crate::leanh::lean_inc(v_bkt_1378_);
                    v___x_1384_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1384_, 0, v_a_1347_);
                    crate::leanh::lean_ctor_set(v___x_1384_, 1, v___x_1381_);
                    crate::leanh::lean_ctor_set(v___x_1384_, 2, v_bkt_1378_);
                    v_buckets_x27_1385_ =
                        lean_array_uset(v_buckets_1356_, v___x_1377_, v___x_1384_);
                    v___x_1386_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_1387_ = lean_nat_mul(v_size_x27_1383_, v___x_1386_);
                    v___x_1388_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_1389_ = lean_nat_div(v___x_1387_, v___x_1388_);
                    crate::leanh::lean_dec(v___x_1387_);
                    v___x_1390_ = lean_array_get_size(v_buckets_x27_1385_);
                    v___x_1391_ = lean_nat_dec_le(v___x_1389_, v___x_1390_);
                    crate::leanh::lean_dec(v___x_1389_);
                    if v___x_1391_ == 0 {
                        v_val_1392_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5___redArg(v_buckets_x27_1385_);
                        if v_isShared_1359_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1358_, 1, v_val_1392_);
                            crate::leanh::lean_ctor_set(v___x_1358_, 0, v_size_x27_1383_);
                            v___x_1394_ = v___x_1358_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1395_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_1395_,
                                0,
                                v_size_x27_1383_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1395_, 1, v_val_1392_);
                            v___x_1394_ = v_reuseFailAlloc_1395_;
                            state = 4;
                            continue;
                        }
                    } else {
                        if v_isShared_1359_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1358_, 1, v_buckets_x27_1385_);
                            crate::leanh::lean_ctor_set(v___x_1358_, 0, v_size_x27_1383_);
                            v___x_1397_ = v___x_1358_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_1398_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_1398_,
                                0,
                                v_size_x27_1383_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_1398_,
                                1,
                                v_buckets_x27_1385_,
                            );
                            v___x_1397_ = v_reuseFailAlloc_1398_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_1378_);
                    crate::leanh::lean_del_object(v___x_1358_);
                    v___x_1399_ = crate::leanh::lean_box(0);
                    v_buckets_x27_1400_ =
                        lean_array_uset(v_buckets_1356_, v___x_1377_, v___x_1399_);
                    crate::leanh::lean_inc_ref(v_a_1347_);
                    v_bkt_x27_1401_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6___redArg(v_a_1345_, v_a_1347_, v_bkt_1378_);
                    v___x_1402_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4___redArg(v_a_1347_, v_bkt_x27_1401_);
                    crate::leanh::lean_dec_ref(v_a_1347_);
                    if v___x_1402_ == 0 {
                        v___x_1403_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1404_ = lean_nat_sub(v_size_1355_, v___x_1403_);
                        crate::leanh::lean_dec(v_size_1355_);
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
                if crate::leanh::lean_obj_tag(v_snd_1361_) == 0 {
                    v___x_1407_ = 11u64;
                    v___y_1364_ = v___y_1406_;
                    v___y_1365_ = v___x_1407_;
                    state = 3;
                    continue;
                } else {
                    v_val_1408_ = crate::leanh::lean_ctor_get(v_snd_1361_, 0);
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
    mut v_key_1416_: *mut crate::leanh::LeanObject,
    mut v_as_1417_: *mut crate::leanh::LeanObject,
    mut v_sz_1418_: usize,
    mut v_i_1419_: usize,
    mut v_b_1420_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1421_: u8 = 0;
    let mut v_a_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: usize = 0;
    let mut v___x_1426_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1421_ = lean_usize_dec_lt(v_i_1419_, v_sz_1418_);
                if v___x_1421_ == 0 {
                    crate::leanh::lean_dec_ref(v_key_1416_);
                    return v_b_1420_;
                } else {
                    v_a_1422_ = lean_array_uget_borrowed(v_as_1417_, v_i_1419_);
                    crate::leanh::lean_inc_ref(v_key_1416_);
                    crate::leanh::lean_inc_n(v_a_1422_, 2);
                    v___x_1423_ = crate::leanh::lean_apply_1(v_key_1416_, v_a_1422_);
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
    mut v_key_1428_: *mut crate::leanh::LeanObject,
    mut v_as_1429_: *mut crate::leanh::LeanObject,
    mut v_sz_1430_: *mut crate::leanh::LeanObject,
    mut v_i_1431_: *mut crate::leanh::LeanObject,
    mut v_b_1432_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1433_: usize = 0;
    let mut v_i_boxed_1434_: usize = 0;
    let mut v_res_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1433_ = crate::leanh::lean_unbox_usize(v_sz_1430_);
    crate::leanh::lean_dec(v_sz_1430_);
    v_i_boxed_1434_ = crate::leanh::lean_unbox_usize(v_i_1431_);
    crate::leanh::lean_dec(v_i_1431_);
    v_res_1435_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__4___redArg(v_key_1428_, v_as_1429_, v_sz_boxed_1433_, v_i_boxed_1434_, v_b_1432_);
    crate::leanh::lean_dec_ref(v_as_1429_);
    return v_res_1435_;
}
pub unsafe fn _init_l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1436_ = crate::leanh::lean_box(0);
    v___x_1437_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_1438_ = lean_mk_array(v___x_1437_, v___x_1436_);
    return v___x_1438_;
}
pub unsafe fn _init_l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_groups_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1439_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___closed__0_once), _init_l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___closed__0);
    v___x_1440_ = crate::leanh::lean_unsigned_to_nat(0);
    v_groups_1441_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v_groups_1441_, 0, v___x_1440_);
    crate::leanh::lean_ctor_set(v_groups_1441_, 1, v___x_1439_);
    return v_groups_1441_;
}
pub unsafe fn l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg(
    mut v_key_1442_: *mut crate::leanh::LeanObject,
    mut v_xs_1443_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_groups_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1445_: usize = 0;
    let mut v___x_1446_: usize = 0;
    let mut v___x_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_groups_1444_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___closed__1_once), _init_l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___closed__1);
    v_sz_1445_ = lean_array_size(v_xs_1443_);
    v___x_1446_ = 0usize;
    v___x_1447_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__4___redArg(v_key_1442_, v_xs_1443_, v_sz_1445_, v___x_1446_, v_groups_1444_);
    return v___x_1447_;
}
pub unsafe fn l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg___boxed(
    mut v_key_1448_: *mut crate::leanh::LeanObject,
    mut v_xs_1449_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1450_ = l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg(v_key_1448_, v_xs_1449_);
    crate::leanh::lean_dec_ref(v_xs_1449_);
    return v_res_1450_;
}
pub unsafe fn l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions(
    mut v_items_1452_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1455_: usize = 0;
    let mut v___x_1456_: usize = 0;
    let mut v___x_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: u8 = 0;
    let mut v___y_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: u8 = 0;
    let mut v___x_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: u8 = 0;
    let mut v___f_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_partitions_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: u8 = 0;
    let mut v___x_1486_: u8 = 0;
    let mut v___x_1487_: usize = 0;
    let mut v___x_1488_: usize = 0;
    let mut v___x_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: usize = 0;
    let mut v___x_1491_: usize = 0;
    let mut v___x_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1478_ = l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions___closed__0;
                v_partitions_1479_ = l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg(v___f_1478_, v_items_1452_);
                v_size_1480_ = crate::leanh::lean_ctor_get(v_partitions_1479_, 0);
                crate::leanh::lean_inc(v_size_1480_);
                v_buckets_1481_ = crate::leanh::lean_ctor_get(v_partitions_1479_, 1);
                crate::leanh::lean_inc_ref(v_buckets_1481_);
                crate::leanh::lean_dec_ref(v_partitions_1479_);
                v___x_1482_ = lean_mk_empty_array_with_capacity(v_size_1480_);
                crate::leanh::lean_dec(v_size_1480_);
                v___x_1483_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1484_ = lean_array_get_size(v_buckets_1481_);
                v___x_1485_ = lean_nat_dec_lt(v___x_1483_, v___x_1484_);
                if v___x_1485_ == 0 {
                    crate::leanh::lean_dec_ref(v_buckets_1481_);
                    v___y_1471_ = v___x_1482_;
                    state = 4;
                    continue;
                } else {
                    v___x_1486_ = lean_nat_dec_le(v___x_1484_, v___x_1484_);
                    if v___x_1486_ == 0 {
                        if v___x_1485_ == 0 {
                            crate::leanh::lean_dec_ref(v_buckets_1481_);
                            v___y_1471_ = v___x_1482_;
                            state = 4;
                            continue;
                        } else {
                            v___x_1487_ = 0usize;
                            v___x_1488_ = lean_usize_of_nat(v___x_1484_);
                            v___x_1489_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__4(v_buckets_1481_, v___x_1487_, v___x_1488_, v___x_1482_);
                            crate::leanh::lean_dec_ref(v_buckets_1481_);
                            v___y_1471_ = v___x_1489_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v___x_1490_ = 0usize;
                        v___x_1491_ = lean_usize_of_nat(v___x_1484_);
                        v___x_1492_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__4(v_buckets_1481_, v___x_1490_, v___x_1491_, v___x_1482_);
                        crate::leanh::lean_dec_ref(v_buckets_1481_);
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
                crate::leanh::lean_dec(v___y_1462_);
                crate::leanh::lean_dec(v___y_1459_);
                v___y_1454_ = v___x_1463_;
                state = 1;
                continue;
            }
            3 => {
                v___x_1469_ = lean_nat_dec_le(v___y_1468_, v___y_1467_);
                if v___x_1469_ == 0 {
                    crate::leanh::lean_dec(v___y_1467_);
                    crate::leanh::lean_inc(v___y_1468_);
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
                v___x_1473_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1474_ = lean_nat_dec_eq(v___x_1472_, v___x_1473_);
                if v___x_1474_ == 0 {
                    v___x_1475_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1476_ = lean_nat_sub(v___x_1472_, v___x_1475_);
                    v___x_1477_ = lean_nat_dec_le(v___x_1473_, v___x_1476_);
                    if v___x_1477_ == 0 {
                        crate::leanh::lean_inc(v___x_1476_);
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
    mut v_items_1493_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1494_ = l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions(v_items_1493_);
    crate::leanh::lean_dec_ref(v_items_1493_);
    return v_res_1494_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1(
    mut v_n_1495_: *mut crate::leanh::LeanObject,
    mut v_as_1496_: *mut crate::leanh::LeanObject,
    mut v_lo_1497_: *mut crate::leanh::LeanObject,
    mut v_hi_1498_: *mut crate::leanh::LeanObject,
    mut v_w_1499_: *mut crate::leanh::LeanObject,
    mut v_hlo_1500_: *mut crate::leanh::LeanObject,
    mut v_hhi_1501_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1502_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___redArg(v_n_1495_, v_as_1496_, v_lo_1497_, v_hi_1498_);
    return v___x_1502_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1___boxed(
    mut v_n_1503_: *mut crate::leanh::LeanObject,
    mut v_as_1504_: *mut crate::leanh::LeanObject,
    mut v_lo_1505_: *mut crate::leanh::LeanObject,
    mut v_hi_1506_: *mut crate::leanh::LeanObject,
    mut v_w_1507_: *mut crate::leanh::LeanObject,
    mut v_hlo_1508_: *mut crate::leanh::LeanObject,
    mut v_hhi_1509_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1510_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1(v_n_1503_, v_as_1504_, v_lo_1505_, v_hi_1506_, v_w_1507_, v_hlo_1508_, v_hhi_1509_);
    crate::leanh::lean_dec(v_hi_1506_);
    crate::leanh::lean_dec(v_n_1503_);
    return v_res_1510_;
}
pub unsafe fn l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2(
    mut v_00_u03b2_1511_: *mut crate::leanh::LeanObject,
    mut v_key_1512_: *mut crate::leanh::LeanObject,
    mut v_xs_1513_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1514_ = l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___redArg(v_key_1512_, v_xs_1513_);
    return v___x_1514_;
}
pub unsafe fn l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2___boxed(
    mut v_00_u03b2_1515_: *mut crate::leanh::LeanObject,
    mut v_key_1516_: *mut crate::leanh::LeanObject,
    mut v_xs_1517_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1518_ = l_Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2(v_00_u03b2_1515_, v_key_1516_, v_xs_1517_);
    crate::leanh::lean_dec_ref(v_xs_1517_);
    return v_res_1518_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1(
    mut v_n_1519_: *mut crate::leanh::LeanObject,
    mut v_lo_1520_: *mut crate::leanh::LeanObject,
    mut v_hi_1521_: *mut crate::leanh::LeanObject,
    mut v_hhi_1522_: *mut crate::leanh::LeanObject,
    mut v_pivot_1523_: *mut crate::leanh::LeanObject,
    mut v_as_1524_: *mut crate::leanh::LeanObject,
    mut v_i_1525_: *mut crate::leanh::LeanObject,
    mut v_k_1526_: *mut crate::leanh::LeanObject,
    mut v_ilo_1527_: *mut crate::leanh::LeanObject,
    mut v_ik_1528_: *mut crate::leanh::LeanObject,
    mut v_w_1529_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1530_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1___redArg(v_hi_1521_, v_pivot_1523_, v_as_1524_, v_i_1525_, v_k_1526_);
    return v___x_1530_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1___boxed(
    mut v_n_1531_: *mut crate::leanh::LeanObject,
    mut v_lo_1532_: *mut crate::leanh::LeanObject,
    mut v_hi_1533_: *mut crate::leanh::LeanObject,
    mut v_hhi_1534_: *mut crate::leanh::LeanObject,
    mut v_pivot_1535_: *mut crate::leanh::LeanObject,
    mut v_as_1536_: *mut crate::leanh::LeanObject,
    mut v_i_1537_: *mut crate::leanh::LeanObject,
    mut v_k_1538_: *mut crate::leanh::LeanObject,
    mut v_ilo_1539_: *mut crate::leanh::LeanObject,
    mut v_ik_1540_: *mut crate::leanh::LeanObject,
    mut v_w_1541_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1542_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__1_spec__1(v_n_1531_, v_lo_1532_, v_hi_1533_, v_hhi_1534_, v_pivot_1535_, v_as_1536_, v_i_1537_, v_k_1538_, v_ilo_1539_, v_ik_1540_, v_w_1541_);
    crate::leanh::lean_dec_ref(v_pivot_1535_);
    crate::leanh::lean_dec(v_hi_1533_);
    crate::leanh::lean_dec(v_lo_1532_);
    crate::leanh::lean_dec(v_n_1531_);
    return v_res_1542_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3(
    mut v_00_u03b2_1543_: *mut crate::leanh::LeanObject,
    mut v_a_1544_: *mut crate::leanh::LeanObject,
    mut v_m_1545_: *mut crate::leanh::LeanObject,
    mut v_a_1546_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1547_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3___redArg(v_a_1544_, v_m_1545_, v_a_1546_);
    return v___x_1547_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__4(
    mut v_00_u03b2_1548_: *mut crate::leanh::LeanObject,
    mut v_key_1549_: *mut crate::leanh::LeanObject,
    mut v_as_1550_: *mut crate::leanh::LeanObject,
    mut v_sz_1551_: usize,
    mut v_i_1552_: usize,
    mut v_b_1553_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1554_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__4___redArg(v_key_1549_, v_as_1550_, v_sz_1551_, v_i_1552_, v_b_1553_);
    return v___x_1554_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__4___boxed(
    mut v_00_u03b2_1555_: *mut crate::leanh::LeanObject,
    mut v_key_1556_: *mut crate::leanh::LeanObject,
    mut v_as_1557_: *mut crate::leanh::LeanObject,
    mut v_sz_1558_: *mut crate::leanh::LeanObject,
    mut v_i_1559_: *mut crate::leanh::LeanObject,
    mut v_b_1560_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1561_: usize = 0;
    let mut v_i_boxed_1562_: usize = 0;
    let mut v_res_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1561_ = crate::leanh::lean_unbox_usize(v_sz_1558_);
    crate::leanh::lean_dec(v_sz_1558_);
    v_i_boxed_1562_ = crate::leanh::lean_unbox_usize(v_i_1559_);
    crate::leanh::lean_dec(v_i_1559_);
    v_res_1563_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__4(v_00_u03b2_1555_, v_key_1556_, v_as_1557_, v_sz_boxed_1561_, v_i_boxed_1562_, v_b_1560_);
    crate::leanh::lean_dec_ref(v_as_1557_);
    return v_res_1563_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4(
    mut v_00_u03b2_1564_: *mut crate::leanh::LeanObject,
    mut v_a_1565_: *mut crate::leanh::LeanObject,
    mut v_x_1566_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1567_: u8 = 0;
    v___x_1567_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4___redArg(v_a_1565_, v_x_1566_);
    return v___x_1567_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4___boxed(
    mut v_00_u03b2_1568_: *mut crate::leanh::LeanObject,
    mut v_a_1569_: *mut crate::leanh::LeanObject,
    mut v_x_1570_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1571_: u8 = 0;
    let mut v_r_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1571_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__4(v_00_u03b2_1568_, v_a_1569_, v_x_1570_);
    crate::leanh::lean_dec(v_x_1570_);
    crate::leanh::lean_dec_ref(v_a_1569_);
    v_r_1572_ = crate::leanh::lean_box((v_res_1571_) as usize);
    return v_r_1572_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5(
    mut v_00_u03b2_1573_: *mut crate::leanh::LeanObject,
    mut v_data_1574_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1575_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5___redArg(v_data_1574_);
    return v___x_1575_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6(
    mut v_00_u03b2_1576_: *mut crate::leanh::LeanObject,
    mut v_a_1577_: *mut crate::leanh::LeanObject,
    mut v_a_1578_: *mut crate::leanh::LeanObject,
    mut v_x_1579_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1580_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__6___redArg(v_a_1577_, v_a_1578_, v_x_1579_);
    return v___x_1580_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5_spec__9(
    mut v_00_u03b2_1581_: *mut crate::leanh::LeanObject,
    mut v_i_1582_: *mut crate::leanh::LeanObject,
    mut v_source_1583_: *mut crate::leanh::LeanObject,
    mut v_target_1584_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1585_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5_spec__9___redArg(v_i_1582_, v_source_1583_, v_target_1584_);
    return v___x_1585_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5_spec__9_spec__11(
    mut v_00_u03b2_1586_: *mut crate::leanh::LeanObject,
    mut v_x_1587_: *mut crate::leanh::LeanObject,
    mut v_x_1588_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1589_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Array_groupByKey___at___00__private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions_spec__2_spec__3_spec__5_spec__9_spec__11___redArg(v_x_1587_, v_x_1588_);
    return v___x_1589_;
}
pub unsafe fn l_Lean_Server_Completion_findPrioritizedCompletionPartitionsAt(
    mut v_fileMap_1590_: *mut crate::leanh::LeanObject,
    mut v_hoverPos_1591_: *mut crate::leanh::LeanObject,
    mut v_cmdStx_1592_: *mut crate::leanh::LeanObject,
    mut v_infoTree_1593_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1599_: u8 = 0;
    let mut v___x_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_partitions_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
                v_fst_1595_ = crate::leanh::lean_ctor_get(v___x_1594_, 0);
                v_snd_1596_ = crate::leanh::lean_ctor_get(v___x_1594_, 1);
                v_isSharedCheck_1606_ = (!crate::leanh::lean_is_exclusive(v___x_1594_)) as u8;
                if v_isSharedCheck_1606_ == 0 {
                    v___x_1598_ = v___x_1594_;
                    v_isShared_1599_ = v_isSharedCheck_1606_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1596_);
                    crate::leanh::lean_inc(v_fst_1595_);
                    crate::leanh::lean_dec(v___x_1594_);
                    v___x_1598_ = crate::leanh::lean_box(0);
                    v_isShared_1599_ = v_isSharedCheck_1606_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1600_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1601_ = l_Array_zipIdx___redArg(v_fst_1595_, v___x_1600_);
                crate::leanh::lean_dec(v_fst_1595_);
                v_partitions_1602_ = l___private_Lean_Server_Completion_CompletionInfoSelection_0__Lean_Server_Completion_computePrioritizedCompletionPartitions(v___x_1601_);
                crate::leanh::lean_dec_ref(v___x_1601_);
                if v_isShared_1599_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1598_, 0, v_partitions_1602_);
                    v___x_1604_ = v___x_1598_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1605_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_partitions_1602_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1605_, 1, v_snd_1596_);
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
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Server_Completion_SyntheticCompletion(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Server_Completion_CompletionInfoSelection(
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
pub unsafe fn initialize_Lean_Server_Completion_CompletionInfoSelection(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Server_Completion_SyntheticCompletion(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Server_Completion_CompletionInfoSelection(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Server_Completion_CompletionInfoSelection(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Server_Completion_CompletionInfoSelection(builtin);
}
