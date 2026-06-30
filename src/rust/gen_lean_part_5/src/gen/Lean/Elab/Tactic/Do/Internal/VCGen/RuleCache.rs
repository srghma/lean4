// Lean compiler output
// Module: Lean.Elab.Tactic.Do.Internal.VCGen.RuleCache
// Imports: Lean.Elab.Tactic.Do.VCGen.Split Lean.Elab.Tactic.Do.Internal.VCGen.Context Lean.Elab.Tactic.Do.Internal.VCGen.RuleConstruction Lean.Elab.Tactic.Do.Internal.VCGen.Util
use crate::ffi::{
    lean_array_fget, lean_array_fset, lean_array_get_size, lean_array_uget_borrowed,
    lean_array_uset, lean_expr_eqv, lean_mk_array, lean_name_eq, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_st_ref_get, lean_st_ref_set,
    lean_uint64_mix_hash, lean_uint64_of_nat, lean_uint64_shift_right, lean_uint64_to_usize,
    lean_uint64_xor, lean_usize_land, lean_usize_of_nat, lean_usize_sub,
};
use crate::r#gen::Lean::Elab::Tactic::Do::Internal::VCGen::Context::{
    initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context,
    runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context,
};
use crate::r#gen::Lean::Elab::Tactic::Do::Internal::VCGen::RuleConstruction::{
    initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleConstruction,
    l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplit,
    l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSimpSpec,
    l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpec,
    runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleConstruction,
};
use crate::r#gen::Lean::Elab::Tactic::Do::Internal::VCGen::Util::{
    initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Util,
    runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Util,
};
use crate::r#gen::Lean::Elab::Tactic::Do::VCGen::Split::{
    initialize_Lean_Elab_Tactic_Do_VCGen_Split, runtime_initialize_Lean_Elab_Tactic_Do_VCGen_Split,
};
use crate::r#gen::Lean::Expr::l_Lean_Expr_hash;
use crate::r#gen::Std::Data::DHashMap::Internal::Defs::{
    l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_insert___redArg,
};
static mut l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0: u64 = 0;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg___closed__0_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [105, 116, 101, 0]};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg___closed__0_value) as *mut leanh::LeanObject,18356704233129443855 as *mut leanh::LeanObject] };
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg___closed__2_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [100, 105, 116, 101, 0]};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg___closed__2_value) as *mut leanh::LeanObject,8391571994004792969 as *mut leanh::LeanObject] };
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg___closed__3_value) as *mut leanh::LeanObject;
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache_0__Lean_Elab_Tactic_Do_Internal_Std_HashMap_getDM___redArg___lam__0(
    mut v_inst_568_: *mut leanh::LeanObject,
    mut v_inst_569_: *mut leanh::LeanObject,
    mut v_cache_570_: *mut leanh::LeanObject,
    mut v_key_571_: *mut leanh::LeanObject,
    mut v_toPure_572_: *mut leanh::LeanObject,
    mut v_b_573_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_576_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_b_573_);
    v___x_574_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
        v_inst_568_,
        v_inst_569_,
        v_cache_570_,
        v_key_571_,
        v_b_573_,
    );
    v___x_575_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_575_, 0, v_b_573_);
    leanh::lean_ctor_set(v___x_575_, 1, v___x_574_);
    v___x_576_ = leanh::lean_apply_2(v_toPure_572_, leanh::lean_box(0), v___x_575_);
    return v___x_576_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache_0__Lean_Elab_Tactic_Do_Internal_Std_HashMap_getDM___redArg(
    mut v_inst_577_: *mut leanh::LeanObject,
    mut v_inst_578_: *mut leanh::LeanObject,
    mut v_inst_579_: *mut leanh::LeanObject,
    mut v_cache_580_: *mut leanh::LeanObject,
    mut v_key_581_: *mut leanh::LeanObject,
    mut v_fallback_582_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_587_: u8 = 0;
    let mut v_toPure_588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_597_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_583_ = leanh::lean_ctor_get(v_inst_577_, 0);
                v_toBind_584_ = leanh::lean_ctor_get(v_inst_577_, 1);
                v_isSharedCheck_597_ = (!leanh::lean_is_exclusive(v_inst_577_)) as u8;
                if v_isSharedCheck_597_ == 0 {
                    v___x_586_ = v_inst_577_;
                    v_isShared_587_ = v_isSharedCheck_597_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toBind_584_);
                    leanh::lean_inc(v_toApplicative_583_);
                    leanh::lean_dec(v_inst_577_);
                    v___x_586_ = leanh::lean_box(0);
                    v_isShared_587_ = v_isSharedCheck_597_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_588_ = leanh::lean_ctor_get(v_toApplicative_583_, 1);
                leanh::lean_inc(v_toPure_588_);
                leanh::lean_dec_ref(v_toApplicative_583_);
                leanh::lean_inc(v_key_581_);
                leanh::lean_inc_ref(v_inst_579_);
                leanh::lean_inc_ref(v_inst_578_);
                v___x_589_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(
                    v_inst_578_,
                    v_inst_579_,
                    v_cache_580_,
                    v_key_581_,
                );
                if leanh::lean_obj_tag(v___x_589_) == 1 {
                    leanh::lean_dec(v_toBind_584_);
                    leanh::lean_dec(v_fallback_582_);
                    leanh::lean_dec(v_key_581_);
                    leanh::lean_dec_ref(v_inst_579_);
                    leanh::lean_dec_ref(v_inst_578_);
                    v_val_590_ = leanh::lean_ctor_get(v___x_589_, 0);
                    leanh::lean_inc(v_val_590_);
                    leanh::lean_dec_ref_known(v___x_589_, 1);
                    if v_isShared_587_ == 0 {
                        leanh::lean_ctor_set(v___x_586_, 1, v_cache_580_);
                        leanh::lean_ctor_set(v___x_586_, 0, v_val_590_);
                        v___x_592_ = v___x_586_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_594_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_594_, 0, v_val_590_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_594_, 1, v_cache_580_);
                        v___x_592_ = v_reuseFailAlloc_594_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_589_);
                    leanh::lean_del_object(v___x_586_);
                    v___f_595_ = leanh::lean_alloc_closure(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache_0__Lean_Elab_Tactic_Do_Internal_Std_HashMap_getDM___redArg___lam__0 as *mut core::ffi::c_void, 6, 5);
                    leanh::lean_closure_set(v___f_595_, 0, v_inst_578_);
                    leanh::lean_closure_set(v___f_595_, 1, v_inst_579_);
                    leanh::lean_closure_set(v___f_595_, 2, v_cache_580_);
                    leanh::lean_closure_set(v___f_595_, 3, v_key_581_);
                    leanh::lean_closure_set(v___f_595_, 4, v_toPure_588_);
                    v___x_596_ = leanh::lean_apply_4(
                        v_toBind_584_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v_fallback_582_,
                        v___f_595_,
                    );
                    return v___x_596_;
                }
            }
            2 => {
                v___x_593_ = leanh::lean_apply_2(
                    v_toPure_588_,
                    leanh::lean_box(0),
                    v___x_592_,
                );
                return v___x_593_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache_0__Lean_Elab_Tactic_Do_Internal_Std_HashMap_getDM(
    mut v_m_598_: *mut leanh::LeanObject,
    mut v_00_u03b1_599_: *mut leanh::LeanObject,
    mut v_00_u03b2_600_: *mut leanh::LeanObject,
    mut v_inst_601_: *mut leanh::LeanObject,
    mut v_inst_602_: *mut leanh::LeanObject,
    mut v_inst_603_: *mut leanh::LeanObject,
    mut v_cache_604_: *mut leanh::LeanObject,
    mut v_key_605_: *mut leanh::LeanObject,
    mut v_fallback_606_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_611_: u8 = 0;
    let mut v_toPure_612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_621_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_607_ = leanh::lean_ctor_get(v_inst_601_, 0);
                v_toBind_608_ = leanh::lean_ctor_get(v_inst_601_, 1);
                v_isSharedCheck_621_ = (!leanh::lean_is_exclusive(v_inst_601_)) as u8;
                if v_isSharedCheck_621_ == 0 {
                    v___x_610_ = v_inst_601_;
                    v_isShared_611_ = v_isSharedCheck_621_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toBind_608_);
                    leanh::lean_inc(v_toApplicative_607_);
                    leanh::lean_dec(v_inst_601_);
                    v___x_610_ = leanh::lean_box(0);
                    v_isShared_611_ = v_isSharedCheck_621_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_612_ = leanh::lean_ctor_get(v_toApplicative_607_, 1);
                leanh::lean_inc(v_toPure_612_);
                leanh::lean_dec_ref(v_toApplicative_607_);
                leanh::lean_inc(v_key_605_);
                leanh::lean_inc_ref(v_inst_603_);
                leanh::lean_inc_ref(v_inst_602_);
                v___x_613_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(
                    v_inst_602_,
                    v_inst_603_,
                    v_cache_604_,
                    v_key_605_,
                );
                if leanh::lean_obj_tag(v___x_613_) == 1 {
                    leanh::lean_dec(v_toBind_608_);
                    leanh::lean_dec(v_fallback_606_);
                    leanh::lean_dec(v_key_605_);
                    leanh::lean_dec_ref(v_inst_603_);
                    leanh::lean_dec_ref(v_inst_602_);
                    v_val_614_ = leanh::lean_ctor_get(v___x_613_, 0);
                    leanh::lean_inc(v_val_614_);
                    leanh::lean_dec_ref_known(v___x_613_, 1);
                    if v_isShared_611_ == 0 {
                        leanh::lean_ctor_set(v___x_610_, 1, v_cache_604_);
                        leanh::lean_ctor_set(v___x_610_, 0, v_val_614_);
                        v___x_616_ = v___x_610_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_618_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_618_, 0, v_val_614_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_618_, 1, v_cache_604_);
                        v___x_616_ = v_reuseFailAlloc_618_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_613_);
                    leanh::lean_del_object(v___x_610_);
                    v___f_619_ = leanh::lean_alloc_closure(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache_0__Lean_Elab_Tactic_Do_Internal_Std_HashMap_getDM___redArg___lam__0 as *mut core::ffi::c_void, 6, 5);
                    leanh::lean_closure_set(v___f_619_, 0, v_inst_602_);
                    leanh::lean_closure_set(v___f_619_, 1, v_inst_603_);
                    leanh::lean_closure_set(v___f_619_, 2, v_cache_604_);
                    leanh::lean_closure_set(v___f_619_, 3, v_key_605_);
                    leanh::lean_closure_set(v___f_619_, 4, v_toPure_612_);
                    v___x_620_ = leanh::lean_apply_4(
                        v_toBind_608_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v_fallback_606_,
                        v___f_619_,
                    );
                    return v___x_620_;
                }
            }
            2 => {
                v___x_617_ = leanh::lean_apply_2(
                    v_toPure_612_,
                    leanh::lean_box(0),
                    v___x_616_,
                );
                return v___x_617_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_SpecTheoremNew_global_x3f(
    mut v_specThm_622_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_proof_623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_627_: u8 = 0;
    let mut v___x_629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_631_: u8 = 0;
    let mut v___x_632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_proof_623_ = leanh::lean_ctor_get(v_specThm_622_, 1);
                leanh::lean_inc_ref(v_proof_623_);
                leanh::lean_dec_ref(v_specThm_622_);
                if leanh::lean_obj_tag(v_proof_623_) == 0 {
                    v_declName_624_ = leanh::lean_ctor_get(v_proof_623_, 0);
                    v_isSharedCheck_631_ = (!leanh::lean_is_exclusive(v_proof_623_)) as u8;
                    if v_isSharedCheck_631_ == 0 {
                        v___x_626_ = v_proof_623_;
                        v_isShared_627_ = v_isSharedCheck_631_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_declName_624_);
                        leanh::lean_dec(v_proof_623_);
                        v___x_626_ = leanh::lean_box(0);
                        v_isShared_627_ = v_isSharedCheck_631_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_proof_623_);
                    v___x_632_ = leanh::lean_box(0);
                    return v___x_632_;
                }
            }
            1 => {
                if v_isShared_627_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_626_, 1);
                    v___x_629_ = v___x_626_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_630_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_630_, 0, v_declName_624_);
                    v___x_629_ = v_reuseFailAlloc_630_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_629_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached___lam__0(
    mut v_kind_633_: *mut leanh::LeanObject,
    mut v_specThm_634_: *mut leanh::LeanObject,
    mut v_m_635_: *mut leanh::LeanObject,
    mut v_00_u03c3s_636_: *mut leanh::LeanObject,
    mut v_ps_637_: *mut leanh::LeanObject,
    mut v_instWP_638_: *mut leanh::LeanObject,
    mut v_excessArgs_639_: *mut leanh::LeanObject,
    mut v___y_640_: *mut leanh::LeanObject,
    mut v___y_641_: *mut leanh::LeanObject,
    mut v___y_642_: *mut leanh::LeanObject,
    mut v___y_643_: *mut leanh::LeanObject,
    mut v___y_644_: *mut leanh::LeanObject,
    mut v___y_645_: *mut leanh::LeanObject,
    mut v___y_646_: *mut leanh::LeanObject,
    mut v___y_647_: *mut leanh::LeanObject,
    mut v___y_648_: *mut leanh::LeanObject,
    mut v___y_649_: *mut leanh::LeanObject,
    mut v___y_650_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_kind_633_) == 0 {
        let mut v___x_652_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_652_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpec(
            v_specThm_634_,
            v_m_635_,
            v_00_u03c3s_636_,
            v_ps_637_,
            v_instWP_638_,
            v_excessArgs_639_,
            v___y_645_,
            v___y_646_,
            v___y_647_,
            v___y_648_,
            v___y_649_,
            v___y_650_,
        );
        return v___x_652_;
    } else {
        let mut v___x_653_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_653_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSimpSpec(
            v_specThm_634_,
            v_m_635_,
            v_00_u03c3s_636_,
            v_ps_637_,
            v_instWP_638_,
            v_excessArgs_639_,
            v___y_645_,
            v___y_646_,
            v___y_647_,
            v___y_648_,
            v___y_649_,
            v___y_650_,
        );
        return v___x_653_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached___lam__0___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_kind_654_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_specThm_655_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_m_656_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_00_u03c3s_657_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_ps_658_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_instWP_659_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_excessArgs_660_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___y_661_: *mut leanh::LeanObject = *_args.add(7);
    let mut v___y_662_: *mut leanh::LeanObject = *_args.add(8);
    let mut v___y_663_: *mut leanh::LeanObject = *_args.add(9);
    let mut v___y_664_: *mut leanh::LeanObject = *_args.add(10);
    let mut v___y_665_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___y_666_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___y_667_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___y_668_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___y_669_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_670_: *mut leanh::LeanObject = *_args.add(16);
    let mut v___y_671_: *mut leanh::LeanObject = *_args.add(17);
    let mut v___y_672_: *mut leanh::LeanObject = *_args.add(18);
    let mut v_res_673_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_673_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached___lam__0(
        v_kind_654_,
        v_specThm_655_,
        v_m_656_,
        v_00_u03c3s_657_,
        v_ps_658_,
        v_instWP_659_,
        v_excessArgs_660_,
        v___y_661_,
        v___y_662_,
        v___y_663_,
        v___y_664_,
        v___y_665_,
        v___y_666_,
        v___y_667_,
        v___y_668_,
        v___y_669_,
        v___y_670_,
        v___y_671_,
    );
    leanh::lean_dec(v___y_671_);
    leanh::lean_dec_ref(v___y_670_);
    leanh::lean_dec(v___y_669_);
    leanh::lean_dec_ref(v___y_668_);
    leanh::lean_dec(v___y_667_);
    leanh::lean_dec_ref(v___y_666_);
    leanh::lean_dec(v___y_665_);
    leanh::lean_dec_ref(v___y_664_);
    leanh::lean_dec(v___y_663_);
    leanh::lean_dec(v___y_662_);
    leanh::lean_dec_ref(v___y_661_);
    leanh::lean_dec_ref(v_kind_654_);
    return v_res_673_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg(
    mut v_a_674_: *mut leanh::LeanObject,
    mut v_x_675_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_681_: u8 = 0;
    let mut v___x_683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_688_: u8 = 0;
    let mut v_fst_689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_693_: u8 = 0;
    let mut v___x_694_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_675_) == 0 {
                    v___x_676_ = leanh::lean_box(0);
                    return v___x_676_;
                } else {
                    v_key_677_ = leanh::lean_ctor_get(v_x_675_, 0);
                    v_value_678_ = leanh::lean_ctor_get(v_x_675_, 1);
                    v_tail_679_ = leanh::lean_ctor_get(v_x_675_, 2);
                    v_fst_684_ = leanh::lean_ctor_get(v_key_677_, 0);
                    v_snd_685_ = leanh::lean_ctor_get(v_key_677_, 1);
                    v_fst_686_ = leanh::lean_ctor_get(v_a_674_, 0);
                    v_snd_687_ = leanh::lean_ctor_get(v_a_674_, 1);
                    v___x_688_ = lean_name_eq(v_fst_684_, v_fst_686_);
                    if v___x_688_ == 0 {
                        v___y_681_ = v___x_688_;
                        state = 1;
                        continue;
                    } else {
                        v_fst_689_ = leanh::lean_ctor_get(v_snd_685_, 0);
                        v_snd_690_ = leanh::lean_ctor_get(v_snd_685_, 1);
                        v_fst_691_ = leanh::lean_ctor_get(v_snd_687_, 0);
                        v_snd_692_ = leanh::lean_ctor_get(v_snd_687_, 1);
                        v___x_693_ = lean_expr_eqv(v_fst_689_, v_fst_691_);
                        if v___x_693_ == 0 {
                            v___y_681_ = v___x_693_;
                            state = 1;
                            continue;
                        } else {
                            v___x_694_ = lean_nat_dec_eq(v_snd_690_, v_snd_692_);
                            v___y_681_ = v___x_694_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v___y_681_ == 0 {
                    v_x_675_ = v_tail_679_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_inc(v_value_678_);
                    v___x_683_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_683_, 0, v_value_678_);
                    return v___x_683_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg___boxed(
    mut v_a_695_: *mut leanh::LeanObject,
    mut v_x_696_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_697_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_697_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg(v_a_695_, v_x_696_);
    leanh::lean_dec(v_x_696_);
    leanh::lean_dec_ref(v_a_695_);
    return v_res_697_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0()
-> u64 {
    let mut v___x_698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_699_: u64 = 0;
    v___x_698_ = leanh::lean_unsigned_to_nat(1723);
    v___x_699_ = lean_uint64_of_nat(v___x_698_);
    return v___x_699_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(
    mut v_m_700_: *mut leanh::LeanObject,
    mut v_a_701_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_707_: u64 = 0;
    let mut v_fst_708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_710_: u64 = 0;
    let mut v___x_711_: u64 = 0;
    let mut v___x_712_: u64 = 0;
    let mut v___x_713_: u64 = 0;
    let mut v___x_714_: u64 = 0;
    let mut v___x_715_: u64 = 0;
    let mut v_fold_716_: u64 = 0;
    let mut v___x_717_: u64 = 0;
    let mut v___x_718_: u64 = 0;
    let mut v___x_719_: u64 = 0;
    let mut v___x_720_: usize = 0;
    let mut v___x_721_: usize = 0;
    let mut v___x_722_: usize = 0;
    let mut v___x_723_: usize = 0;
    let mut v___x_724_: usize = 0;
    let mut v___x_725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_727_: u64 = 0;
    let mut v_hash_728_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_702_ = leanh::lean_ctor_get(v_m_700_, 1);
                v_fst_703_ = leanh::lean_ctor_get(v_a_701_, 0);
                v_snd_704_ = leanh::lean_ctor_get(v_a_701_, 1);
                v___x_705_ = lean_array_get_size(v_buckets_702_);
                if leanh::lean_obj_tag(v_fst_703_) == 0 {
                    v___x_727_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0);
                    v___y_707_ = v___x_727_;
                    state = 1;
                    continue;
                } else {
                    v_hash_728_ = leanh::lean_ctor_get_uint64(
                        v_fst_703_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_707_ = v_hash_728_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fst_708_ = leanh::lean_ctor_get(v_snd_704_, 0);
                v_snd_709_ = leanh::lean_ctor_get(v_snd_704_, 1);
                v___x_710_ = l_Lean_Expr_hash(v_fst_708_);
                v___x_711_ = lean_uint64_of_nat(v_snd_709_);
                v___x_712_ = lean_uint64_mix_hash(v___x_710_, v___x_711_);
                v___x_713_ = lean_uint64_mix_hash(v___y_707_, v___x_712_);
                v___x_714_ = 32u64;
                v___x_715_ = lean_uint64_shift_right(v___x_713_, v___x_714_);
                v_fold_716_ = lean_uint64_xor(v___x_713_, v___x_715_);
                v___x_717_ = 16u64;
                v___x_718_ = lean_uint64_shift_right(v_fold_716_, v___x_717_);
                v___x_719_ = lean_uint64_xor(v_fold_716_, v___x_718_);
                v___x_720_ = lean_uint64_to_usize(v___x_719_);
                v___x_721_ = lean_usize_of_nat(v___x_705_);
                v___x_722_ = 1usize;
                v___x_723_ = lean_usize_sub(v___x_721_, v___x_722_);
                v___x_724_ = lean_usize_land(v___x_720_, v___x_723_);
                v___x_725_ = lean_array_uget_borrowed(v_buckets_702_, v___x_724_);
                v___x_726_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg(v_a_701_, v___x_725_);
                return v___x_726_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___boxed(
    mut v_m_729_: *mut leanh::LeanObject,
    mut v_a_730_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_731_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_731_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(v_m_729_, v_a_730_);
    leanh::lean_dec_ref(v_a_730_);
    leanh::lean_dec_ref(v_m_729_);
    return v_res_731_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__3_spec__4_spec__5___redArg(
    mut v_x_732_: *mut leanh::LeanObject,
    mut v_x_733_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_739_: u8 = 0;
    let mut v_fst_740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_744_: u64 = 0;
    let mut v_fst_745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_747_: u64 = 0;
    let mut v___x_748_: u64 = 0;
    let mut v___x_749_: u64 = 0;
    let mut v___x_750_: u64 = 0;
    let mut v___x_751_: u64 = 0;
    let mut v___x_752_: u64 = 0;
    let mut v_fold_753_: u64 = 0;
    let mut v___x_754_: u64 = 0;
    let mut v___x_755_: u64 = 0;
    let mut v___x_756_: u64 = 0;
    let mut v___x_757_: usize = 0;
    let mut v___x_758_: usize = 0;
    let mut v___x_759_: usize = 0;
    let mut v___x_760_: usize = 0;
    let mut v___x_761_: usize = 0;
    let mut v___x_762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_768_: u64 = 0;
    let mut v_hash_769_: u64 = 0;
    let mut v_isSharedCheck_770_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_733_) == 0 {
                    return v_x_732_;
                } else {
                    v_key_734_ = leanh::lean_ctor_get(v_x_733_, 0);
                    v_value_735_ = leanh::lean_ctor_get(v_x_733_, 1);
                    v_tail_736_ = leanh::lean_ctor_get(v_x_733_, 2);
                    v_isSharedCheck_770_ = (!leanh::lean_is_exclusive(v_x_733_)) as u8;
                    if v_isSharedCheck_770_ == 0 {
                        v___x_738_ = v_x_733_;
                        v_isShared_739_ = v_isSharedCheck_770_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_736_);
                        leanh::lean_inc(v_value_735_);
                        leanh::lean_inc(v_key_734_);
                        leanh::lean_dec(v_x_733_);
                        v___x_738_ = leanh::lean_box(0);
                        v_isShared_739_ = v_isSharedCheck_770_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_740_ = leanh::lean_ctor_get(v_key_734_, 0);
                v_snd_741_ = leanh::lean_ctor_get(v_key_734_, 1);
                v___x_742_ = lean_array_get_size(v_x_732_);
                if leanh::lean_obj_tag(v_fst_740_) == 0 {
                    v___x_768_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0);
                    v___y_744_ = v___x_768_;
                    state = 2;
                    continue;
                } else {
                    v_hash_769_ = leanh::lean_ctor_get_uint64(
                        v_fst_740_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_744_ = v_hash_769_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_fst_745_ = leanh::lean_ctor_get(v_snd_741_, 0);
                v_snd_746_ = leanh::lean_ctor_get(v_snd_741_, 1);
                v___x_747_ = l_Lean_Expr_hash(v_fst_745_);
                v___x_748_ = lean_uint64_of_nat(v_snd_746_);
                v___x_749_ = lean_uint64_mix_hash(v___x_747_, v___x_748_);
                v___x_750_ = lean_uint64_mix_hash(v___y_744_, v___x_749_);
                v___x_751_ = 32u64;
                v___x_752_ = lean_uint64_shift_right(v___x_750_, v___x_751_);
                v_fold_753_ = lean_uint64_xor(v___x_750_, v___x_752_);
                v___x_754_ = 16u64;
                v___x_755_ = lean_uint64_shift_right(v_fold_753_, v___x_754_);
                v___x_756_ = lean_uint64_xor(v_fold_753_, v___x_755_);
                v___x_757_ = lean_uint64_to_usize(v___x_756_);
                v___x_758_ = lean_usize_of_nat(v___x_742_);
                v___x_759_ = 1usize;
                v___x_760_ = lean_usize_sub(v___x_758_, v___x_759_);
                v___x_761_ = lean_usize_land(v___x_757_, v___x_760_);
                v___x_762_ = lean_array_uget_borrowed(v_x_732_, v___x_761_);
                leanh::lean_inc(v___x_762_);
                if v_isShared_739_ == 0 {
                    leanh::lean_ctor_set(v___x_738_, 2, v___x_762_);
                    v___x_764_ = v___x_738_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_767_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_767_, 0, v_key_734_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_767_, 1, v_value_735_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_767_, 2, v___x_762_);
                    v___x_764_ = v_reuseFailAlloc_767_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_765_ = lean_array_uset(v_x_732_, v___x_761_, v___x_764_);
                v_x_732_ = v___x_765_;
                v_x_733_ = v_tail_736_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__3_spec__4___redArg(
    mut v_i_771_: *mut leanh::LeanObject,
    mut v_source_772_: *mut leanh::LeanObject,
    mut v_target_773_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_775_: u8 = 0;
    let mut v_es_776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_774_ = lean_array_get_size(v_source_772_);
                v___x_775_ = lean_nat_dec_lt(v_i_771_, v___x_774_);
                if v___x_775_ == 0 {
                    leanh::lean_dec_ref(v_source_772_);
                    leanh::lean_dec(v_i_771_);
                    return v_target_773_;
                } else {
                    v_es_776_ = lean_array_fget(v_source_772_, v_i_771_);
                    v___x_777_ = leanh::lean_box(0);
                    v_source_778_ = lean_array_fset(v_source_772_, v_i_771_, v___x_777_);
                    v_target_779_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__3_spec__4_spec__5___redArg(v_target_773_, v_es_776_);
                    v___x_780_ = leanh::lean_unsigned_to_nat(1);
                    v___x_781_ = lean_nat_add(v_i_771_, v___x_780_);
                    leanh::lean_dec(v_i_771_);
                    v_i_771_ = v___x_781_;
                    v_source_772_ = v_source_778_;
                    v_target_773_ = v_target_779_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__3___redArg(
    mut v_data_783_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_790_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_784_ = lean_array_get_size(v_data_783_);
    v___x_785_ = leanh::lean_unsigned_to_nat(2);
    v_nbuckets_786_ = lean_nat_mul(v___x_784_, v___x_785_);
    v___x_787_ = leanh::lean_unsigned_to_nat(0);
    v___x_788_ = leanh::lean_box(0);
    v___x_789_ = lean_mk_array(v_nbuckets_786_, v___x_788_);
    v___x_790_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__3_spec__4___redArg(v___x_787_, v_data_783_, v___x_789_);
    return v___x_790_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__2___redArg(
    mut v_a_791_: *mut leanh::LeanObject,
    mut v_x_792_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_793_: u8 = 0;
    let mut v_key_794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_797_: u8 = 0;
    let mut v_fst_799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_803_: u8 = 0;
    let mut v_fst_804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_808_: u8 = 0;
    let mut v___x_809_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_792_) == 0 {
                    v___x_793_ = 0;
                    return v___x_793_;
                } else {
                    v_key_794_ = leanh::lean_ctor_get(v_x_792_, 0);
                    v_tail_795_ = leanh::lean_ctor_get(v_x_792_, 2);
                    v_fst_799_ = leanh::lean_ctor_get(v_key_794_, 0);
                    v_snd_800_ = leanh::lean_ctor_get(v_key_794_, 1);
                    v_fst_801_ = leanh::lean_ctor_get(v_a_791_, 0);
                    v_snd_802_ = leanh::lean_ctor_get(v_a_791_, 1);
                    v___x_803_ = lean_name_eq(v_fst_799_, v_fst_801_);
                    if v___x_803_ == 0 {
                        v___y_797_ = v___x_803_;
                        state = 1;
                        continue;
                    } else {
                        v_fst_804_ = leanh::lean_ctor_get(v_snd_800_, 0);
                        v_snd_805_ = leanh::lean_ctor_get(v_snd_800_, 1);
                        v_fst_806_ = leanh::lean_ctor_get(v_snd_802_, 0);
                        v_snd_807_ = leanh::lean_ctor_get(v_snd_802_, 1);
                        v___x_808_ = lean_expr_eqv(v_fst_804_, v_fst_806_);
                        if v___x_808_ == 0 {
                            v___y_797_ = v___x_808_;
                            state = 1;
                            continue;
                        } else {
                            v___x_809_ = lean_nat_dec_eq(v_snd_805_, v_snd_807_);
                            v___y_797_ = v___x_809_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v___y_797_ == 0 {
                    v_x_792_ = v_tail_795_;
                    state = 0;
                    continue;
                } else {
                    return v___y_797_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__2___redArg___boxed(
    mut v_a_810_: *mut leanh::LeanObject,
    mut v_x_811_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_812_: u8 = 0;
    let mut v_r_813_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_812_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__2___redArg(v_a_810_, v_x_811_);
    leanh::lean_dec(v_x_811_);
    leanh::lean_dec_ref(v_a_810_);
    v_r_813_ = leanh::lean_box((v_res_812_) as usize);
    return v_r_813_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__4___redArg(
    mut v_a_814_: *mut leanh::LeanObject,
    mut v_b_815_: *mut leanh::LeanObject,
    mut v_x_816_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_822_: u8 = 0;
    let mut v___y_824_: u8 = 0;
    let mut v___x_825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_836_: u8 = 0;
    let mut v_fst_837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_841_: u8 = 0;
    let mut v___x_842_: u8 = 0;
    let mut v_isSharedCheck_843_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_816_) == 0 {
                    leanh::lean_dec(v_b_815_);
                    leanh::lean_dec_ref(v_a_814_);
                    return v_x_816_;
                } else {
                    v_key_817_ = leanh::lean_ctor_get(v_x_816_, 0);
                    v_value_818_ = leanh::lean_ctor_get(v_x_816_, 1);
                    v_tail_819_ = leanh::lean_ctor_get(v_x_816_, 2);
                    v_isSharedCheck_843_ = (!leanh::lean_is_exclusive(v_x_816_)) as u8;
                    if v_isSharedCheck_843_ == 0 {
                        v___x_821_ = v_x_816_;
                        v_isShared_822_ = v_isSharedCheck_843_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_819_);
                        leanh::lean_inc(v_value_818_);
                        leanh::lean_inc(v_key_817_);
                        leanh::lean_dec(v_x_816_);
                        v___x_821_ = leanh::lean_box(0);
                        v_isShared_822_ = v_isSharedCheck_843_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_832_ = leanh::lean_ctor_get(v_key_817_, 0);
                v_snd_833_ = leanh::lean_ctor_get(v_key_817_, 1);
                v_fst_834_ = leanh::lean_ctor_get(v_a_814_, 0);
                v_snd_835_ = leanh::lean_ctor_get(v_a_814_, 1);
                v___x_836_ = lean_name_eq(v_fst_832_, v_fst_834_);
                if v___x_836_ == 0 {
                    v___y_824_ = v___x_836_;
                    state = 2;
                    continue;
                } else {
                    v_fst_837_ = leanh::lean_ctor_get(v_snd_833_, 0);
                    v_snd_838_ = leanh::lean_ctor_get(v_snd_833_, 1);
                    v_fst_839_ = leanh::lean_ctor_get(v_snd_835_, 0);
                    v_snd_840_ = leanh::lean_ctor_get(v_snd_835_, 1);
                    v___x_841_ = lean_expr_eqv(v_fst_837_, v_fst_839_);
                    if v___x_841_ == 0 {
                        v___y_824_ = v___x_841_;
                        state = 2;
                        continue;
                    } else {
                        v___x_842_ = lean_nat_dec_eq(v_snd_838_, v_snd_840_);
                        v___y_824_ = v___x_842_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v___y_824_ == 0 {
                    v___x_825_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__4___redArg(v_a_814_, v_b_815_, v_tail_819_);
                    if v_isShared_822_ == 0 {
                        leanh::lean_ctor_set(v___x_821_, 2, v___x_825_);
                        v___x_827_ = v___x_821_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_828_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_828_, 0, v_key_817_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_828_, 1, v_value_818_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_828_, 2, v___x_825_);
                        v___x_827_ = v_reuseFailAlloc_828_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_value_818_);
                    leanh::lean_dec(v_key_817_);
                    if v_isShared_822_ == 0 {
                        leanh::lean_ctor_set(v___x_821_, 1, v_b_815_);
                        leanh::lean_ctor_set(v___x_821_, 0, v_a_814_);
                        v___x_830_ = v___x_821_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_831_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_831_, 0, v_a_814_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_831_, 1, v_b_815_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_831_, 2, v_tail_819_);
                        v___x_830_ = v_reuseFailAlloc_831_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_827_;
            }
            4 => {
                return v___x_830_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1___redArg(
    mut v_m_844_: *mut leanh::LeanObject,
    mut v_a_845_: *mut leanh::LeanObject,
    mut v_b_846_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_851_: u8 = 0;
    let mut v_fst_852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_856_: u64 = 0;
    let mut v_fst_857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_859_: u64 = 0;
    let mut v___x_860_: u64 = 0;
    let mut v___x_861_: u64 = 0;
    let mut v___x_862_: u64 = 0;
    let mut v___x_863_: u64 = 0;
    let mut v___x_864_: u64 = 0;
    let mut v_fold_865_: u64 = 0;
    let mut v___x_866_: u64 = 0;
    let mut v___x_867_: u64 = 0;
    let mut v___x_868_: u64 = 0;
    let mut v___x_869_: usize = 0;
    let mut v___x_870_: usize = 0;
    let mut v___x_871_: usize = 0;
    let mut v___x_872_: usize = 0;
    let mut v___x_873_: usize = 0;
    let mut v_bkt_874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_875_: u8 = 0;
    let mut v___x_876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_885_: u8 = 0;
    let mut v_val_886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_900_: u64 = 0;
    let mut v_hash_901_: u64 = 0;
    let mut v_isSharedCheck_902_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_847_ = leanh::lean_ctor_get(v_m_844_, 0);
                v_buckets_848_ = leanh::lean_ctor_get(v_m_844_, 1);
                v_isSharedCheck_902_ = (!leanh::lean_is_exclusive(v_m_844_)) as u8;
                if v_isSharedCheck_902_ == 0 {
                    v___x_850_ = v_m_844_;
                    v_isShared_851_ = v_isSharedCheck_902_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_848_);
                    leanh::lean_inc(v_size_847_);
                    leanh::lean_dec(v_m_844_);
                    v___x_850_ = leanh::lean_box(0);
                    v_isShared_851_ = v_isSharedCheck_902_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fst_852_ = leanh::lean_ctor_get(v_a_845_, 0);
                v_snd_853_ = leanh::lean_ctor_get(v_a_845_, 1);
                v___x_854_ = lean_array_get_size(v_buckets_848_);
                if leanh::lean_obj_tag(v_fst_852_) == 0 {
                    v___x_900_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0);
                    v___y_856_ = v___x_900_;
                    state = 2;
                    continue;
                } else {
                    v_hash_901_ = leanh::lean_ctor_get_uint64(
                        v_fst_852_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_856_ = v_hash_901_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_fst_857_ = leanh::lean_ctor_get(v_snd_853_, 0);
                v_snd_858_ = leanh::lean_ctor_get(v_snd_853_, 1);
                v___x_859_ = l_Lean_Expr_hash(v_fst_857_);
                v___x_860_ = lean_uint64_of_nat(v_snd_858_);
                v___x_861_ = lean_uint64_mix_hash(v___x_859_, v___x_860_);
                v___x_862_ = lean_uint64_mix_hash(v___y_856_, v___x_861_);
                v___x_863_ = 32u64;
                v___x_864_ = lean_uint64_shift_right(v___x_862_, v___x_863_);
                v_fold_865_ = lean_uint64_xor(v___x_862_, v___x_864_);
                v___x_866_ = 16u64;
                v___x_867_ = lean_uint64_shift_right(v_fold_865_, v___x_866_);
                v___x_868_ = lean_uint64_xor(v_fold_865_, v___x_867_);
                v___x_869_ = lean_uint64_to_usize(v___x_868_);
                v___x_870_ = lean_usize_of_nat(v___x_854_);
                v___x_871_ = 1usize;
                v___x_872_ = lean_usize_sub(v___x_870_, v___x_871_);
                v___x_873_ = lean_usize_land(v___x_869_, v___x_872_);
                v_bkt_874_ = lean_array_uget_borrowed(v_buckets_848_, v___x_873_);
                v___x_875_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__2___redArg(v_a_845_, v_bkt_874_);
                if v___x_875_ == 0 {
                    v___x_876_ = leanh::lean_unsigned_to_nat(1);
                    v_size_x27_877_ = lean_nat_add(v_size_847_, v___x_876_);
                    leanh::lean_dec(v_size_847_);
                    leanh::lean_inc(v_bkt_874_);
                    v___x_878_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_878_, 0, v_a_845_);
                    leanh::lean_ctor_set(v___x_878_, 1, v_b_846_);
                    leanh::lean_ctor_set(v___x_878_, 2, v_bkt_874_);
                    v_buckets_x27_879_ = lean_array_uset(v_buckets_848_, v___x_873_, v___x_878_);
                    v___x_880_ = leanh::lean_unsigned_to_nat(4);
                    v___x_881_ = lean_nat_mul(v_size_x27_877_, v___x_880_);
                    v___x_882_ = leanh::lean_unsigned_to_nat(3);
                    v___x_883_ = lean_nat_div(v___x_881_, v___x_882_);
                    leanh::lean_dec(v___x_881_);
                    v___x_884_ = lean_array_get_size(v_buckets_x27_879_);
                    v___x_885_ = lean_nat_dec_le(v___x_883_, v___x_884_);
                    leanh::lean_dec(v___x_883_);
                    if v___x_885_ == 0 {
                        v_val_886_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__3___redArg(v_buckets_x27_879_);
                        if v_isShared_851_ == 0 {
                            leanh::lean_ctor_set(v___x_850_, 1, v_val_886_);
                            leanh::lean_ctor_set(v___x_850_, 0, v_size_x27_877_);
                            v___x_888_ = v___x_850_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_889_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_889_, 0, v_size_x27_877_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_889_, 1, v_val_886_);
                            v___x_888_ = v_reuseFailAlloc_889_;
                            state = 3;
                            continue;
                        }
                    } else {
                        if v_isShared_851_ == 0 {
                            leanh::lean_ctor_set(v___x_850_, 1, v_buckets_x27_879_);
                            leanh::lean_ctor_set(v___x_850_, 0, v_size_x27_877_);
                            v___x_891_ = v___x_850_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_892_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_892_, 0, v_size_x27_877_);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_892_,
                                1,
                                v_buckets_x27_879_,
                            );
                            v___x_891_ = v_reuseFailAlloc_892_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_inc(v_bkt_874_);
                    v___x_893_ = leanh::lean_box(0);
                    v_buckets_x27_894_ = lean_array_uset(v_buckets_848_, v___x_873_, v___x_893_);
                    v___x_895_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__4___redArg(v_a_845_, v_b_846_, v_bkt_874_);
                    v___x_896_ = lean_array_uset(v_buckets_x27_894_, v___x_873_, v___x_895_);
                    if v_isShared_851_ == 0 {
                        leanh::lean_ctor_set(v___x_850_, 1, v___x_896_);
                        v___x_898_ = v___x_850_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_899_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_899_, 0, v_size_847_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_899_, 1, v___x_896_);
                        v___x_898_ = v_reuseFailAlloc_899_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_888_;
            }
            4 => {
                return v___x_891_;
            }
            5 => {
                return v___x_898_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached(
    mut v_specThm_903_: *mut leanh::LeanObject,
    mut v_m_904_: *mut leanh::LeanObject,
    mut v_00_u03c3s_905_: *mut leanh::LeanObject,
    mut v_ps_906_: *mut leanh::LeanObject,
    mut v_instWP_907_: *mut leanh::LeanObject,
    mut v_excessArgs_908_: *mut leanh::LeanObject,
    mut v_a_909_: *mut leanh::LeanObject,
    mut v_a_910_: *mut leanh::LeanObject,
    mut v_a_911_: *mut leanh::LeanObject,
    mut v_a_912_: *mut leanh::LeanObject,
    mut v_a_913_: *mut leanh::LeanObject,
    mut v_a_914_: *mut leanh::LeanObject,
    mut v_a_915_: *mut leanh::LeanObject,
    mut v_a_916_: *mut leanh::LeanObject,
    mut v_a_917_: *mut leanh::LeanObject,
    mut v_a_918_: *mut leanh::LeanObject,
    mut v_a_919_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_927_: u8 = 0;
    let mut v_specBackwardRuleCache_928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_splitBackwardRuleCache_929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invariants_930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vcs_931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_simpState_932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fuel_933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inlineHandledInvariants_934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_preTacFailed_935_: u8 = 0;
    let mut v___x_937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_938_: u8 = 0;
    let mut v_fst_940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_957_: u8 = 0;
    let mut v_isSharedCheck_958_: u8 = 0;
    let mut v___x_959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_921_ = lean_st_ref_get(v_a_910_);
                v_kind_922_ = leanh::lean_ctor_get(v_specThm_903_, 2);
                leanh::lean_inc_ref(v_kind_922_);
                leanh::lean_inc_ref(v_specThm_903_);
                v___x_923_ =
                    l_Lean_Elab_Tactic_Do_Internal_VCGen_SpecTheoremNew_global_x3f(v_specThm_903_);
                if leanh::lean_obj_tag(v___x_923_) == 1 {
                    v_val_924_ = leanh::lean_ctor_get(v___x_923_, 0);
                    v_isSharedCheck_958_ = (!leanh::lean_is_exclusive(v___x_923_)) as u8;
                    if v_isSharedCheck_958_ == 0 {
                        v___x_926_ = v___x_923_;
                        v_isShared_927_ = v_isSharedCheck_958_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_924_);
                        leanh::lean_dec(v___x_923_);
                        v___x_926_ = leanh::lean_box(0);
                        v_isShared_927_ = v_isSharedCheck_958_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_923_);
                    leanh::lean_dec(v___x_921_);
                    v___x_959_ =
                        l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached___lam__0(
                            v_kind_922_,
                            v_specThm_903_,
                            v_m_904_,
                            v_00_u03c3s_905_,
                            v_ps_906_,
                            v_instWP_907_,
                            v_excessArgs_908_,
                            v_a_909_,
                            v_a_910_,
                            v_a_911_,
                            v_a_912_,
                            v_a_913_,
                            v_a_914_,
                            v_a_915_,
                            v_a_916_,
                            v_a_917_,
                            v_a_918_,
                            v_a_919_,
                        );
                    leanh::lean_dec_ref(v_kind_922_);
                    return v___x_959_;
                }
            }
            1 => {
                v_specBackwardRuleCache_928_ = leanh::lean_ctor_get(v___x_921_, 0);
                v_splitBackwardRuleCache_929_ = leanh::lean_ctor_get(v___x_921_, 1);
                v_invariants_930_ = leanh::lean_ctor_get(v___x_921_, 2);
                v_vcs_931_ = leanh::lean_ctor_get(v___x_921_, 3);
                v_simpState_932_ = leanh::lean_ctor_get(v___x_921_, 4);
                v_fuel_933_ = leanh::lean_ctor_get(v___x_921_, 5);
                v_inlineHandledInvariants_934_ = leanh::lean_ctor_get(v___x_921_, 6);
                v_preTacFailed_935_ = leanh::lean_ctor_get_uint8(
                    v___x_921_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                );
                v_isSharedCheck_957_ = (!leanh::lean_is_exclusive(v___x_921_)) as u8;
                if v_isSharedCheck_957_ == 0 {
                    v___x_937_ = v___x_921_;
                    v_isShared_938_ = v_isSharedCheck_957_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_inlineHandledInvariants_934_);
                    leanh::lean_inc(v_fuel_933_);
                    leanh::lean_inc(v_simpState_932_);
                    leanh::lean_inc(v_vcs_931_);
                    leanh::lean_inc(v_invariants_930_);
                    leanh::lean_inc(v_splitBackwardRuleCache_929_);
                    leanh::lean_inc(v_specBackwardRuleCache_928_);
                    leanh::lean_dec(v___x_921_);
                    v___x_937_ = leanh::lean_box(0);
                    v_isShared_938_ = v_isSharedCheck_957_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_949_ = lean_array_get_size(v_excessArgs_908_);
                leanh::lean_inc_ref(v_m_904_);
                v___x_950_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_950_, 0, v_m_904_);
                leanh::lean_ctor_set(v___x_950_, 1, v___x_949_);
                v___x_951_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_951_, 0, v_val_924_);
                leanh::lean_ctor_set(v___x_951_, 1, v___x_950_);
                v___x_952_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(v_specBackwardRuleCache_928_, v___x_951_);
                if leanh::lean_obj_tag(v___x_952_) == 1 {
                    leanh::lean_dec_ref_known(v___x_951_, 2);
                    leanh::lean_dec_ref(v_kind_922_);
                    leanh::lean_dec_ref(v_excessArgs_908_);
                    leanh::lean_dec_ref(v_instWP_907_);
                    leanh::lean_dec_ref(v_ps_906_);
                    leanh::lean_dec_ref(v_00_u03c3s_905_);
                    leanh::lean_dec_ref(v_m_904_);
                    leanh::lean_dec_ref(v_specThm_903_);
                    v_val_953_ = leanh::lean_ctor_get(v___x_952_, 0);
                    leanh::lean_inc(v_val_953_);
                    leanh::lean_dec_ref_known(v___x_952_, 1);
                    v_fst_940_ = v_val_953_;
                    v_snd_941_ = v_specBackwardRuleCache_928_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_dec(v___x_952_);
                    v___x_954_ =
                        l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached___lam__0(
                            v_kind_922_,
                            v_specThm_903_,
                            v_m_904_,
                            v_00_u03c3s_905_,
                            v_ps_906_,
                            v_instWP_907_,
                            v_excessArgs_908_,
                            v_a_909_,
                            v_a_910_,
                            v_a_911_,
                            v_a_912_,
                            v_a_913_,
                            v_a_914_,
                            v_a_915_,
                            v_a_916_,
                            v_a_917_,
                            v_a_918_,
                            v_a_919_,
                        );
                    leanh::lean_dec_ref(v_kind_922_);
                    if leanh::lean_obj_tag(v___x_954_) == 0 {
                        v_a_955_ = leanh::lean_ctor_get(v___x_954_, 0);
                        leanh::lean_inc_n(v_a_955_, 2);
                        leanh::lean_dec_ref_known(v___x_954_, 1);
                        v___x_956_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1___redArg(v_specBackwardRuleCache_928_, v___x_951_, v_a_955_);
                        v_fst_940_ = v_a_955_;
                        v_snd_941_ = v___x_956_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_dec_ref_known(v___x_951_, 2);
                        leanh::lean_del_object(v___x_937_);
                        leanh::lean_dec_ref(v_inlineHandledInvariants_934_);
                        leanh::lean_dec(v_fuel_933_);
                        leanh::lean_dec_ref(v_simpState_932_);
                        leanh::lean_dec_ref(v_vcs_931_);
                        leanh::lean_dec_ref(v_invariants_930_);
                        leanh::lean_dec_ref(v_splitBackwardRuleCache_929_);
                        leanh::lean_dec_ref(v_specBackwardRuleCache_928_);
                        leanh::lean_del_object(v___x_926_);
                        return v___x_954_;
                    }
                }
            }
            3 => {
                if v_isShared_938_ == 0 {
                    leanh::lean_ctor_set(v___x_937_, 0, v_snd_941_);
                    v___x_943_ = v___x_937_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_948_ = leanh::lean_alloc_ctor(0, 7, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_948_, 0, v_snd_941_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_948_,
                        1,
                        v_splitBackwardRuleCache_929_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_948_, 2, v_invariants_930_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_948_, 3, v_vcs_931_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_948_, 4, v_simpState_932_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_948_, 5, v_fuel_933_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_948_,
                        6,
                        v_inlineHandledInvariants_934_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_948_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                        v_preTacFailed_935_,
                    );
                    v___x_943_ = v_reuseFailAlloc_948_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_944_ = lean_st_ref_set(v_a_910_, v___x_943_);
                if v_isShared_927_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_926_, 0);
                    leanh::lean_ctor_set(v___x_926_, 0, v_fst_940_);
                    v___x_946_ = v___x_926_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_947_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_947_, 0, v_fst_940_);
                    v___x_946_ = v_reuseFailAlloc_947_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_946_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_specThm_960_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_m_961_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_00_u03c3s_962_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_ps_963_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_instWP_964_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_excessArgs_965_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_a_966_: *mut leanh::LeanObject = *_args.add(6);
    let mut v_a_967_: *mut leanh::LeanObject = *_args.add(7);
    let mut v_a_968_: *mut leanh::LeanObject = *_args.add(8);
    let mut v_a_969_: *mut leanh::LeanObject = *_args.add(9);
    let mut v_a_970_: *mut leanh::LeanObject = *_args.add(10);
    let mut v_a_971_: *mut leanh::LeanObject = *_args.add(11);
    let mut v_a_972_: *mut leanh::LeanObject = *_args.add(12);
    let mut v_a_973_: *mut leanh::LeanObject = *_args.add(13);
    let mut v_a_974_: *mut leanh::LeanObject = *_args.add(14);
    let mut v_a_975_: *mut leanh::LeanObject = *_args.add(15);
    let mut v_a_976_: *mut leanh::LeanObject = *_args.add(16);
    let mut v_a_977_: *mut leanh::LeanObject = *_args.add(17);
    let mut v_res_978_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_978_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached(
        v_specThm_960_,
        v_m_961_,
        v_00_u03c3s_962_,
        v_ps_963_,
        v_instWP_964_,
        v_excessArgs_965_,
        v_a_966_,
        v_a_967_,
        v_a_968_,
        v_a_969_,
        v_a_970_,
        v_a_971_,
        v_a_972_,
        v_a_973_,
        v_a_974_,
        v_a_975_,
        v_a_976_,
    );
    leanh::lean_dec(v_a_976_);
    leanh::lean_dec_ref(v_a_975_);
    leanh::lean_dec(v_a_974_);
    leanh::lean_dec_ref(v_a_973_);
    leanh::lean_dec(v_a_972_);
    leanh::lean_dec_ref(v_a_971_);
    leanh::lean_dec(v_a_970_);
    leanh::lean_dec_ref(v_a_969_);
    leanh::lean_dec(v_a_968_);
    leanh::lean_dec(v_a_967_);
    leanh::lean_dec_ref(v_a_966_);
    return v_res_978_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0(
    mut v_00_u03b2_979_: *mut leanh::LeanObject,
    mut v_m_980_: *mut leanh::LeanObject,
    mut v_a_981_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_982_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_982_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(v_m_980_, v_a_981_);
    return v___x_982_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___boxed(
    mut v_00_u03b2_983_: *mut leanh::LeanObject,
    mut v_m_984_: *mut leanh::LeanObject,
    mut v_a_985_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_986_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_986_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0(v_00_u03b2_983_, v_m_984_, v_a_985_);
    leanh::lean_dec_ref(v_a_985_);
    leanh::lean_dec_ref(v_m_984_);
    return v_res_986_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1(
    mut v_00_u03b2_987_: *mut leanh::LeanObject,
    mut v_m_988_: *mut leanh::LeanObject,
    mut v_a_989_: *mut leanh::LeanObject,
    mut v_b_990_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_991_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_991_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1___redArg(v_m_988_, v_a_989_, v_b_990_);
    return v___x_991_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0(
    mut v_00_u03b2_992_: *mut leanh::LeanObject,
    mut v_a_993_: *mut leanh::LeanObject,
    mut v_x_994_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_995_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_995_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg(v_a_993_, v_x_994_);
    return v___x_995_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___boxed(
    mut v_00_u03b2_996_: *mut leanh::LeanObject,
    mut v_a_997_: *mut leanh::LeanObject,
    mut v_x_998_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_999_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_999_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0(v_00_u03b2_996_, v_a_997_, v_x_998_);
    leanh::lean_dec(v_x_998_);
    leanh::lean_dec_ref(v_a_997_);
    return v_res_999_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__2(
    mut v_00_u03b2_1000_: *mut leanh::LeanObject,
    mut v_a_1001_: *mut leanh::LeanObject,
    mut v_x_1002_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1003_: u8 = 0;
    v___x_1003_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__2___redArg(v_a_1001_, v_x_1002_);
    return v___x_1003_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__2___boxed(
    mut v_00_u03b2_1004_: *mut leanh::LeanObject,
    mut v_a_1005_: *mut leanh::LeanObject,
    mut v_x_1006_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1007_: u8 = 0;
    let mut v_r_1008_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1007_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__2(v_00_u03b2_1004_, v_a_1005_, v_x_1006_);
    leanh::lean_dec(v_x_1006_);
    leanh::lean_dec_ref(v_a_1005_);
    v_r_1008_ = leanh::lean_box((v_res_1007_) as usize);
    return v_r_1008_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__3(
    mut v_00_u03b2_1009_: *mut leanh::LeanObject,
    mut v_data_1010_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1011_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1011_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__3___redArg(v_data_1010_);
    return v___x_1011_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__4(
    mut v_00_u03b2_1012_: *mut leanh::LeanObject,
    mut v_a_1013_: *mut leanh::LeanObject,
    mut v_b_1014_: *mut leanh::LeanObject,
    mut v_x_1015_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1016_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1016_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__4___redArg(v_a_1013_, v_b_1014_, v_x_1015_);
    return v___x_1016_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__3_spec__4(
    mut v_00_u03b2_1017_: *mut leanh::LeanObject,
    mut v_i_1018_: *mut leanh::LeanObject,
    mut v_source_1019_: *mut leanh::LeanObject,
    mut v_target_1020_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1021_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1021_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__3_spec__4___redArg(v_i_1018_, v_source_1019_, v_target_1020_);
    return v___x_1021_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__3_spec__4_spec__5(
    mut v_00_u03b2_1022_: *mut leanh::LeanObject,
    mut v_x_1023_: *mut leanh::LeanObject,
    mut v_x_1024_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1025_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1025_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__3_spec__4_spec__5___redArg(v_x_1023_, v_x_1024_);
    return v___x_1025_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg(
    mut v_splitInfo_1032_: *mut leanh::LeanObject,
    mut v_m_1033_: *mut leanh::LeanObject,
    mut v_00_u03c3s_1034_: *mut leanh::LeanObject,
    mut v_ps_1035_: *mut leanh::LeanObject,
    mut v_instWP_1036_: *mut leanh::LeanObject,
    mut v_excessArgs_1037_: *mut leanh::LeanObject,
    mut v_a_1038_: *mut leanh::LeanObject,
    mut v_a_1039_: *mut leanh::LeanObject,
    mut v_a_1040_: *mut leanh::LeanObject,
    mut v_a_1041_: *mut leanh::LeanObject,
    mut v_a_1042_: *mut leanh::LeanObject,
    mut v_a_1043_: *mut leanh::LeanObject,
    mut v_a_1044_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_specBackwardRuleCache_1047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invariants_1048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vcs_1049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_simpState_1050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fuel_1051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inlineHandledInvariants_1052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_preTacFailed_1053_: u8 = 0;
    let mut v_fst_1054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_specBackwardRuleCache_1062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_splitBackwardRuleCache_1063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invariants_1064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vcs_1065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_simpState_1066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fuel_1067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inlineHandledInvariants_1068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_preTacFailed_1069_: u8 = 0;
    let mut v___x_1070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_matcherApp_1080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_matcherName_1081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_splitInfo_1032_) {
                0 => {
                    v___x_1078_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg___closed__1;
                    v___y_1060_ = v___x_1078_;
                    state = 2;
                    continue;
                }
                1 => {
                    v___x_1079_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg___closed__3;
                    v___y_1060_ = v___x_1079_;
                    state = 2;
                    continue;
                }
                _ => {
                    v_matcherApp_1080_ = leanh::lean_ctor_get(v_splitInfo_1032_, 0);
                    v_matcherName_1081_ = leanh::lean_ctor_get(v_matcherApp_1080_, 1);
                    leanh::lean_inc(v_matcherName_1081_);
                    v___y_1060_ = v_matcherName_1081_;
                    state = 2;
                    continue;
                }
            },
            1 => {
                v___x_1056_ = leanh::lean_alloc_ctor(0, 7, (1) as u32);
                leanh::lean_ctor_set(v___x_1056_, 0, v_specBackwardRuleCache_1047_);
                leanh::lean_ctor_set(v___x_1056_, 1, v_snd_1055_);
                leanh::lean_ctor_set(v___x_1056_, 2, v_invariants_1048_);
                leanh::lean_ctor_set(v___x_1056_, 3, v_vcs_1049_);
                leanh::lean_ctor_set(v___x_1056_, 4, v_simpState_1050_);
                leanh::lean_ctor_set(v___x_1056_, 5, v_fuel_1051_);
                leanh::lean_ctor_set(v___x_1056_, 6, v_inlineHandledInvariants_1052_);
                leanh::lean_ctor_set_uint8(
                    v___x_1056_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                    v_preTacFailed_1053_,
                );
                v___x_1057_ = lean_st_ref_set(v_a_1038_, v___x_1056_);
                v___x_1058_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1058_, 0, v_fst_1054_);
                return v___x_1058_;
            }
            2 => {
                v___x_1061_ = lean_st_ref_get(v_a_1038_);
                v_specBackwardRuleCache_1062_ = leanh::lean_ctor_get(v___x_1061_, 0);
                leanh::lean_inc_ref(v_specBackwardRuleCache_1062_);
                v_splitBackwardRuleCache_1063_ = leanh::lean_ctor_get(v___x_1061_, 1);
                leanh::lean_inc_ref(v_splitBackwardRuleCache_1063_);
                v_invariants_1064_ = leanh::lean_ctor_get(v___x_1061_, 2);
                leanh::lean_inc_ref(v_invariants_1064_);
                v_vcs_1065_ = leanh::lean_ctor_get(v___x_1061_, 3);
                leanh::lean_inc_ref(v_vcs_1065_);
                v_simpState_1066_ = leanh::lean_ctor_get(v___x_1061_, 4);
                leanh::lean_inc_ref(v_simpState_1066_);
                v_fuel_1067_ = leanh::lean_ctor_get(v___x_1061_, 5);
                leanh::lean_inc(v_fuel_1067_);
                v_inlineHandledInvariants_1068_ = leanh::lean_ctor_get(v___x_1061_, 6);
                leanh::lean_inc_ref(v_inlineHandledInvariants_1068_);
                v_preTacFailed_1069_ = leanh::lean_ctor_get_uint8(
                    v___x_1061_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                );
                leanh::lean_dec(v___x_1061_);
                v___x_1070_ = lean_array_get_size(v_excessArgs_1037_);
                leanh::lean_inc_ref(v_m_1033_);
                v___x_1071_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1071_, 0, v_m_1033_);
                leanh::lean_ctor_set(v___x_1071_, 1, v___x_1070_);
                v___x_1072_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1072_, 0, v___y_1060_);
                leanh::lean_ctor_set(v___x_1072_, 1, v___x_1071_);
                v___x_1073_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(v_splitBackwardRuleCache_1063_, v___x_1072_);
                if leanh::lean_obj_tag(v___x_1073_) == 1 {
                    leanh::lean_dec_ref_known(v___x_1072_, 2);
                    leanh::lean_dec_ref(v_excessArgs_1037_);
                    leanh::lean_dec_ref(v_instWP_1036_);
                    leanh::lean_dec_ref(v_ps_1035_);
                    leanh::lean_dec_ref(v_00_u03c3s_1034_);
                    leanh::lean_dec_ref(v_m_1033_);
                    leanh::lean_dec_ref(v_splitInfo_1032_);
                    v_val_1074_ = leanh::lean_ctor_get(v___x_1073_, 0);
                    leanh::lean_inc(v_val_1074_);
                    leanh::lean_dec_ref_known(v___x_1073_, 1);
                    v_specBackwardRuleCache_1047_ = v_specBackwardRuleCache_1062_;
                    v_invariants_1048_ = v_invariants_1064_;
                    v_vcs_1049_ = v_vcs_1065_;
                    v_simpState_1050_ = v_simpState_1066_;
                    v_fuel_1051_ = v_fuel_1067_;
                    v_inlineHandledInvariants_1052_ = v_inlineHandledInvariants_1068_;
                    v_preTacFailed_1053_ = v_preTacFailed_1069_;
                    v_fst_1054_ = v_val_1074_;
                    v_snd_1055_ = v_splitBackwardRuleCache_1063_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v___x_1073_);
                    v___x_1075_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplit(
                        v_splitInfo_1032_,
                        v_m_1033_,
                        v_00_u03c3s_1034_,
                        v_ps_1035_,
                        v_instWP_1036_,
                        v_excessArgs_1037_,
                        v_a_1039_,
                        v_a_1040_,
                        v_a_1041_,
                        v_a_1042_,
                        v_a_1043_,
                        v_a_1044_,
                    );
                    if leanh::lean_obj_tag(v___x_1075_) == 0 {
                        v_a_1076_ = leanh::lean_ctor_get(v___x_1075_, 0);
                        leanh::lean_inc_n(v_a_1076_, 2);
                        leanh::lean_dec_ref_known(v___x_1075_, 1);
                        v___x_1077_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1___redArg(v_splitBackwardRuleCache_1063_, v___x_1072_, v_a_1076_);
                        v_specBackwardRuleCache_1047_ = v_specBackwardRuleCache_1062_;
                        v_invariants_1048_ = v_invariants_1064_;
                        v_vcs_1049_ = v_vcs_1065_;
                        v_simpState_1050_ = v_simpState_1066_;
                        v_fuel_1051_ = v_fuel_1067_;
                        v_inlineHandledInvariants_1052_ = v_inlineHandledInvariants_1068_;
                        v_preTacFailed_1053_ = v_preTacFailed_1069_;
                        v_fst_1054_ = v_a_1076_;
                        v_snd_1055_ = v___x_1077_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec_ref_known(v___x_1072_, 2);
                        leanh::lean_dec_ref(v_inlineHandledInvariants_1068_);
                        leanh::lean_dec(v_fuel_1067_);
                        leanh::lean_dec_ref(v_simpState_1066_);
                        leanh::lean_dec_ref(v_vcs_1065_);
                        leanh::lean_dec_ref(v_invariants_1064_);
                        leanh::lean_dec_ref(v_splitBackwardRuleCache_1063_);
                        leanh::lean_dec_ref(v_specBackwardRuleCache_1062_);
                        return v___x_1075_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg___boxed(
    mut v_splitInfo_1082_: *mut leanh::LeanObject,
    mut v_m_1083_: *mut leanh::LeanObject,
    mut v_00_u03c3s_1084_: *mut leanh::LeanObject,
    mut v_ps_1085_: *mut leanh::LeanObject,
    mut v_instWP_1086_: *mut leanh::LeanObject,
    mut v_excessArgs_1087_: *mut leanh::LeanObject,
    mut v_a_1088_: *mut leanh::LeanObject,
    mut v_a_1089_: *mut leanh::LeanObject,
    mut v_a_1090_: *mut leanh::LeanObject,
    mut v_a_1091_: *mut leanh::LeanObject,
    mut v_a_1092_: *mut leanh::LeanObject,
    mut v_a_1093_: *mut leanh::LeanObject,
    mut v_a_1094_: *mut leanh::LeanObject,
    mut v_a_1095_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1096_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1096_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg(
        v_splitInfo_1082_,
        v_m_1083_,
        v_00_u03c3s_1084_,
        v_ps_1085_,
        v_instWP_1086_,
        v_excessArgs_1087_,
        v_a_1088_,
        v_a_1089_,
        v_a_1090_,
        v_a_1091_,
        v_a_1092_,
        v_a_1093_,
        v_a_1094_,
    );
    leanh::lean_dec(v_a_1094_);
    leanh::lean_dec_ref(v_a_1093_);
    leanh::lean_dec(v_a_1092_);
    leanh::lean_dec_ref(v_a_1091_);
    leanh::lean_dec(v_a_1090_);
    leanh::lean_dec_ref(v_a_1089_);
    leanh::lean_dec(v_a_1088_);
    return v_res_1096_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached(
    mut v_splitInfo_1097_: *mut leanh::LeanObject,
    mut v_m_1098_: *mut leanh::LeanObject,
    mut v_00_u03c3s_1099_: *mut leanh::LeanObject,
    mut v_ps_1100_: *mut leanh::LeanObject,
    mut v_instWP_1101_: *mut leanh::LeanObject,
    mut v_excessArgs_1102_: *mut leanh::LeanObject,
    mut v_a_1103_: *mut leanh::LeanObject,
    mut v_a_1104_: *mut leanh::LeanObject,
    mut v_a_1105_: *mut leanh::LeanObject,
    mut v_a_1106_: *mut leanh::LeanObject,
    mut v_a_1107_: *mut leanh::LeanObject,
    mut v_a_1108_: *mut leanh::LeanObject,
    mut v_a_1109_: *mut leanh::LeanObject,
    mut v_a_1110_: *mut leanh::LeanObject,
    mut v_a_1111_: *mut leanh::LeanObject,
    mut v_a_1112_: *mut leanh::LeanObject,
    mut v_a_1113_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1115_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1115_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg(
        v_splitInfo_1097_,
        v_m_1098_,
        v_00_u03c3s_1099_,
        v_ps_1100_,
        v_instWP_1101_,
        v_excessArgs_1102_,
        v_a_1104_,
        v_a_1108_,
        v_a_1109_,
        v_a_1110_,
        v_a_1111_,
        v_a_1112_,
        v_a_1113_,
    );
    return v___x_1115_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_splitInfo_1116_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_m_1117_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_00_u03c3s_1118_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_ps_1119_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_instWP_1120_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_excessArgs_1121_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_a_1122_: *mut leanh::LeanObject = *_args.add(6);
    let mut v_a_1123_: *mut leanh::LeanObject = *_args.add(7);
    let mut v_a_1124_: *mut leanh::LeanObject = *_args.add(8);
    let mut v_a_1125_: *mut leanh::LeanObject = *_args.add(9);
    let mut v_a_1126_: *mut leanh::LeanObject = *_args.add(10);
    let mut v_a_1127_: *mut leanh::LeanObject = *_args.add(11);
    let mut v_a_1128_: *mut leanh::LeanObject = *_args.add(12);
    let mut v_a_1129_: *mut leanh::LeanObject = *_args.add(13);
    let mut v_a_1130_: *mut leanh::LeanObject = *_args.add(14);
    let mut v_a_1131_: *mut leanh::LeanObject = *_args.add(15);
    let mut v_a_1132_: *mut leanh::LeanObject = *_args.add(16);
    let mut v_a_1133_: *mut leanh::LeanObject = *_args.add(17);
    let mut v_res_1134_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1134_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached(
        v_splitInfo_1116_,
        v_m_1117_,
        v_00_u03c3s_1118_,
        v_ps_1119_,
        v_instWP_1120_,
        v_excessArgs_1121_,
        v_a_1122_,
        v_a_1123_,
        v_a_1124_,
        v_a_1125_,
        v_a_1126_,
        v_a_1127_,
        v_a_1128_,
        v_a_1129_,
        v_a_1130_,
        v_a_1131_,
        v_a_1132_,
    );
    leanh::lean_dec(v_a_1132_);
    leanh::lean_dec_ref(v_a_1131_);
    leanh::lean_dec(v_a_1130_);
    leanh::lean_dec_ref(v_a_1129_);
    leanh::lean_dec(v_a_1128_);
    leanh::lean_dec_ref(v_a_1127_);
    leanh::lean_dec(v_a_1126_);
    leanh::lean_dec_ref(v_a_1125_);
    leanh::lean_dec(v_a_1124_);
    leanh::lean_dec(v_a_1123_);
    leanh::lean_dec_ref(v_a_1122_);
    return v_res_1134_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Tactic_Do_VCGen_Split(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleConstruction(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache(
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
pub unsafe fn initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Tactic_Do_VCGen_Split(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleConstruction(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache(builtin);
}