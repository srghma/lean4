// Lean compiler output
// Module: Lean.Elab.Tactic.Do.Internal.VCGen.RuleCache
// Imports: Lean.Elab.Tactic.Do.VCGen.Split Lean.Elab.Tactic.Do.Internal.VCGen.Context Lean.Elab.Tactic.Do.Internal.VCGen.RuleConstruction Lean.Elab.Tactic.Do.Internal.VCGen.Util
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
use crate::ffi::{
    lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::ffi::lean_array_fset;
use crate::ffi::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::ffi::{
    lean_uint64_of_nat, lean_usize_of_nat, lean_usize_sub,
};
use crate::ffi::{
    lean_array_fget, lean_array_get_size, lean_name_eq, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_uint64_mix_hash,
};
use crate::ffi::{lean_st_ref_get, lean_st_ref_set};
use crate::ffi::lean_expr_eqv;
static mut l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0: u64 = 0;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg___closed__0_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [105, 116, 101, 0]};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg___closed__0_value) as *mut crate::leanh::LeanObject,18356704233129443855 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg___closed__2_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [100, 105, 116, 101, 0]};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg___closed__2_value) as *mut crate::leanh::LeanObject,8391571994004792969 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg___closed__3_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache_0__Lean_Elab_Tactic_Do_Internal_Std_HashMap_getDM___redArg___lam__0(
    mut v_inst_568_: *mut crate::leanh::LeanObject,
    mut v_inst_569_: *mut crate::leanh::LeanObject,
    mut v_cache_570_: *mut crate::leanh::LeanObject,
    mut v_key_571_: *mut crate::leanh::LeanObject,
    mut v_toPure_572_: *mut crate::leanh::LeanObject,
    mut v_b_573_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_b_573_);
    v___x_574_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
        v_inst_568_,
        v_inst_569_,
        v_cache_570_,
        v_key_571_,
        v_b_573_,
    );
    v___x_575_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_575_, 0, v_b_573_);
    crate::leanh::lean_ctor_set(v___x_575_, 1, v___x_574_);
    v___x_576_ = crate::leanh::lean_apply_2(v_toPure_572_, crate::leanh::lean_box(0), v___x_575_);
    return v___x_576_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache_0__Lean_Elab_Tactic_Do_Internal_Std_HashMap_getDM___redArg(
    mut v_inst_577_: *mut crate::leanh::LeanObject,
    mut v_inst_578_: *mut crate::leanh::LeanObject,
    mut v_inst_579_: *mut crate::leanh::LeanObject,
    mut v_cache_580_: *mut crate::leanh::LeanObject,
    mut v_key_581_: *mut crate::leanh::LeanObject,
    mut v_fallback_582_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_587_: u8 = 0;
    let mut v_toPure_588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_597_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_583_ = crate::leanh::lean_ctor_get(v_inst_577_, 0);
                v_toBind_584_ = crate::leanh::lean_ctor_get(v_inst_577_, 1);
                v_isSharedCheck_597_ = (!crate::leanh::lean_is_exclusive(v_inst_577_)) as u8;
                if v_isSharedCheck_597_ == 0 {
                    v___x_586_ = v_inst_577_;
                    v_isShared_587_ = v_isSharedCheck_597_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toBind_584_);
                    crate::leanh::lean_inc(v_toApplicative_583_);
                    crate::leanh::lean_dec(v_inst_577_);
                    v___x_586_ = crate::leanh::lean_box(0);
                    v_isShared_587_ = v_isSharedCheck_597_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_588_ = crate::leanh::lean_ctor_get(v_toApplicative_583_, 1);
                crate::leanh::lean_inc(v_toPure_588_);
                crate::leanh::lean_dec_ref(v_toApplicative_583_);
                crate::leanh::lean_inc(v_key_581_);
                crate::leanh::lean_inc_ref(v_inst_579_);
                crate::leanh::lean_inc_ref(v_inst_578_);
                v___x_589_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(
                    v_inst_578_,
                    v_inst_579_,
                    v_cache_580_,
                    v_key_581_,
                );
                if crate::leanh::lean_obj_tag(v___x_589_) == 1 {
                    crate::leanh::lean_dec(v_toBind_584_);
                    crate::leanh::lean_dec(v_fallback_582_);
                    crate::leanh::lean_dec(v_key_581_);
                    crate::leanh::lean_dec_ref(v_inst_579_);
                    crate::leanh::lean_dec_ref(v_inst_578_);
                    v_val_590_ = crate::leanh::lean_ctor_get(v___x_589_, 0);
                    crate::leanh::lean_inc(v_val_590_);
                    crate::leanh::lean_dec_ref_known(v___x_589_, 1);
                    if v_isShared_587_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_586_, 1, v_cache_580_);
                        crate::leanh::lean_ctor_set(v___x_586_, 0, v_val_590_);
                        v___x_592_ = v___x_586_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_594_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_594_, 0, v_val_590_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_594_, 1, v_cache_580_);
                        v___x_592_ = v_reuseFailAlloc_594_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_589_);
                    crate::leanh::lean_del_object(v___x_586_);
                    v___f_595_ = crate::leanh::lean_alloc_closure(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache_0__Lean_Elab_Tactic_Do_Internal_Std_HashMap_getDM___redArg___lam__0 as *mut core::ffi::c_void, 6, 5);
                    crate::leanh::lean_closure_set(v___f_595_, 0, v_inst_578_);
                    crate::leanh::lean_closure_set(v___f_595_, 1, v_inst_579_);
                    crate::leanh::lean_closure_set(v___f_595_, 2, v_cache_580_);
                    crate::leanh::lean_closure_set(v___f_595_, 3, v_key_581_);
                    crate::leanh::lean_closure_set(v___f_595_, 4, v_toPure_588_);
                    v___x_596_ = crate::leanh::lean_apply_4(
                        v_toBind_584_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v_fallback_582_,
                        v___f_595_,
                    );
                    return v___x_596_;
                }
            }
            2 => {
                v___x_593_ = crate::leanh::lean_apply_2(
                    v_toPure_588_,
                    crate::leanh::lean_box(0),
                    v___x_592_,
                );
                return v___x_593_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache_0__Lean_Elab_Tactic_Do_Internal_Std_HashMap_getDM(
    mut v_m_598_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_599_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_600_: *mut crate::leanh::LeanObject,
    mut v_inst_601_: *mut crate::leanh::LeanObject,
    mut v_inst_602_: *mut crate::leanh::LeanObject,
    mut v_inst_603_: *mut crate::leanh::LeanObject,
    mut v_cache_604_: *mut crate::leanh::LeanObject,
    mut v_key_605_: *mut crate::leanh::LeanObject,
    mut v_fallback_606_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_611_: u8 = 0;
    let mut v_toPure_612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_621_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_607_ = crate::leanh::lean_ctor_get(v_inst_601_, 0);
                v_toBind_608_ = crate::leanh::lean_ctor_get(v_inst_601_, 1);
                v_isSharedCheck_621_ = (!crate::leanh::lean_is_exclusive(v_inst_601_)) as u8;
                if v_isSharedCheck_621_ == 0 {
                    v___x_610_ = v_inst_601_;
                    v_isShared_611_ = v_isSharedCheck_621_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toBind_608_);
                    crate::leanh::lean_inc(v_toApplicative_607_);
                    crate::leanh::lean_dec(v_inst_601_);
                    v___x_610_ = crate::leanh::lean_box(0);
                    v_isShared_611_ = v_isSharedCheck_621_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_612_ = crate::leanh::lean_ctor_get(v_toApplicative_607_, 1);
                crate::leanh::lean_inc(v_toPure_612_);
                crate::leanh::lean_dec_ref(v_toApplicative_607_);
                crate::leanh::lean_inc(v_key_605_);
                crate::leanh::lean_inc_ref(v_inst_603_);
                crate::leanh::lean_inc_ref(v_inst_602_);
                v___x_613_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(
                    v_inst_602_,
                    v_inst_603_,
                    v_cache_604_,
                    v_key_605_,
                );
                if crate::leanh::lean_obj_tag(v___x_613_) == 1 {
                    crate::leanh::lean_dec(v_toBind_608_);
                    crate::leanh::lean_dec(v_fallback_606_);
                    crate::leanh::lean_dec(v_key_605_);
                    crate::leanh::lean_dec_ref(v_inst_603_);
                    crate::leanh::lean_dec_ref(v_inst_602_);
                    v_val_614_ = crate::leanh::lean_ctor_get(v___x_613_, 0);
                    crate::leanh::lean_inc(v_val_614_);
                    crate::leanh::lean_dec_ref_known(v___x_613_, 1);
                    if v_isShared_611_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_610_, 1, v_cache_604_);
                        crate::leanh::lean_ctor_set(v___x_610_, 0, v_val_614_);
                        v___x_616_ = v___x_610_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_618_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_618_, 0, v_val_614_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_618_, 1, v_cache_604_);
                        v___x_616_ = v_reuseFailAlloc_618_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_613_);
                    crate::leanh::lean_del_object(v___x_610_);
                    v___f_619_ = crate::leanh::lean_alloc_closure(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache_0__Lean_Elab_Tactic_Do_Internal_Std_HashMap_getDM___redArg___lam__0 as *mut core::ffi::c_void, 6, 5);
                    crate::leanh::lean_closure_set(v___f_619_, 0, v_inst_602_);
                    crate::leanh::lean_closure_set(v___f_619_, 1, v_inst_603_);
                    crate::leanh::lean_closure_set(v___f_619_, 2, v_cache_604_);
                    crate::leanh::lean_closure_set(v___f_619_, 3, v_key_605_);
                    crate::leanh::lean_closure_set(v___f_619_, 4, v_toPure_612_);
                    v___x_620_ = crate::leanh::lean_apply_4(
                        v_toBind_608_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v_fallback_606_,
                        v___f_619_,
                    );
                    return v___x_620_;
                }
            }
            2 => {
                v___x_617_ = crate::leanh::lean_apply_2(
                    v_toPure_612_,
                    crate::leanh::lean_box(0),
                    v___x_616_,
                );
                return v___x_617_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_SpecTheoremNew_global_x3f(
    mut v_specThm_622_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_proof_623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_627_: u8 = 0;
    let mut v___x_629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_631_: u8 = 0;
    let mut v___x_632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_proof_623_ = crate::leanh::lean_ctor_get(v_specThm_622_, 1);
                crate::leanh::lean_inc_ref(v_proof_623_);
                crate::leanh::lean_dec_ref(v_specThm_622_);
                if crate::leanh::lean_obj_tag(v_proof_623_) == 0 {
                    v_declName_624_ = crate::leanh::lean_ctor_get(v_proof_623_, 0);
                    v_isSharedCheck_631_ = (!crate::leanh::lean_is_exclusive(v_proof_623_)) as u8;
                    if v_isSharedCheck_631_ == 0 {
                        v___x_626_ = v_proof_623_;
                        v_isShared_627_ = v_isSharedCheck_631_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_declName_624_);
                        crate::leanh::lean_dec(v_proof_623_);
                        v___x_626_ = crate::leanh::lean_box(0);
                        v_isShared_627_ = v_isSharedCheck_631_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_proof_623_);
                    v___x_632_ = crate::leanh::lean_box(0);
                    return v___x_632_;
                }
            }
            1 => {
                if v_isShared_627_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_626_, 1);
                    v___x_629_ = v___x_626_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_630_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_630_, 0, v_declName_624_);
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
    mut v_kind_633_: *mut crate::leanh::LeanObject,
    mut v_specThm_634_: *mut crate::leanh::LeanObject,
    mut v_m_635_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3s_636_: *mut crate::leanh::LeanObject,
    mut v_ps_637_: *mut crate::leanh::LeanObject,
    mut v_instWP_638_: *mut crate::leanh::LeanObject,
    mut v_excessArgs_639_: *mut crate::leanh::LeanObject,
    mut v___y_640_: *mut crate::leanh::LeanObject,
    mut v___y_641_: *mut crate::leanh::LeanObject,
    mut v___y_642_: *mut crate::leanh::LeanObject,
    mut v___y_643_: *mut crate::leanh::LeanObject,
    mut v___y_644_: *mut crate::leanh::LeanObject,
    mut v___y_645_: *mut crate::leanh::LeanObject,
    mut v___y_646_: *mut crate::leanh::LeanObject,
    mut v___y_647_: *mut crate::leanh::LeanObject,
    mut v___y_648_: *mut crate::leanh::LeanObject,
    mut v___y_649_: *mut crate::leanh::LeanObject,
    mut v___y_650_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_kind_633_) == 0 {
        let mut v___x_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
        let mut v___x_653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_654_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_specThm_655_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_m_656_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_00_u03c3s_657_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_ps_658_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_instWP_659_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_excessArgs_660_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___y_661_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___y_662_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_663_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_664_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_665_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_666_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_667_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_668_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_669_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_670_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_671_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___y_672_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v_res_673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v___y_671_);
    crate::leanh::lean_dec_ref(v___y_670_);
    crate::leanh::lean_dec(v___y_669_);
    crate::leanh::lean_dec_ref(v___y_668_);
    crate::leanh::lean_dec(v___y_667_);
    crate::leanh::lean_dec_ref(v___y_666_);
    crate::leanh::lean_dec(v___y_665_);
    crate::leanh::lean_dec_ref(v___y_664_);
    crate::leanh::lean_dec(v___y_663_);
    crate::leanh::lean_dec(v___y_662_);
    crate::leanh::lean_dec_ref(v___y_661_);
    crate::leanh::lean_dec_ref(v_kind_654_);
    return v_res_673_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg(
    mut v_a_674_: *mut crate::leanh::LeanObject,
    mut v_x_675_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_681_: u8 = 0;
    let mut v___x_683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_688_: u8 = 0;
    let mut v_fst_689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_693_: u8 = 0;
    let mut v___x_694_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_675_) == 0 {
                    v___x_676_ = crate::leanh::lean_box(0);
                    return v___x_676_;
                } else {
                    v_key_677_ = crate::leanh::lean_ctor_get(v_x_675_, 0);
                    v_value_678_ = crate::leanh::lean_ctor_get(v_x_675_, 1);
                    v_tail_679_ = crate::leanh::lean_ctor_get(v_x_675_, 2);
                    v_fst_684_ = crate::leanh::lean_ctor_get(v_key_677_, 0);
                    v_snd_685_ = crate::leanh::lean_ctor_get(v_key_677_, 1);
                    v_fst_686_ = crate::leanh::lean_ctor_get(v_a_674_, 0);
                    v_snd_687_ = crate::leanh::lean_ctor_get(v_a_674_, 1);
                    v___x_688_ = lean_name_eq(v_fst_684_, v_fst_686_);
                    if v___x_688_ == 0 {
                        v___y_681_ = v___x_688_;
                        state = 1;
                        continue;
                    } else {
                        v_fst_689_ = crate::leanh::lean_ctor_get(v_snd_685_, 0);
                        v_snd_690_ = crate::leanh::lean_ctor_get(v_snd_685_, 1);
                        v_fst_691_ = crate::leanh::lean_ctor_get(v_snd_687_, 0);
                        v_snd_692_ = crate::leanh::lean_ctor_get(v_snd_687_, 1);
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
                    crate::leanh::lean_inc(v_value_678_);
                    v___x_683_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_683_, 0, v_value_678_);
                    return v___x_683_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg___boxed(
    mut v_a_695_: *mut crate::leanh::LeanObject,
    mut v_x_696_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_697_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg(v_a_695_, v_x_696_);
    crate::leanh::lean_dec(v_x_696_);
    crate::leanh::lean_dec_ref(v_a_695_);
    return v_res_697_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0()
-> u64 {
    let mut v___x_698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_699_: u64 = 0;
    v___x_698_ = crate::leanh::lean_unsigned_to_nat(1723);
    v___x_699_ = lean_uint64_of_nat(v___x_698_);
    return v___x_699_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(
    mut v_m_700_: *mut crate::leanh::LeanObject,
    mut v_a_701_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_707_: u64 = 0;
    let mut v_fst_708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_727_: u64 = 0;
    let mut v_hash_728_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_702_ = crate::leanh::lean_ctor_get(v_m_700_, 1);
                v_fst_703_ = crate::leanh::lean_ctor_get(v_a_701_, 0);
                v_snd_704_ = crate::leanh::lean_ctor_get(v_a_701_, 1);
                v___x_705_ = lean_array_get_size(v_buckets_702_);
                if crate::leanh::lean_obj_tag(v_fst_703_) == 0 {
                    v___x_727_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0);
                    v___y_707_ = v___x_727_;
                    state = 1;
                    continue;
                } else {
                    v_hash_728_ = crate::leanh::lean_ctor_get_uint64(
                        v_fst_703_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_707_ = v_hash_728_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fst_708_ = crate::leanh::lean_ctor_get(v_snd_704_, 0);
                v_snd_709_ = crate::leanh::lean_ctor_get(v_snd_704_, 1);
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
    mut v_m_729_: *mut crate::leanh::LeanObject,
    mut v_a_730_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_731_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(v_m_729_, v_a_730_);
    crate::leanh::lean_dec_ref(v_a_730_);
    crate::leanh::lean_dec_ref(v_m_729_);
    return v_res_731_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__3_spec__4_spec__5___redArg(
    mut v_x_732_: *mut crate::leanh::LeanObject,
    mut v_x_733_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_739_: u8 = 0;
    let mut v_fst_740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_744_: u64 = 0;
    let mut v_fst_745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_768_: u64 = 0;
    let mut v_hash_769_: u64 = 0;
    let mut v_isSharedCheck_770_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_733_) == 0 {
                    return v_x_732_;
                } else {
                    v_key_734_ = crate::leanh::lean_ctor_get(v_x_733_, 0);
                    v_value_735_ = crate::leanh::lean_ctor_get(v_x_733_, 1);
                    v_tail_736_ = crate::leanh::lean_ctor_get(v_x_733_, 2);
                    v_isSharedCheck_770_ = (!crate::leanh::lean_is_exclusive(v_x_733_)) as u8;
                    if v_isSharedCheck_770_ == 0 {
                        v___x_738_ = v_x_733_;
                        v_isShared_739_ = v_isSharedCheck_770_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_736_);
                        crate::leanh::lean_inc(v_value_735_);
                        crate::leanh::lean_inc(v_key_734_);
                        crate::leanh::lean_dec(v_x_733_);
                        v___x_738_ = crate::leanh::lean_box(0);
                        v_isShared_739_ = v_isSharedCheck_770_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_740_ = crate::leanh::lean_ctor_get(v_key_734_, 0);
                v_snd_741_ = crate::leanh::lean_ctor_get(v_key_734_, 1);
                v___x_742_ = lean_array_get_size(v_x_732_);
                if crate::leanh::lean_obj_tag(v_fst_740_) == 0 {
                    v___x_768_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0);
                    v___y_744_ = v___x_768_;
                    state = 2;
                    continue;
                } else {
                    v_hash_769_ = crate::leanh::lean_ctor_get_uint64(
                        v_fst_740_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_744_ = v_hash_769_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_fst_745_ = crate::leanh::lean_ctor_get(v_snd_741_, 0);
                v_snd_746_ = crate::leanh::lean_ctor_get(v_snd_741_, 1);
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
                crate::leanh::lean_inc(v___x_762_);
                if v_isShared_739_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_738_, 2, v___x_762_);
                    v___x_764_ = v___x_738_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_767_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_767_, 0, v_key_734_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_767_, 1, v_value_735_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_767_, 2, v___x_762_);
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
    mut v_i_771_: *mut crate::leanh::LeanObject,
    mut v_source_772_: *mut crate::leanh::LeanObject,
    mut v_target_773_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_775_: u8 = 0;
    let mut v_es_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_774_ = lean_array_get_size(v_source_772_);
                v___x_775_ = lean_nat_dec_lt(v_i_771_, v___x_774_);
                if v___x_775_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_772_);
                    crate::leanh::lean_dec(v_i_771_);
                    return v_target_773_;
                } else {
                    v_es_776_ = lean_array_fget(v_source_772_, v_i_771_);
                    v___x_777_ = crate::leanh::lean_box(0);
                    v_source_778_ = lean_array_fset(v_source_772_, v_i_771_, v___x_777_);
                    v_target_779_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__3_spec__4_spec__5___redArg(v_target_773_, v_es_776_);
                    v___x_780_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_781_ = lean_nat_add(v_i_771_, v___x_780_);
                    crate::leanh::lean_dec(v_i_771_);
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
    mut v_data_783_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_784_ = lean_array_get_size(v_data_783_);
    v___x_785_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_786_ = lean_nat_mul(v___x_784_, v___x_785_);
    v___x_787_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_788_ = crate::leanh::lean_box(0);
    v___x_789_ = lean_mk_array(v_nbuckets_786_, v___x_788_);
    v___x_790_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__3_spec__4___redArg(v___x_787_, v_data_783_, v___x_789_);
    return v___x_790_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__2___redArg(
    mut v_a_791_: *mut crate::leanh::LeanObject,
    mut v_x_792_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_793_: u8 = 0;
    let mut v_key_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_797_: u8 = 0;
    let mut v_fst_799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_803_: u8 = 0;
    let mut v_fst_804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_808_: u8 = 0;
    let mut v___x_809_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_792_) == 0 {
                    v___x_793_ = 0;
                    return v___x_793_;
                } else {
                    v_key_794_ = crate::leanh::lean_ctor_get(v_x_792_, 0);
                    v_tail_795_ = crate::leanh::lean_ctor_get(v_x_792_, 2);
                    v_fst_799_ = crate::leanh::lean_ctor_get(v_key_794_, 0);
                    v_snd_800_ = crate::leanh::lean_ctor_get(v_key_794_, 1);
                    v_fst_801_ = crate::leanh::lean_ctor_get(v_a_791_, 0);
                    v_snd_802_ = crate::leanh::lean_ctor_get(v_a_791_, 1);
                    v___x_803_ = lean_name_eq(v_fst_799_, v_fst_801_);
                    if v___x_803_ == 0 {
                        v___y_797_ = v___x_803_;
                        state = 1;
                        continue;
                    } else {
                        v_fst_804_ = crate::leanh::lean_ctor_get(v_snd_800_, 0);
                        v_snd_805_ = crate::leanh::lean_ctor_get(v_snd_800_, 1);
                        v_fst_806_ = crate::leanh::lean_ctor_get(v_snd_802_, 0);
                        v_snd_807_ = crate::leanh::lean_ctor_get(v_snd_802_, 1);
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
    mut v_a_810_: *mut crate::leanh::LeanObject,
    mut v_x_811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_812_: u8 = 0;
    let mut v_r_813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_812_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__2___redArg(v_a_810_, v_x_811_);
    crate::leanh::lean_dec(v_x_811_);
    crate::leanh::lean_dec_ref(v_a_810_);
    v_r_813_ = crate::leanh::lean_box((v_res_812_) as usize);
    return v_r_813_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__4___redArg(
    mut v_a_814_: *mut crate::leanh::LeanObject,
    mut v_b_815_: *mut crate::leanh::LeanObject,
    mut v_x_816_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_822_: u8 = 0;
    let mut v___y_824_: u8 = 0;
    let mut v___x_825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_836_: u8 = 0;
    let mut v_fst_837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_841_: u8 = 0;
    let mut v___x_842_: u8 = 0;
    let mut v_isSharedCheck_843_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_816_) == 0 {
                    crate::leanh::lean_dec(v_b_815_);
                    crate::leanh::lean_dec_ref(v_a_814_);
                    return v_x_816_;
                } else {
                    v_key_817_ = crate::leanh::lean_ctor_get(v_x_816_, 0);
                    v_value_818_ = crate::leanh::lean_ctor_get(v_x_816_, 1);
                    v_tail_819_ = crate::leanh::lean_ctor_get(v_x_816_, 2);
                    v_isSharedCheck_843_ = (!crate::leanh::lean_is_exclusive(v_x_816_)) as u8;
                    if v_isSharedCheck_843_ == 0 {
                        v___x_821_ = v_x_816_;
                        v_isShared_822_ = v_isSharedCheck_843_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_819_);
                        crate::leanh::lean_inc(v_value_818_);
                        crate::leanh::lean_inc(v_key_817_);
                        crate::leanh::lean_dec(v_x_816_);
                        v___x_821_ = crate::leanh::lean_box(0);
                        v_isShared_822_ = v_isSharedCheck_843_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_832_ = crate::leanh::lean_ctor_get(v_key_817_, 0);
                v_snd_833_ = crate::leanh::lean_ctor_get(v_key_817_, 1);
                v_fst_834_ = crate::leanh::lean_ctor_get(v_a_814_, 0);
                v_snd_835_ = crate::leanh::lean_ctor_get(v_a_814_, 1);
                v___x_836_ = lean_name_eq(v_fst_832_, v_fst_834_);
                if v___x_836_ == 0 {
                    v___y_824_ = v___x_836_;
                    state = 2;
                    continue;
                } else {
                    v_fst_837_ = crate::leanh::lean_ctor_get(v_snd_833_, 0);
                    v_snd_838_ = crate::leanh::lean_ctor_get(v_snd_833_, 1);
                    v_fst_839_ = crate::leanh::lean_ctor_get(v_snd_835_, 0);
                    v_snd_840_ = crate::leanh::lean_ctor_get(v_snd_835_, 1);
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
                        crate::leanh::lean_ctor_set(v___x_821_, 2, v___x_825_);
                        v___x_827_ = v___x_821_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_828_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_828_, 0, v_key_817_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_828_, 1, v_value_818_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_828_, 2, v___x_825_);
                        v___x_827_ = v_reuseFailAlloc_828_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_value_818_);
                    crate::leanh::lean_dec(v_key_817_);
                    if v_isShared_822_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_821_, 1, v_b_815_);
                        crate::leanh::lean_ctor_set(v___x_821_, 0, v_a_814_);
                        v___x_830_ = v___x_821_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_831_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_831_, 0, v_a_814_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_831_, 1, v_b_815_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_831_, 2, v_tail_819_);
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
    mut v_m_844_: *mut crate::leanh::LeanObject,
    mut v_a_845_: *mut crate::leanh::LeanObject,
    mut v_b_846_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_851_: u8 = 0;
    let mut v_fst_852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_856_: u64 = 0;
    let mut v_fst_857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_875_: u8 = 0;
    let mut v___x_876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_885_: u8 = 0;
    let mut v_val_886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_900_: u64 = 0;
    let mut v_hash_901_: u64 = 0;
    let mut v_isSharedCheck_902_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_847_ = crate::leanh::lean_ctor_get(v_m_844_, 0);
                v_buckets_848_ = crate::leanh::lean_ctor_get(v_m_844_, 1);
                v_isSharedCheck_902_ = (!crate::leanh::lean_is_exclusive(v_m_844_)) as u8;
                if v_isSharedCheck_902_ == 0 {
                    v___x_850_ = v_m_844_;
                    v_isShared_851_ = v_isSharedCheck_902_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_848_);
                    crate::leanh::lean_inc(v_size_847_);
                    crate::leanh::lean_dec(v_m_844_);
                    v___x_850_ = crate::leanh::lean_box(0);
                    v_isShared_851_ = v_isSharedCheck_902_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fst_852_ = crate::leanh::lean_ctor_get(v_a_845_, 0);
                v_snd_853_ = crate::leanh::lean_ctor_get(v_a_845_, 1);
                v___x_854_ = lean_array_get_size(v_buckets_848_);
                if crate::leanh::lean_obj_tag(v_fst_852_) == 0 {
                    v___x_900_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0);
                    v___y_856_ = v___x_900_;
                    state = 2;
                    continue;
                } else {
                    v_hash_901_ = crate::leanh::lean_ctor_get_uint64(
                        v_fst_852_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_856_ = v_hash_901_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_fst_857_ = crate::leanh::lean_ctor_get(v_snd_853_, 0);
                v_snd_858_ = crate::leanh::lean_ctor_get(v_snd_853_, 1);
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
                    v___x_876_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_877_ = lean_nat_add(v_size_847_, v___x_876_);
                    crate::leanh::lean_dec(v_size_847_);
                    crate::leanh::lean_inc(v_bkt_874_);
                    v___x_878_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_878_, 0, v_a_845_);
                    crate::leanh::lean_ctor_set(v___x_878_, 1, v_b_846_);
                    crate::leanh::lean_ctor_set(v___x_878_, 2, v_bkt_874_);
                    v_buckets_x27_879_ = lean_array_uset(v_buckets_848_, v___x_873_, v___x_878_);
                    v___x_880_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_881_ = lean_nat_mul(v_size_x27_877_, v___x_880_);
                    v___x_882_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_883_ = lean_nat_div(v___x_881_, v___x_882_);
                    crate::leanh::lean_dec(v___x_881_);
                    v___x_884_ = lean_array_get_size(v_buckets_x27_879_);
                    v___x_885_ = lean_nat_dec_le(v___x_883_, v___x_884_);
                    crate::leanh::lean_dec(v___x_883_);
                    if v___x_885_ == 0 {
                        v_val_886_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__3___redArg(v_buckets_x27_879_);
                        if v_isShared_851_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_850_, 1, v_val_886_);
                            crate::leanh::lean_ctor_set(v___x_850_, 0, v_size_x27_877_);
                            v___x_888_ = v___x_850_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_889_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_889_, 0, v_size_x27_877_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_889_, 1, v_val_886_);
                            v___x_888_ = v_reuseFailAlloc_889_;
                            state = 3;
                            continue;
                        }
                    } else {
                        if v_isShared_851_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_850_, 1, v_buckets_x27_879_);
                            crate::leanh::lean_ctor_set(v___x_850_, 0, v_size_x27_877_);
                            v___x_891_ = v___x_850_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_892_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_892_, 0, v_size_x27_877_);
                            crate::leanh::lean_ctor_set(
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
                    crate::leanh::lean_inc(v_bkt_874_);
                    v___x_893_ = crate::leanh::lean_box(0);
                    v_buckets_x27_894_ = lean_array_uset(v_buckets_848_, v___x_873_, v___x_893_);
                    v___x_895_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__4___redArg(v_a_845_, v_b_846_, v_bkt_874_);
                    v___x_896_ = lean_array_uset(v_buckets_x27_894_, v___x_873_, v___x_895_);
                    if v_isShared_851_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_850_, 1, v___x_896_);
                        v___x_898_ = v___x_850_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_899_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_899_, 0, v_size_847_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_899_, 1, v___x_896_);
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
    mut v_specThm_903_: *mut crate::leanh::LeanObject,
    mut v_m_904_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3s_905_: *mut crate::leanh::LeanObject,
    mut v_ps_906_: *mut crate::leanh::LeanObject,
    mut v_instWP_907_: *mut crate::leanh::LeanObject,
    mut v_excessArgs_908_: *mut crate::leanh::LeanObject,
    mut v_a_909_: *mut crate::leanh::LeanObject,
    mut v_a_910_: *mut crate::leanh::LeanObject,
    mut v_a_911_: *mut crate::leanh::LeanObject,
    mut v_a_912_: *mut crate::leanh::LeanObject,
    mut v_a_913_: *mut crate::leanh::LeanObject,
    mut v_a_914_: *mut crate::leanh::LeanObject,
    mut v_a_915_: *mut crate::leanh::LeanObject,
    mut v_a_916_: *mut crate::leanh::LeanObject,
    mut v_a_917_: *mut crate::leanh::LeanObject,
    mut v_a_918_: *mut crate::leanh::LeanObject,
    mut v_a_919_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_927_: u8 = 0;
    let mut v_specBackwardRuleCache_928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_splitBackwardRuleCache_929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invariants_930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vcs_931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_simpState_932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fuel_933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inlineHandledInvariants_934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_preTacFailed_935_: u8 = 0;
    let mut v___x_937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_938_: u8 = 0;
    let mut v_fst_940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_957_: u8 = 0;
    let mut v_isSharedCheck_958_: u8 = 0;
    let mut v___x_959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_921_ = lean_st_ref_get(v_a_910_);
                v_kind_922_ = crate::leanh::lean_ctor_get(v_specThm_903_, 2);
                crate::leanh::lean_inc_ref(v_kind_922_);
                crate::leanh::lean_inc_ref(v_specThm_903_);
                v___x_923_ =
                    l_Lean_Elab_Tactic_Do_Internal_VCGen_SpecTheoremNew_global_x3f(v_specThm_903_);
                if crate::leanh::lean_obj_tag(v___x_923_) == 1 {
                    v_val_924_ = crate::leanh::lean_ctor_get(v___x_923_, 0);
                    v_isSharedCheck_958_ = (!crate::leanh::lean_is_exclusive(v___x_923_)) as u8;
                    if v_isSharedCheck_958_ == 0 {
                        v___x_926_ = v___x_923_;
                        v_isShared_927_ = v_isSharedCheck_958_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_924_);
                        crate::leanh::lean_dec(v___x_923_);
                        v___x_926_ = crate::leanh::lean_box(0);
                        v_isShared_927_ = v_isSharedCheck_958_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_923_);
                    crate::leanh::lean_dec(v___x_921_);
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
                    crate::leanh::lean_dec_ref(v_kind_922_);
                    return v___x_959_;
                }
            }
            1 => {
                v_specBackwardRuleCache_928_ = crate::leanh::lean_ctor_get(v___x_921_, 0);
                v_splitBackwardRuleCache_929_ = crate::leanh::lean_ctor_get(v___x_921_, 1);
                v_invariants_930_ = crate::leanh::lean_ctor_get(v___x_921_, 2);
                v_vcs_931_ = crate::leanh::lean_ctor_get(v___x_921_, 3);
                v_simpState_932_ = crate::leanh::lean_ctor_get(v___x_921_, 4);
                v_fuel_933_ = crate::leanh::lean_ctor_get(v___x_921_, 5);
                v_inlineHandledInvariants_934_ = crate::leanh::lean_ctor_get(v___x_921_, 6);
                v_preTacFailed_935_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_921_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_isSharedCheck_957_ = (!crate::leanh::lean_is_exclusive(v___x_921_)) as u8;
                if v_isSharedCheck_957_ == 0 {
                    v___x_937_ = v___x_921_;
                    v_isShared_938_ = v_isSharedCheck_957_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_inlineHandledInvariants_934_);
                    crate::leanh::lean_inc(v_fuel_933_);
                    crate::leanh::lean_inc(v_simpState_932_);
                    crate::leanh::lean_inc(v_vcs_931_);
                    crate::leanh::lean_inc(v_invariants_930_);
                    crate::leanh::lean_inc(v_splitBackwardRuleCache_929_);
                    crate::leanh::lean_inc(v_specBackwardRuleCache_928_);
                    crate::leanh::lean_dec(v___x_921_);
                    v___x_937_ = crate::leanh::lean_box(0);
                    v_isShared_938_ = v_isSharedCheck_957_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_949_ = lean_array_get_size(v_excessArgs_908_);
                crate::leanh::lean_inc_ref(v_m_904_);
                v___x_950_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_950_, 0, v_m_904_);
                crate::leanh::lean_ctor_set(v___x_950_, 1, v___x_949_);
                v___x_951_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_951_, 0, v_val_924_);
                crate::leanh::lean_ctor_set(v___x_951_, 1, v___x_950_);
                v___x_952_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(v_specBackwardRuleCache_928_, v___x_951_);
                if crate::leanh::lean_obj_tag(v___x_952_) == 1 {
                    crate::leanh::lean_dec_ref_known(v___x_951_, 2);
                    crate::leanh::lean_dec_ref(v_kind_922_);
                    crate::leanh::lean_dec_ref(v_excessArgs_908_);
                    crate::leanh::lean_dec_ref(v_instWP_907_);
                    crate::leanh::lean_dec_ref(v_ps_906_);
                    crate::leanh::lean_dec_ref(v_00_u03c3s_905_);
                    crate::leanh::lean_dec_ref(v_m_904_);
                    crate::leanh::lean_dec_ref(v_specThm_903_);
                    v_val_953_ = crate::leanh::lean_ctor_get(v___x_952_, 0);
                    crate::leanh::lean_inc(v_val_953_);
                    crate::leanh::lean_dec_ref_known(v___x_952_, 1);
                    v_fst_940_ = v_val_953_;
                    v_snd_941_ = v_specBackwardRuleCache_928_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_952_);
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
                    crate::leanh::lean_dec_ref(v_kind_922_);
                    if crate::leanh::lean_obj_tag(v___x_954_) == 0 {
                        v_a_955_ = crate::leanh::lean_ctor_get(v___x_954_, 0);
                        crate::leanh::lean_inc_n(v_a_955_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_954_, 1);
                        v___x_956_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1___redArg(v_specBackwardRuleCache_928_, v___x_951_, v_a_955_);
                        v_fst_940_ = v_a_955_;
                        v_snd_941_ = v___x_956_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref_known(v___x_951_, 2);
                        crate::leanh::lean_del_object(v___x_937_);
                        crate::leanh::lean_dec_ref(v_inlineHandledInvariants_934_);
                        crate::leanh::lean_dec(v_fuel_933_);
                        crate::leanh::lean_dec_ref(v_simpState_932_);
                        crate::leanh::lean_dec_ref(v_vcs_931_);
                        crate::leanh::lean_dec_ref(v_invariants_930_);
                        crate::leanh::lean_dec_ref(v_splitBackwardRuleCache_929_);
                        crate::leanh::lean_dec_ref(v_specBackwardRuleCache_928_);
                        crate::leanh::lean_del_object(v___x_926_);
                        return v___x_954_;
                    }
                }
            }
            3 => {
                if v_isShared_938_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_937_, 0, v_snd_941_);
                    v___x_943_ = v___x_937_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_948_ = crate::leanh::lean_alloc_ctor(0, 7, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_948_, 0, v_snd_941_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_948_,
                        1,
                        v_splitBackwardRuleCache_929_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_948_, 2, v_invariants_930_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_948_, 3, v_vcs_931_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_948_, 4, v_simpState_932_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_948_, 5, v_fuel_933_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_948_,
                        6,
                        v_inlineHandledInvariants_934_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_948_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
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
                    crate::leanh::lean_ctor_set_tag(v___x_926_, 0);
                    crate::leanh::lean_ctor_set(v___x_926_, 0, v_fst_940_);
                    v___x_946_ = v___x_926_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_947_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_947_, 0, v_fst_940_);
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
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_specThm_960_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_m_961_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_00_u03c3s_962_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_ps_963_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_instWP_964_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_excessArgs_965_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_a_966_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_a_967_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_a_968_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_a_969_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_a_970_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_a_971_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_a_972_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_a_973_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_a_974_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_a_975_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_a_976_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_a_977_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_res_978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_a_976_);
    crate::leanh::lean_dec_ref(v_a_975_);
    crate::leanh::lean_dec(v_a_974_);
    crate::leanh::lean_dec_ref(v_a_973_);
    crate::leanh::lean_dec(v_a_972_);
    crate::leanh::lean_dec_ref(v_a_971_);
    crate::leanh::lean_dec(v_a_970_);
    crate::leanh::lean_dec_ref(v_a_969_);
    crate::leanh::lean_dec(v_a_968_);
    crate::leanh::lean_dec(v_a_967_);
    crate::leanh::lean_dec_ref(v_a_966_);
    return v_res_978_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0(
    mut v_00_u03b2_979_: *mut crate::leanh::LeanObject,
    mut v_m_980_: *mut crate::leanh::LeanObject,
    mut v_a_981_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_982_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(v_m_980_, v_a_981_);
    return v___x_982_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___boxed(
    mut v_00_u03b2_983_: *mut crate::leanh::LeanObject,
    mut v_m_984_: *mut crate::leanh::LeanObject,
    mut v_a_985_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_986_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0(v_00_u03b2_983_, v_m_984_, v_a_985_);
    crate::leanh::lean_dec_ref(v_a_985_);
    crate::leanh::lean_dec_ref(v_m_984_);
    return v_res_986_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1(
    mut v_00_u03b2_987_: *mut crate::leanh::LeanObject,
    mut v_m_988_: *mut crate::leanh::LeanObject,
    mut v_a_989_: *mut crate::leanh::LeanObject,
    mut v_b_990_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_991_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1___redArg(v_m_988_, v_a_989_, v_b_990_);
    return v___x_991_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0(
    mut v_00_u03b2_992_: *mut crate::leanh::LeanObject,
    mut v_a_993_: *mut crate::leanh::LeanObject,
    mut v_x_994_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_995_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg(v_a_993_, v_x_994_);
    return v___x_995_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___boxed(
    mut v_00_u03b2_996_: *mut crate::leanh::LeanObject,
    mut v_a_997_: *mut crate::leanh::LeanObject,
    mut v_x_998_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_999_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0(v_00_u03b2_996_, v_a_997_, v_x_998_);
    crate::leanh::lean_dec(v_x_998_);
    crate::leanh::lean_dec_ref(v_a_997_);
    return v_res_999_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__2(
    mut v_00_u03b2_1000_: *mut crate::leanh::LeanObject,
    mut v_a_1001_: *mut crate::leanh::LeanObject,
    mut v_x_1002_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1003_: u8 = 0;
    v___x_1003_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__2___redArg(v_a_1001_, v_x_1002_);
    return v___x_1003_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__2___boxed(
    mut v_00_u03b2_1004_: *mut crate::leanh::LeanObject,
    mut v_a_1005_: *mut crate::leanh::LeanObject,
    mut v_x_1006_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1007_: u8 = 0;
    let mut v_r_1008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1007_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__2(v_00_u03b2_1004_, v_a_1005_, v_x_1006_);
    crate::leanh::lean_dec(v_x_1006_);
    crate::leanh::lean_dec_ref(v_a_1005_);
    v_r_1008_ = crate::leanh::lean_box((v_res_1007_) as usize);
    return v_r_1008_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__3(
    mut v_00_u03b2_1009_: *mut crate::leanh::LeanObject,
    mut v_data_1010_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1011_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__3___redArg(v_data_1010_);
    return v___x_1011_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__4(
    mut v_00_u03b2_1012_: *mut crate::leanh::LeanObject,
    mut v_a_1013_: *mut crate::leanh::LeanObject,
    mut v_b_1014_: *mut crate::leanh::LeanObject,
    mut v_x_1015_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1016_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__4___redArg(v_a_1013_, v_b_1014_, v_x_1015_);
    return v___x_1016_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__3_spec__4(
    mut v_00_u03b2_1017_: *mut crate::leanh::LeanObject,
    mut v_i_1018_: *mut crate::leanh::LeanObject,
    mut v_source_1019_: *mut crate::leanh::LeanObject,
    mut v_target_1020_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1021_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__3_spec__4___redArg(v_i_1018_, v_source_1019_, v_target_1020_);
    return v___x_1021_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__3_spec__4_spec__5(
    mut v_00_u03b2_1022_: *mut crate::leanh::LeanObject,
    mut v_x_1023_: *mut crate::leanh::LeanObject,
    mut v_x_1024_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1025_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__3_spec__4_spec__5___redArg(v_x_1023_, v_x_1024_);
    return v___x_1025_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg(
    mut v_splitInfo_1032_: *mut crate::leanh::LeanObject,
    mut v_m_1033_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3s_1034_: *mut crate::leanh::LeanObject,
    mut v_ps_1035_: *mut crate::leanh::LeanObject,
    mut v_instWP_1036_: *mut crate::leanh::LeanObject,
    mut v_excessArgs_1037_: *mut crate::leanh::LeanObject,
    mut v_a_1038_: *mut crate::leanh::LeanObject,
    mut v_a_1039_: *mut crate::leanh::LeanObject,
    mut v_a_1040_: *mut crate::leanh::LeanObject,
    mut v_a_1041_: *mut crate::leanh::LeanObject,
    mut v_a_1042_: *mut crate::leanh::LeanObject,
    mut v_a_1043_: *mut crate::leanh::LeanObject,
    mut v_a_1044_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_specBackwardRuleCache_1047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invariants_1048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vcs_1049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_simpState_1050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fuel_1051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inlineHandledInvariants_1052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_preTacFailed_1053_: u8 = 0;
    let mut v_fst_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_specBackwardRuleCache_1062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_splitBackwardRuleCache_1063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invariants_1064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vcs_1065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_simpState_1066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fuel_1067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inlineHandledInvariants_1068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_preTacFailed_1069_: u8 = 0;
    let mut v___x_1070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_matcherApp_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_matcherName_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_splitInfo_1032_) {
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
                    v_matcherApp_1080_ = crate::leanh::lean_ctor_get(v_splitInfo_1032_, 0);
                    v_matcherName_1081_ = crate::leanh::lean_ctor_get(v_matcherApp_1080_, 1);
                    crate::leanh::lean_inc(v_matcherName_1081_);
                    v___y_1060_ = v_matcherName_1081_;
                    state = 2;
                    continue;
                }
            },
            1 => {
                v___x_1056_ = crate::leanh::lean_alloc_ctor(0, 7, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1056_, 0, v_specBackwardRuleCache_1047_);
                crate::leanh::lean_ctor_set(v___x_1056_, 1, v_snd_1055_);
                crate::leanh::lean_ctor_set(v___x_1056_, 2, v_invariants_1048_);
                crate::leanh::lean_ctor_set(v___x_1056_, 3, v_vcs_1049_);
                crate::leanh::lean_ctor_set(v___x_1056_, 4, v_simpState_1050_);
                crate::leanh::lean_ctor_set(v___x_1056_, 5, v_fuel_1051_);
                crate::leanh::lean_ctor_set(v___x_1056_, 6, v_inlineHandledInvariants_1052_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1056_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                    v_preTacFailed_1053_,
                );
                v___x_1057_ = lean_st_ref_set(v_a_1038_, v___x_1056_);
                v___x_1058_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1058_, 0, v_fst_1054_);
                return v___x_1058_;
            }
            2 => {
                v___x_1061_ = lean_st_ref_get(v_a_1038_);
                v_specBackwardRuleCache_1062_ = crate::leanh::lean_ctor_get(v___x_1061_, 0);
                crate::leanh::lean_inc_ref(v_specBackwardRuleCache_1062_);
                v_splitBackwardRuleCache_1063_ = crate::leanh::lean_ctor_get(v___x_1061_, 1);
                crate::leanh::lean_inc_ref(v_splitBackwardRuleCache_1063_);
                v_invariants_1064_ = crate::leanh::lean_ctor_get(v___x_1061_, 2);
                crate::leanh::lean_inc_ref(v_invariants_1064_);
                v_vcs_1065_ = crate::leanh::lean_ctor_get(v___x_1061_, 3);
                crate::leanh::lean_inc_ref(v_vcs_1065_);
                v_simpState_1066_ = crate::leanh::lean_ctor_get(v___x_1061_, 4);
                crate::leanh::lean_inc_ref(v_simpState_1066_);
                v_fuel_1067_ = crate::leanh::lean_ctor_get(v___x_1061_, 5);
                crate::leanh::lean_inc(v_fuel_1067_);
                v_inlineHandledInvariants_1068_ = crate::leanh::lean_ctor_get(v___x_1061_, 6);
                crate::leanh::lean_inc_ref(v_inlineHandledInvariants_1068_);
                v_preTacFailed_1069_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_1061_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                crate::leanh::lean_dec(v___x_1061_);
                v___x_1070_ = lean_array_get_size(v_excessArgs_1037_);
                crate::leanh::lean_inc_ref(v_m_1033_);
                v___x_1071_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1071_, 0, v_m_1033_);
                crate::leanh::lean_ctor_set(v___x_1071_, 1, v___x_1070_);
                v___x_1072_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1072_, 0, v___y_1060_);
                crate::leanh::lean_ctor_set(v___x_1072_, 1, v___x_1071_);
                v___x_1073_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(v_splitBackwardRuleCache_1063_, v___x_1072_);
                if crate::leanh::lean_obj_tag(v___x_1073_) == 1 {
                    crate::leanh::lean_dec_ref_known(v___x_1072_, 2);
                    crate::leanh::lean_dec_ref(v_excessArgs_1037_);
                    crate::leanh::lean_dec_ref(v_instWP_1036_);
                    crate::leanh::lean_dec_ref(v_ps_1035_);
                    crate::leanh::lean_dec_ref(v_00_u03c3s_1034_);
                    crate::leanh::lean_dec_ref(v_m_1033_);
                    crate::leanh::lean_dec_ref(v_splitInfo_1032_);
                    v_val_1074_ = crate::leanh::lean_ctor_get(v___x_1073_, 0);
                    crate::leanh::lean_inc(v_val_1074_);
                    crate::leanh::lean_dec_ref_known(v___x_1073_, 1);
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
                    crate::leanh::lean_dec(v___x_1073_);
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
                    if crate::leanh::lean_obj_tag(v___x_1075_) == 0 {
                        v_a_1076_ = crate::leanh::lean_ctor_get(v___x_1075_, 0);
                        crate::leanh::lean_inc_n(v_a_1076_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_1075_, 1);
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
                        crate::leanh::lean_dec_ref_known(v___x_1072_, 2);
                        crate::leanh::lean_dec_ref(v_inlineHandledInvariants_1068_);
                        crate::leanh::lean_dec(v_fuel_1067_);
                        crate::leanh::lean_dec_ref(v_simpState_1066_);
                        crate::leanh::lean_dec_ref(v_vcs_1065_);
                        crate::leanh::lean_dec_ref(v_invariants_1064_);
                        crate::leanh::lean_dec_ref(v_splitBackwardRuleCache_1063_);
                        crate::leanh::lean_dec_ref(v_specBackwardRuleCache_1062_);
                        return v___x_1075_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg___boxed(
    mut v_splitInfo_1082_: *mut crate::leanh::LeanObject,
    mut v_m_1083_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3s_1084_: *mut crate::leanh::LeanObject,
    mut v_ps_1085_: *mut crate::leanh::LeanObject,
    mut v_instWP_1086_: *mut crate::leanh::LeanObject,
    mut v_excessArgs_1087_: *mut crate::leanh::LeanObject,
    mut v_a_1088_: *mut crate::leanh::LeanObject,
    mut v_a_1089_: *mut crate::leanh::LeanObject,
    mut v_a_1090_: *mut crate::leanh::LeanObject,
    mut v_a_1091_: *mut crate::leanh::LeanObject,
    mut v_a_1092_: *mut crate::leanh::LeanObject,
    mut v_a_1093_: *mut crate::leanh::LeanObject,
    mut v_a_1094_: *mut crate::leanh::LeanObject,
    mut v_a_1095_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_a_1094_);
    crate::leanh::lean_dec_ref(v_a_1093_);
    crate::leanh::lean_dec(v_a_1092_);
    crate::leanh::lean_dec_ref(v_a_1091_);
    crate::leanh::lean_dec(v_a_1090_);
    crate::leanh::lean_dec_ref(v_a_1089_);
    crate::leanh::lean_dec(v_a_1088_);
    return v_res_1096_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached(
    mut v_splitInfo_1097_: *mut crate::leanh::LeanObject,
    mut v_m_1098_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3s_1099_: *mut crate::leanh::LeanObject,
    mut v_ps_1100_: *mut crate::leanh::LeanObject,
    mut v_instWP_1101_: *mut crate::leanh::LeanObject,
    mut v_excessArgs_1102_: *mut crate::leanh::LeanObject,
    mut v_a_1103_: *mut crate::leanh::LeanObject,
    mut v_a_1104_: *mut crate::leanh::LeanObject,
    mut v_a_1105_: *mut crate::leanh::LeanObject,
    mut v_a_1106_: *mut crate::leanh::LeanObject,
    mut v_a_1107_: *mut crate::leanh::LeanObject,
    mut v_a_1108_: *mut crate::leanh::LeanObject,
    mut v_a_1109_: *mut crate::leanh::LeanObject,
    mut v_a_1110_: *mut crate::leanh::LeanObject,
    mut v_a_1111_: *mut crate::leanh::LeanObject,
    mut v_a_1112_: *mut crate::leanh::LeanObject,
    mut v_a_1113_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_splitInfo_1116_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_m_1117_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_00_u03c3s_1118_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_ps_1119_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_instWP_1120_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_excessArgs_1121_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_a_1122_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_a_1123_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_a_1124_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_a_1125_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_a_1126_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_a_1127_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_a_1128_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_a_1129_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_a_1130_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_a_1131_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_a_1132_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_a_1133_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_res_1134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_a_1132_);
    crate::leanh::lean_dec_ref(v_a_1131_);
    crate::leanh::lean_dec(v_a_1130_);
    crate::leanh::lean_dec_ref(v_a_1129_);
    crate::leanh::lean_dec(v_a_1128_);
    crate::leanh::lean_dec_ref(v_a_1127_);
    crate::leanh::lean_dec(v_a_1126_);
    crate::leanh::lean_dec_ref(v_a_1125_);
    crate::leanh::lean_dec(v_a_1124_);
    crate::leanh::lean_dec(v_a_1123_);
    crate::leanh::lean_dec_ref(v_a_1122_);
    return v_res_1134_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Tactic_Do_VCGen_Split(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleConstruction(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache(
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
pub unsafe fn initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Tactic_Do_VCGen_Split(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleConstruction(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache(builtin);
}
