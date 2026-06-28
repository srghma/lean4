// Lean compiler output
// Module: Lean.Elab.Tactic.Do.Internal.VCGen.RuleCache
// Imports: Lean.Elab.Tactic.Do.VCGen.Split Lean.Elab.Tactic.Do.Internal.VCGen.Context Lean.Elab.Tactic.Do.Internal.VCGen.RuleConstruction Lean.Elab.Tactic.Do.Internal.VCGen.Util
use crate::r#gen::Init::Prelude::l_Lean_Name_mkStr1;
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
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_uint64_of_nat, lean_usize_of_nat, lean_usize_sub,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_get_size, lean_name_eq, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_uint64_mix_hash,
    lean_uint64_of_nat,
};
use crate::lean_imports_rs::Init::System::ST::{lean_st_ref_get, lean_st_ref_set};
use crate::lean_imports_rs::Lean::Expr::lean_expr_eqv;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_2,
    lean_apply_4, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_get_uint64, lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_tag,
    lean_uint64_once, lean_unsigned_to_nat,
};
static mut l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0: u64 = 0;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg___closed__0_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [105, 116, 101, 0]};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg___closed__0_value) as *mut LeanObject,18356704233129443855 as *mut LeanObject] };
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg___closed__2_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [100, 105, 116, 101, 0]};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg___closed__2_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg___closed__2_value) as *mut LeanObject,8391571994004792969 as *mut LeanObject] };
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg___closed__3_value) as *mut LeanObject;
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache_0__Lean_Elab_Tactic_Do_Internal_Std_HashMap_getDM___redArg___lam__0(
    mut v_inst_568_: *mut LeanObject,
    mut v_inst_569_: *mut LeanObject,
    mut v_cache_570_: *mut LeanObject,
    mut v_key_571_: *mut LeanObject,
    mut v_toPure_572_: *mut LeanObject,
    mut v_b_573_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_576_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_b_573_);
    v___x_574_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
        v_inst_568_,
        v_inst_569_,
        v_cache_570_,
        v_key_571_,
        v_b_573_,
    );
    v___x_575_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_575_, 0, v_b_573_);
    lean_ctor_set(v___x_575_, 1, v___x_574_);
    v___x_576_ = lean_apply_2(v_toPure_572_, lean_box(0), v___x_575_);
    return v___x_576_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache_0__Lean_Elab_Tactic_Do_Internal_Std_HashMap_getDM___redArg(
    mut v_inst_577_: *mut LeanObject,
    mut v_inst_578_: *mut LeanObject,
    mut v_inst_579_: *mut LeanObject,
    mut v_cache_580_: *mut LeanObject,
    mut v_key_581_: *mut LeanObject,
    mut v_fallback_582_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_587_: u8 = 0;
    let mut v_toPure_588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_597_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_583_ = lean_ctor_get(v_inst_577_, 0);
                v_toBind_584_ = lean_ctor_get(v_inst_577_, 1);
                v_isSharedCheck_597_ = (!lean_is_exclusive(v_inst_577_)) as u8;
                if v_isSharedCheck_597_ == 0 {
                    v___x_586_ = v_inst_577_;
                    v_isShared_587_ = v_isSharedCheck_597_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toBind_584_);
                    lean_inc(v_toApplicative_583_);
                    lean_dec(v_inst_577_);
                    v___x_586_ = lean_box(0);
                    v_isShared_587_ = v_isSharedCheck_597_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_588_ = lean_ctor_get(v_toApplicative_583_, 1);
                lean_inc(v_toPure_588_);
                lean_dec_ref(v_toApplicative_583_);
                lean_inc(v_key_581_);
                lean_inc_ref(v_inst_579_);
                lean_inc_ref(v_inst_578_);
                v___x_589_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(
                    v_inst_578_,
                    v_inst_579_,
                    v_cache_580_,
                    v_key_581_,
                );
                if lean_obj_tag(v___x_589_) == 1 {
                    lean_dec(v_toBind_584_);
                    lean_dec(v_fallback_582_);
                    lean_dec(v_key_581_);
                    lean_dec_ref(v_inst_579_);
                    lean_dec_ref(v_inst_578_);
                    v_val_590_ = lean_ctor_get(v___x_589_, 0);
                    lean_inc(v_val_590_);
                    lean_dec_ref_known(v___x_589_, 1);
                    if v_isShared_587_ == 0 {
                        lean_ctor_set(v___x_586_, 1, v_cache_580_);
                        lean_ctor_set(v___x_586_, 0, v_val_590_);
                        v___x_592_ = v___x_586_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_594_, 0, v_val_590_);
                        lean_ctor_set(v_reuseFailAlloc_594_, 1, v_cache_580_);
                        v___x_592_ = v_reuseFailAlloc_594_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_589_);
                    lean_del_object(v___x_586_);
                    v___f_595_ = lean_alloc_closure(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache_0__Lean_Elab_Tactic_Do_Internal_Std_HashMap_getDM___redArg___lam__0 as *mut core::ffi::c_void, 6, 5);
                    lean_closure_set(v___f_595_, 0, v_inst_578_);
                    lean_closure_set(v___f_595_, 1, v_inst_579_);
                    lean_closure_set(v___f_595_, 2, v_cache_580_);
                    lean_closure_set(v___f_595_, 3, v_key_581_);
                    lean_closure_set(v___f_595_, 4, v_toPure_588_);
                    v___x_596_ = lean_apply_4(
                        v_toBind_584_,
                        lean_box(0),
                        lean_box(0),
                        v_fallback_582_,
                        v___f_595_,
                    );
                    return v___x_596_;
                }
            }
            2 => {
                v___x_593_ = lean_apply_2(v_toPure_588_, lean_box(0), v___x_592_);
                return v___x_593_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache_0__Lean_Elab_Tactic_Do_Internal_Std_HashMap_getDM(
    mut v_m_598_: *mut LeanObject,
    mut v_00_u03b1_599_: *mut LeanObject,
    mut v_00_u03b2_600_: *mut LeanObject,
    mut v_inst_601_: *mut LeanObject,
    mut v_inst_602_: *mut LeanObject,
    mut v_inst_603_: *mut LeanObject,
    mut v_cache_604_: *mut LeanObject,
    mut v_key_605_: *mut LeanObject,
    mut v_fallback_606_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_611_: u8 = 0;
    let mut v_toPure_612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_621_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_607_ = lean_ctor_get(v_inst_601_, 0);
                v_toBind_608_ = lean_ctor_get(v_inst_601_, 1);
                v_isSharedCheck_621_ = (!lean_is_exclusive(v_inst_601_)) as u8;
                if v_isSharedCheck_621_ == 0 {
                    v___x_610_ = v_inst_601_;
                    v_isShared_611_ = v_isSharedCheck_621_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toBind_608_);
                    lean_inc(v_toApplicative_607_);
                    lean_dec(v_inst_601_);
                    v___x_610_ = lean_box(0);
                    v_isShared_611_ = v_isSharedCheck_621_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_612_ = lean_ctor_get(v_toApplicative_607_, 1);
                lean_inc(v_toPure_612_);
                lean_dec_ref(v_toApplicative_607_);
                lean_inc(v_key_605_);
                lean_inc_ref(v_inst_603_);
                lean_inc_ref(v_inst_602_);
                v___x_613_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(
                    v_inst_602_,
                    v_inst_603_,
                    v_cache_604_,
                    v_key_605_,
                );
                if lean_obj_tag(v___x_613_) == 1 {
                    lean_dec(v_toBind_608_);
                    lean_dec(v_fallback_606_);
                    lean_dec(v_key_605_);
                    lean_dec_ref(v_inst_603_);
                    lean_dec_ref(v_inst_602_);
                    v_val_614_ = lean_ctor_get(v___x_613_, 0);
                    lean_inc(v_val_614_);
                    lean_dec_ref_known(v___x_613_, 1);
                    if v_isShared_611_ == 0 {
                        lean_ctor_set(v___x_610_, 1, v_cache_604_);
                        lean_ctor_set(v___x_610_, 0, v_val_614_);
                        v___x_616_ = v___x_610_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_618_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_618_, 0, v_val_614_);
                        lean_ctor_set(v_reuseFailAlloc_618_, 1, v_cache_604_);
                        v___x_616_ = v_reuseFailAlloc_618_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_613_);
                    lean_del_object(v___x_610_);
                    v___f_619_ = lean_alloc_closure(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache_0__Lean_Elab_Tactic_Do_Internal_Std_HashMap_getDM___redArg___lam__0 as *mut core::ffi::c_void, 6, 5);
                    lean_closure_set(v___f_619_, 0, v_inst_602_);
                    lean_closure_set(v___f_619_, 1, v_inst_603_);
                    lean_closure_set(v___f_619_, 2, v_cache_604_);
                    lean_closure_set(v___f_619_, 3, v_key_605_);
                    lean_closure_set(v___f_619_, 4, v_toPure_612_);
                    v___x_620_ = lean_apply_4(
                        v_toBind_608_,
                        lean_box(0),
                        lean_box(0),
                        v_fallback_606_,
                        v___f_619_,
                    );
                    return v___x_620_;
                }
            }
            2 => {
                v___x_617_ = lean_apply_2(v_toPure_612_, lean_box(0), v___x_616_);
                return v___x_617_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_SpecTheoremNew_global_x3f(
    mut v_specThm_622_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_proof_623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_627_: u8 = 0;
    let mut v___x_629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_631_: u8 = 0;
    let mut v___x_632_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_proof_623_ = lean_ctor_get(v_specThm_622_, 1);
                lean_inc_ref(v_proof_623_);
                lean_dec_ref(v_specThm_622_);
                if lean_obj_tag(v_proof_623_) == 0 {
                    v_declName_624_ = lean_ctor_get(v_proof_623_, 0);
                    v_isSharedCheck_631_ = (!lean_is_exclusive(v_proof_623_)) as u8;
                    if v_isSharedCheck_631_ == 0 {
                        v___x_626_ = v_proof_623_;
                        v_isShared_627_ = v_isSharedCheck_631_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_declName_624_);
                        lean_dec(v_proof_623_);
                        v___x_626_ = lean_box(0);
                        v_isShared_627_ = v_isSharedCheck_631_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_proof_623_);
                    v___x_632_ = lean_box(0);
                    return v___x_632_;
                }
            }
            1 => {
                if v_isShared_627_ == 0 {
                    lean_ctor_set_tag(v___x_626_, 1);
                    v___x_629_ = v___x_626_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_630_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_630_, 0, v_declName_624_);
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
    mut v_kind_633_: *mut LeanObject,
    mut v_specThm_634_: *mut LeanObject,
    mut v_m_635_: *mut LeanObject,
    mut v_00_u03c3s_636_: *mut LeanObject,
    mut v_ps_637_: *mut LeanObject,
    mut v_instWP_638_: *mut LeanObject,
    mut v_excessArgs_639_: *mut LeanObject,
    mut v___y_640_: *mut LeanObject,
    mut v___y_641_: *mut LeanObject,
    mut v___y_642_: *mut LeanObject,
    mut v___y_643_: *mut LeanObject,
    mut v___y_644_: *mut LeanObject,
    mut v___y_645_: *mut LeanObject,
    mut v___y_646_: *mut LeanObject,
    mut v___y_647_: *mut LeanObject,
    mut v___y_648_: *mut LeanObject,
    mut v___y_649_: *mut LeanObject,
    mut v___y_650_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_kind_633_) == 0 {
        let mut v___x_652_: *mut LeanObject = core::ptr::null_mut();
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
        let mut v___x_653_: *mut LeanObject = core::ptr::null_mut();
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
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_654_: *mut LeanObject = *_args.add(0);
    let mut v_specThm_655_: *mut LeanObject = *_args.add(1);
    let mut v_m_656_: *mut LeanObject = *_args.add(2);
    let mut v_00_u03c3s_657_: *mut LeanObject = *_args.add(3);
    let mut v_ps_658_: *mut LeanObject = *_args.add(4);
    let mut v_instWP_659_: *mut LeanObject = *_args.add(5);
    let mut v_excessArgs_660_: *mut LeanObject = *_args.add(6);
    let mut v___y_661_: *mut LeanObject = *_args.add(7);
    let mut v___y_662_: *mut LeanObject = *_args.add(8);
    let mut v___y_663_: *mut LeanObject = *_args.add(9);
    let mut v___y_664_: *mut LeanObject = *_args.add(10);
    let mut v___y_665_: *mut LeanObject = *_args.add(11);
    let mut v___y_666_: *mut LeanObject = *_args.add(12);
    let mut v___y_667_: *mut LeanObject = *_args.add(13);
    let mut v___y_668_: *mut LeanObject = *_args.add(14);
    let mut v___y_669_: *mut LeanObject = *_args.add(15);
    let mut v___y_670_: *mut LeanObject = *_args.add(16);
    let mut v___y_671_: *mut LeanObject = *_args.add(17);
    let mut v___y_672_: *mut LeanObject = *_args.add(18);
    let mut v_res_673_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_671_);
    lean_dec_ref(v___y_670_);
    lean_dec(v___y_669_);
    lean_dec_ref(v___y_668_);
    lean_dec(v___y_667_);
    lean_dec_ref(v___y_666_);
    lean_dec(v___y_665_);
    lean_dec_ref(v___y_664_);
    lean_dec(v___y_663_);
    lean_dec(v___y_662_);
    lean_dec_ref(v___y_661_);
    lean_dec_ref(v_kind_654_);
    return v_res_673_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg(
    mut v_a_674_: *mut LeanObject,
    mut v_x_675_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_681_: u8 = 0;
    let mut v___x_683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_688_: u8 = 0;
    let mut v_fst_689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_693_: u8 = 0;
    let mut v___x_694_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_675_) == 0 {
                    v___x_676_ = lean_box(0);
                    return v___x_676_;
                } else {
                    v_key_677_ = lean_ctor_get(v_x_675_, 0);
                    v_value_678_ = lean_ctor_get(v_x_675_, 1);
                    v_tail_679_ = lean_ctor_get(v_x_675_, 2);
                    v_fst_684_ = lean_ctor_get(v_key_677_, 0);
                    v_snd_685_ = lean_ctor_get(v_key_677_, 1);
                    v_fst_686_ = lean_ctor_get(v_a_674_, 0);
                    v_snd_687_ = lean_ctor_get(v_a_674_, 1);
                    v___x_688_ = lean_name_eq(v_fst_684_, v_fst_686_);
                    if v___x_688_ == 0 {
                        v___y_681_ = v___x_688_;
                        state = 1;
                        continue;
                    } else {
                        v_fst_689_ = lean_ctor_get(v_snd_685_, 0);
                        v_snd_690_ = lean_ctor_get(v_snd_685_, 1);
                        v_fst_691_ = lean_ctor_get(v_snd_687_, 0);
                        v_snd_692_ = lean_ctor_get(v_snd_687_, 1);
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
                    lean_inc(v_value_678_);
                    v___x_683_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_683_, 0, v_value_678_);
                    return v___x_683_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg___boxed(
    mut v_a_695_: *mut LeanObject,
    mut v_x_696_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_697_: *mut LeanObject = core::ptr::null_mut();
    v_res_697_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg(v_a_695_, v_x_696_);
    lean_dec(v_x_696_);
    lean_dec_ref(v_a_695_);
    return v_res_697_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0()
-> u64 {
    let mut v___x_698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_699_: u64 = 0;
    v___x_698_ = lean_unsigned_to_nat(1723);
    v___x_699_ = lean_uint64_of_nat(v___x_698_);
    return v___x_699_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(
    mut v_m_700_: *mut LeanObject,
    mut v_a_701_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_707_: u64 = 0;
    let mut v_fst_708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_709_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_727_: u64 = 0;
    let mut v_hash_728_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_702_ = lean_ctor_get(v_m_700_, 1);
                v_fst_703_ = lean_ctor_get(v_a_701_, 0);
                v_snd_704_ = lean_ctor_get(v_a_701_, 1);
                v___x_705_ = lean_array_get_size(v_buckets_702_);
                if lean_obj_tag(v_fst_703_) == 0 {
                    v___x_727_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0);
                    v___y_707_ = v___x_727_;
                    state = 1;
                    continue;
                } else {
                    v_hash_728_ = lean_ctor_get_uint64(
                        v_fst_703_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_707_ = v_hash_728_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fst_708_ = lean_ctor_get(v_snd_704_, 0);
                v_snd_709_ = lean_ctor_get(v_snd_704_, 1);
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
    mut v_m_729_: *mut LeanObject,
    mut v_a_730_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_731_: *mut LeanObject = core::ptr::null_mut();
    v_res_731_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(v_m_729_, v_a_730_);
    lean_dec_ref(v_a_730_);
    lean_dec_ref(v_m_729_);
    return v_res_731_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__3_spec__4_spec__5___redArg(
    mut v_x_732_: *mut LeanObject,
    mut v_x_733_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_739_: u8 = 0;
    let mut v_fst_740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_744_: u64 = 0;
    let mut v_fst_745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_746_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_768_: u64 = 0;
    let mut v_hash_769_: u64 = 0;
    let mut v_isSharedCheck_770_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_733_) == 0 {
                    return v_x_732_;
                } else {
                    v_key_734_ = lean_ctor_get(v_x_733_, 0);
                    v_value_735_ = lean_ctor_get(v_x_733_, 1);
                    v_tail_736_ = lean_ctor_get(v_x_733_, 2);
                    v_isSharedCheck_770_ = (!lean_is_exclusive(v_x_733_)) as u8;
                    if v_isSharedCheck_770_ == 0 {
                        v___x_738_ = v_x_733_;
                        v_isShared_739_ = v_isSharedCheck_770_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_736_);
                        lean_inc(v_value_735_);
                        lean_inc(v_key_734_);
                        lean_dec(v_x_733_);
                        v___x_738_ = lean_box(0);
                        v_isShared_739_ = v_isSharedCheck_770_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_740_ = lean_ctor_get(v_key_734_, 0);
                v_snd_741_ = lean_ctor_get(v_key_734_, 1);
                v___x_742_ = lean_array_get_size(v_x_732_);
                if lean_obj_tag(v_fst_740_) == 0 {
                    v___x_768_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0);
                    v___y_744_ = v___x_768_;
                    state = 2;
                    continue;
                } else {
                    v_hash_769_ = lean_ctor_get_uint64(
                        v_fst_740_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_744_ = v_hash_769_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_fst_745_ = lean_ctor_get(v_snd_741_, 0);
                v_snd_746_ = lean_ctor_get(v_snd_741_, 1);
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
                lean_inc(v___x_762_);
                if v_isShared_739_ == 0 {
                    lean_ctor_set(v___x_738_, 2, v___x_762_);
                    v___x_764_ = v___x_738_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_767_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_767_, 0, v_key_734_);
                    lean_ctor_set(v_reuseFailAlloc_767_, 1, v_value_735_);
                    lean_ctor_set(v_reuseFailAlloc_767_, 2, v___x_762_);
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
    mut v_i_771_: *mut LeanObject,
    mut v_source_772_: *mut LeanObject,
    mut v_target_773_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_775_: u8 = 0;
    let mut v_es_776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_781_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_774_ = lean_array_get_size(v_source_772_);
                v___x_775_ = lean_nat_dec_lt(v_i_771_, v___x_774_);
                if v___x_775_ == 0 {
                    lean_dec_ref(v_source_772_);
                    lean_dec(v_i_771_);
                    return v_target_773_;
                } else {
                    v_es_776_ = lean_array_fget(v_source_772_, v_i_771_);
                    v___x_777_ = lean_box(0);
                    v_source_778_ = lean_array_fset(v_source_772_, v_i_771_, v___x_777_);
                    v_target_779_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__3_spec__4_spec__5___redArg(v_target_773_, v_es_776_);
                    v___x_780_ = lean_unsigned_to_nat(1);
                    v___x_781_ = lean_nat_add(v_i_771_, v___x_780_);
                    lean_dec(v_i_771_);
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
    mut v_data_783_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_790_: *mut LeanObject = core::ptr::null_mut();
    v___x_784_ = lean_array_get_size(v_data_783_);
    v___x_785_ = lean_unsigned_to_nat(2);
    v_nbuckets_786_ = lean_nat_mul(v___x_784_, v___x_785_);
    v___x_787_ = lean_unsigned_to_nat(0);
    v___x_788_ = lean_box(0);
    v___x_789_ = lean_mk_array(v_nbuckets_786_, v___x_788_);
    v___x_790_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__3_spec__4___redArg(v___x_787_, v_data_783_, v___x_789_);
    return v___x_790_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__2___redArg(
    mut v_a_791_: *mut LeanObject,
    mut v_x_792_: *mut LeanObject,
) -> u8 {
    let mut v___x_793_: u8 = 0;
    let mut v_key_794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_797_: u8 = 0;
    let mut v_fst_799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_803_: u8 = 0;
    let mut v_fst_804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_808_: u8 = 0;
    let mut v___x_809_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_792_) == 0 {
                    v___x_793_ = 0;
                    return v___x_793_;
                } else {
                    v_key_794_ = lean_ctor_get(v_x_792_, 0);
                    v_tail_795_ = lean_ctor_get(v_x_792_, 2);
                    v_fst_799_ = lean_ctor_get(v_key_794_, 0);
                    v_snd_800_ = lean_ctor_get(v_key_794_, 1);
                    v_fst_801_ = lean_ctor_get(v_a_791_, 0);
                    v_snd_802_ = lean_ctor_get(v_a_791_, 1);
                    v___x_803_ = lean_name_eq(v_fst_799_, v_fst_801_);
                    if v___x_803_ == 0 {
                        v___y_797_ = v___x_803_;
                        state = 1;
                        continue;
                    } else {
                        v_fst_804_ = lean_ctor_get(v_snd_800_, 0);
                        v_snd_805_ = lean_ctor_get(v_snd_800_, 1);
                        v_fst_806_ = lean_ctor_get(v_snd_802_, 0);
                        v_snd_807_ = lean_ctor_get(v_snd_802_, 1);
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
    mut v_a_810_: *mut LeanObject,
    mut v_x_811_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_812_: u8 = 0;
    let mut v_r_813_: *mut LeanObject = core::ptr::null_mut();
    v_res_812_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__2___redArg(v_a_810_, v_x_811_);
    lean_dec(v_x_811_);
    lean_dec_ref(v_a_810_);
    v_r_813_ = lean_box((v_res_812_) as usize);
    return v_r_813_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__4___redArg(
    mut v_a_814_: *mut LeanObject,
    mut v_b_815_: *mut LeanObject,
    mut v_x_816_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_822_: u8 = 0;
    let mut v___y_824_: u8 = 0;
    let mut v___x_825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_836_: u8 = 0;
    let mut v_fst_837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_841_: u8 = 0;
    let mut v___x_842_: u8 = 0;
    let mut v_isSharedCheck_843_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_816_) == 0 {
                    lean_dec(v_b_815_);
                    lean_dec_ref(v_a_814_);
                    return v_x_816_;
                } else {
                    v_key_817_ = lean_ctor_get(v_x_816_, 0);
                    v_value_818_ = lean_ctor_get(v_x_816_, 1);
                    v_tail_819_ = lean_ctor_get(v_x_816_, 2);
                    v_isSharedCheck_843_ = (!lean_is_exclusive(v_x_816_)) as u8;
                    if v_isSharedCheck_843_ == 0 {
                        v___x_821_ = v_x_816_;
                        v_isShared_822_ = v_isSharedCheck_843_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_819_);
                        lean_inc(v_value_818_);
                        lean_inc(v_key_817_);
                        lean_dec(v_x_816_);
                        v___x_821_ = lean_box(0);
                        v_isShared_822_ = v_isSharedCheck_843_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_832_ = lean_ctor_get(v_key_817_, 0);
                v_snd_833_ = lean_ctor_get(v_key_817_, 1);
                v_fst_834_ = lean_ctor_get(v_a_814_, 0);
                v_snd_835_ = lean_ctor_get(v_a_814_, 1);
                v___x_836_ = lean_name_eq(v_fst_832_, v_fst_834_);
                if v___x_836_ == 0 {
                    v___y_824_ = v___x_836_;
                    state = 2;
                    continue;
                } else {
                    v_fst_837_ = lean_ctor_get(v_snd_833_, 0);
                    v_snd_838_ = lean_ctor_get(v_snd_833_, 1);
                    v_fst_839_ = lean_ctor_get(v_snd_835_, 0);
                    v_snd_840_ = lean_ctor_get(v_snd_835_, 1);
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
                        lean_ctor_set(v___x_821_, 2, v___x_825_);
                        v___x_827_ = v___x_821_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_828_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_828_, 0, v_key_817_);
                        lean_ctor_set(v_reuseFailAlloc_828_, 1, v_value_818_);
                        lean_ctor_set(v_reuseFailAlloc_828_, 2, v___x_825_);
                        v___x_827_ = v_reuseFailAlloc_828_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_value_818_);
                    lean_dec(v_key_817_);
                    if v_isShared_822_ == 0 {
                        lean_ctor_set(v___x_821_, 1, v_b_815_);
                        lean_ctor_set(v___x_821_, 0, v_a_814_);
                        v___x_830_ = v___x_821_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_831_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_831_, 0, v_a_814_);
                        lean_ctor_set(v_reuseFailAlloc_831_, 1, v_b_815_);
                        lean_ctor_set(v_reuseFailAlloc_831_, 2, v_tail_819_);
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
    mut v_m_844_: *mut LeanObject,
    mut v_a_845_: *mut LeanObject,
    mut v_b_846_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_851_: u8 = 0;
    let mut v_fst_852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_856_: u64 = 0;
    let mut v_fst_857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_858_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_875_: u8 = 0;
    let mut v___x_876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_885_: u8 = 0;
    let mut v_val_886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_900_: u64 = 0;
    let mut v_hash_901_: u64 = 0;
    let mut v_isSharedCheck_902_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_847_ = lean_ctor_get(v_m_844_, 0);
                v_buckets_848_ = lean_ctor_get(v_m_844_, 1);
                v_isSharedCheck_902_ = (!lean_is_exclusive(v_m_844_)) as u8;
                if v_isSharedCheck_902_ == 0 {
                    v___x_850_ = v_m_844_;
                    v_isShared_851_ = v_isSharedCheck_902_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_buckets_848_);
                    lean_inc(v_size_847_);
                    lean_dec(v_m_844_);
                    v___x_850_ = lean_box(0);
                    v_isShared_851_ = v_isSharedCheck_902_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fst_852_ = lean_ctor_get(v_a_845_, 0);
                v_snd_853_ = lean_ctor_get(v_a_845_, 1);
                v___x_854_ = lean_array_get_size(v_buckets_848_);
                if lean_obj_tag(v_fst_852_) == 0 {
                    v___x_900_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0);
                    v___y_856_ = v___x_900_;
                    state = 2;
                    continue;
                } else {
                    v_hash_901_ = lean_ctor_get_uint64(
                        v_fst_852_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_856_ = v_hash_901_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_fst_857_ = lean_ctor_get(v_snd_853_, 0);
                v_snd_858_ = lean_ctor_get(v_snd_853_, 1);
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
                    v___x_876_ = lean_unsigned_to_nat(1);
                    v_size_x27_877_ = lean_nat_add(v_size_847_, v___x_876_);
                    lean_dec(v_size_847_);
                    lean_inc(v_bkt_874_);
                    v___x_878_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_878_, 0, v_a_845_);
                    lean_ctor_set(v___x_878_, 1, v_b_846_);
                    lean_ctor_set(v___x_878_, 2, v_bkt_874_);
                    v_buckets_x27_879_ = lean_array_uset(v_buckets_848_, v___x_873_, v___x_878_);
                    v___x_880_ = lean_unsigned_to_nat(4);
                    v___x_881_ = lean_nat_mul(v_size_x27_877_, v___x_880_);
                    v___x_882_ = lean_unsigned_to_nat(3);
                    v___x_883_ = lean_nat_div(v___x_881_, v___x_882_);
                    lean_dec(v___x_881_);
                    v___x_884_ = lean_array_get_size(v_buckets_x27_879_);
                    v___x_885_ = lean_nat_dec_le(v___x_883_, v___x_884_);
                    lean_dec(v___x_883_);
                    if v___x_885_ == 0 {
                        v_val_886_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__3___redArg(v_buckets_x27_879_);
                        if v_isShared_851_ == 0 {
                            lean_ctor_set(v___x_850_, 1, v_val_886_);
                            lean_ctor_set(v___x_850_, 0, v_size_x27_877_);
                            v___x_888_ = v___x_850_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_889_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_889_, 0, v_size_x27_877_);
                            lean_ctor_set(v_reuseFailAlloc_889_, 1, v_val_886_);
                            v___x_888_ = v_reuseFailAlloc_889_;
                            state = 3;
                            continue;
                        }
                    } else {
                        if v_isShared_851_ == 0 {
                            lean_ctor_set(v___x_850_, 1, v_buckets_x27_879_);
                            lean_ctor_set(v___x_850_, 0, v_size_x27_877_);
                            v___x_891_ = v___x_850_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_892_, 0, v_size_x27_877_);
                            lean_ctor_set(v_reuseFailAlloc_892_, 1, v_buckets_x27_879_);
                            v___x_891_ = v_reuseFailAlloc_892_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_inc(v_bkt_874_);
                    v___x_893_ = lean_box(0);
                    v_buckets_x27_894_ = lean_array_uset(v_buckets_848_, v___x_873_, v___x_893_);
                    v___x_895_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__4___redArg(v_a_845_, v_b_846_, v_bkt_874_);
                    v___x_896_ = lean_array_uset(v_buckets_x27_894_, v___x_873_, v___x_895_);
                    if v_isShared_851_ == 0 {
                        lean_ctor_set(v___x_850_, 1, v___x_896_);
                        v___x_898_ = v___x_850_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_899_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_899_, 0, v_size_847_);
                        lean_ctor_set(v_reuseFailAlloc_899_, 1, v___x_896_);
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
    mut v_specThm_903_: *mut LeanObject,
    mut v_m_904_: *mut LeanObject,
    mut v_00_u03c3s_905_: *mut LeanObject,
    mut v_ps_906_: *mut LeanObject,
    mut v_instWP_907_: *mut LeanObject,
    mut v_excessArgs_908_: *mut LeanObject,
    mut v_a_909_: *mut LeanObject,
    mut v_a_910_: *mut LeanObject,
    mut v_a_911_: *mut LeanObject,
    mut v_a_912_: *mut LeanObject,
    mut v_a_913_: *mut LeanObject,
    mut v_a_914_: *mut LeanObject,
    mut v_a_915_: *mut LeanObject,
    mut v_a_916_: *mut LeanObject,
    mut v_a_917_: *mut LeanObject,
    mut v_a_918_: *mut LeanObject,
    mut v_a_919_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_927_: u8 = 0;
    let mut v_specBackwardRuleCache_928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_splitBackwardRuleCache_929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_invariants_930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vcs_931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_simpState_932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fuel_933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inlineHandledInvariants_934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_preTacFailed_935_: u8 = 0;
    let mut v___x_937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_938_: u8 = 0;
    let mut v_fst_940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_957_: u8 = 0;
    let mut v_isSharedCheck_958_: u8 = 0;
    let mut v___x_959_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_921_ = lean_st_ref_get(v_a_910_);
                v_kind_922_ = lean_ctor_get(v_specThm_903_, 2);
                lean_inc_ref(v_kind_922_);
                lean_inc_ref(v_specThm_903_);
                v___x_923_ =
                    l_Lean_Elab_Tactic_Do_Internal_VCGen_SpecTheoremNew_global_x3f(v_specThm_903_);
                if lean_obj_tag(v___x_923_) == 1 {
                    v_val_924_ = lean_ctor_get(v___x_923_, 0);
                    v_isSharedCheck_958_ = (!lean_is_exclusive(v___x_923_)) as u8;
                    if v_isSharedCheck_958_ == 0 {
                        v___x_926_ = v___x_923_;
                        v_isShared_927_ = v_isSharedCheck_958_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_924_);
                        lean_dec(v___x_923_);
                        v___x_926_ = lean_box(0);
                        v_isShared_927_ = v_isSharedCheck_958_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_923_);
                    lean_dec(v___x_921_);
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
                    lean_dec_ref(v_kind_922_);
                    return v___x_959_;
                }
            }
            1 => {
                v_specBackwardRuleCache_928_ = lean_ctor_get(v___x_921_, 0);
                v_splitBackwardRuleCache_929_ = lean_ctor_get(v___x_921_, 1);
                v_invariants_930_ = lean_ctor_get(v___x_921_, 2);
                v_vcs_931_ = lean_ctor_get(v___x_921_, 3);
                v_simpState_932_ = lean_ctor_get(v___x_921_, 4);
                v_fuel_933_ = lean_ctor_get(v___x_921_, 5);
                v_inlineHandledInvariants_934_ = lean_ctor_get(v___x_921_, 6);
                v_preTacFailed_935_ = lean_ctor_get_uint8(
                    v___x_921_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                );
                v_isSharedCheck_957_ = (!lean_is_exclusive(v___x_921_)) as u8;
                if v_isSharedCheck_957_ == 0 {
                    v___x_937_ = v___x_921_;
                    v_isShared_938_ = v_isSharedCheck_957_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_inlineHandledInvariants_934_);
                    lean_inc(v_fuel_933_);
                    lean_inc(v_simpState_932_);
                    lean_inc(v_vcs_931_);
                    lean_inc(v_invariants_930_);
                    lean_inc(v_splitBackwardRuleCache_929_);
                    lean_inc(v_specBackwardRuleCache_928_);
                    lean_dec(v___x_921_);
                    v___x_937_ = lean_box(0);
                    v_isShared_938_ = v_isSharedCheck_957_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_949_ = lean_array_get_size(v_excessArgs_908_);
                lean_inc_ref(v_m_904_);
                v___x_950_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_950_, 0, v_m_904_);
                lean_ctor_set(v___x_950_, 1, v___x_949_);
                v___x_951_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_951_, 0, v_val_924_);
                lean_ctor_set(v___x_951_, 1, v___x_950_);
                v___x_952_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(v_specBackwardRuleCache_928_, v___x_951_);
                if lean_obj_tag(v___x_952_) == 1 {
                    lean_dec_ref_known(v___x_951_, 2);
                    lean_dec_ref(v_kind_922_);
                    lean_dec_ref(v_excessArgs_908_);
                    lean_dec_ref(v_instWP_907_);
                    lean_dec_ref(v_ps_906_);
                    lean_dec_ref(v_00_u03c3s_905_);
                    lean_dec_ref(v_m_904_);
                    lean_dec_ref(v_specThm_903_);
                    v_val_953_ = lean_ctor_get(v___x_952_, 0);
                    lean_inc(v_val_953_);
                    lean_dec_ref_known(v___x_952_, 1);
                    v_fst_940_ = v_val_953_;
                    v_snd_941_ = v_specBackwardRuleCache_928_;
                    state = 3;
                    continue;
                } else {
                    lean_dec(v___x_952_);
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
                    lean_dec_ref(v_kind_922_);
                    if lean_obj_tag(v___x_954_) == 0 {
                        v_a_955_ = lean_ctor_get(v___x_954_, 0);
                        lean_inc_n(v_a_955_, 2);
                        lean_dec_ref_known(v___x_954_, 1);
                        v___x_956_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1___redArg(v_specBackwardRuleCache_928_, v___x_951_, v_a_955_);
                        v_fst_940_ = v_a_955_;
                        v_snd_941_ = v___x_956_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec_ref_known(v___x_951_, 2);
                        lean_del_object(v___x_937_);
                        lean_dec_ref(v_inlineHandledInvariants_934_);
                        lean_dec(v_fuel_933_);
                        lean_dec_ref(v_simpState_932_);
                        lean_dec_ref(v_vcs_931_);
                        lean_dec_ref(v_invariants_930_);
                        lean_dec_ref(v_splitBackwardRuleCache_929_);
                        lean_dec_ref(v_specBackwardRuleCache_928_);
                        lean_del_object(v___x_926_);
                        return v___x_954_;
                    }
                }
            }
            3 => {
                if v_isShared_938_ == 0 {
                    lean_ctor_set(v___x_937_, 0, v_snd_941_);
                    v___x_943_ = v___x_937_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 7, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_948_, 0, v_snd_941_);
                    lean_ctor_set(v_reuseFailAlloc_948_, 1, v_splitBackwardRuleCache_929_);
                    lean_ctor_set(v_reuseFailAlloc_948_, 2, v_invariants_930_);
                    lean_ctor_set(v_reuseFailAlloc_948_, 3, v_vcs_931_);
                    lean_ctor_set(v_reuseFailAlloc_948_, 4, v_simpState_932_);
                    lean_ctor_set(v_reuseFailAlloc_948_, 5, v_fuel_933_);
                    lean_ctor_set(v_reuseFailAlloc_948_, 6, v_inlineHandledInvariants_934_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_948_,
                        (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
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
                    lean_ctor_set_tag(v___x_926_, 0);
                    lean_ctor_set(v___x_926_, 0, v_fst_940_);
                    v___x_946_ = v___x_926_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_947_, 0, v_fst_940_);
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
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_specThm_960_: *mut LeanObject = *_args.add(0);
    let mut v_m_961_: *mut LeanObject = *_args.add(1);
    let mut v_00_u03c3s_962_: *mut LeanObject = *_args.add(2);
    let mut v_ps_963_: *mut LeanObject = *_args.add(3);
    let mut v_instWP_964_: *mut LeanObject = *_args.add(4);
    let mut v_excessArgs_965_: *mut LeanObject = *_args.add(5);
    let mut v_a_966_: *mut LeanObject = *_args.add(6);
    let mut v_a_967_: *mut LeanObject = *_args.add(7);
    let mut v_a_968_: *mut LeanObject = *_args.add(8);
    let mut v_a_969_: *mut LeanObject = *_args.add(9);
    let mut v_a_970_: *mut LeanObject = *_args.add(10);
    let mut v_a_971_: *mut LeanObject = *_args.add(11);
    let mut v_a_972_: *mut LeanObject = *_args.add(12);
    let mut v_a_973_: *mut LeanObject = *_args.add(13);
    let mut v_a_974_: *mut LeanObject = *_args.add(14);
    let mut v_a_975_: *mut LeanObject = *_args.add(15);
    let mut v_a_976_: *mut LeanObject = *_args.add(16);
    let mut v_a_977_: *mut LeanObject = *_args.add(17);
    let mut v_res_978_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_976_);
    lean_dec_ref(v_a_975_);
    lean_dec(v_a_974_);
    lean_dec_ref(v_a_973_);
    lean_dec(v_a_972_);
    lean_dec_ref(v_a_971_);
    lean_dec(v_a_970_);
    lean_dec_ref(v_a_969_);
    lean_dec(v_a_968_);
    lean_dec(v_a_967_);
    lean_dec_ref(v_a_966_);
    return v_res_978_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0(
    mut v_00_u03b2_979_: *mut LeanObject,
    mut v_m_980_: *mut LeanObject,
    mut v_a_981_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_982_: *mut LeanObject = core::ptr::null_mut();
    v___x_982_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(v_m_980_, v_a_981_);
    return v___x_982_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___boxed(
    mut v_00_u03b2_983_: *mut LeanObject,
    mut v_m_984_: *mut LeanObject,
    mut v_a_985_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_986_: *mut LeanObject = core::ptr::null_mut();
    v_res_986_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0(v_00_u03b2_983_, v_m_984_, v_a_985_);
    lean_dec_ref(v_a_985_);
    lean_dec_ref(v_m_984_);
    return v_res_986_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1(
    mut v_00_u03b2_987_: *mut LeanObject,
    mut v_m_988_: *mut LeanObject,
    mut v_a_989_: *mut LeanObject,
    mut v_b_990_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_991_: *mut LeanObject = core::ptr::null_mut();
    v___x_991_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1___redArg(v_m_988_, v_a_989_, v_b_990_);
    return v___x_991_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0(
    mut v_00_u03b2_992_: *mut LeanObject,
    mut v_a_993_: *mut LeanObject,
    mut v_x_994_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_995_: *mut LeanObject = core::ptr::null_mut();
    v___x_995_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg(v_a_993_, v_x_994_);
    return v___x_995_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___boxed(
    mut v_00_u03b2_996_: *mut LeanObject,
    mut v_a_997_: *mut LeanObject,
    mut v_x_998_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_999_: *mut LeanObject = core::ptr::null_mut();
    v_res_999_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0(v_00_u03b2_996_, v_a_997_, v_x_998_);
    lean_dec(v_x_998_);
    lean_dec_ref(v_a_997_);
    return v_res_999_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__2(
    mut v_00_u03b2_1000_: *mut LeanObject,
    mut v_a_1001_: *mut LeanObject,
    mut v_x_1002_: *mut LeanObject,
) -> u8 {
    let mut v___x_1003_: u8 = 0;
    v___x_1003_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__2___redArg(v_a_1001_, v_x_1002_);
    return v___x_1003_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__2___boxed(
    mut v_00_u03b2_1004_: *mut LeanObject,
    mut v_a_1005_: *mut LeanObject,
    mut v_x_1006_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1007_: u8 = 0;
    let mut v_r_1008_: *mut LeanObject = core::ptr::null_mut();
    v_res_1007_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__2(v_00_u03b2_1004_, v_a_1005_, v_x_1006_);
    lean_dec(v_x_1006_);
    lean_dec_ref(v_a_1005_);
    v_r_1008_ = lean_box((v_res_1007_) as usize);
    return v_r_1008_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__3(
    mut v_00_u03b2_1009_: *mut LeanObject,
    mut v_data_1010_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1011_: *mut LeanObject = core::ptr::null_mut();
    v___x_1011_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__3___redArg(v_data_1010_);
    return v___x_1011_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__4(
    mut v_00_u03b2_1012_: *mut LeanObject,
    mut v_a_1013_: *mut LeanObject,
    mut v_b_1014_: *mut LeanObject,
    mut v_x_1015_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1016_: *mut LeanObject = core::ptr::null_mut();
    v___x_1016_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__4___redArg(v_a_1013_, v_b_1014_, v_x_1015_);
    return v___x_1016_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__3_spec__4(
    mut v_00_u03b2_1017_: *mut LeanObject,
    mut v_i_1018_: *mut LeanObject,
    mut v_source_1019_: *mut LeanObject,
    mut v_target_1020_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1021_: *mut LeanObject = core::ptr::null_mut();
    v___x_1021_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__3_spec__4___redArg(v_i_1018_, v_source_1019_, v_target_1020_);
    return v___x_1021_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__3_spec__4_spec__5(
    mut v_00_u03b2_1022_: *mut LeanObject,
    mut v_x_1023_: *mut LeanObject,
    mut v_x_1024_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1025_: *mut LeanObject = core::ptr::null_mut();
    v___x_1025_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1_spec__3_spec__4_spec__5___redArg(v_x_1023_, v_x_1024_);
    return v___x_1025_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg(
    mut v_splitInfo_1032_: *mut LeanObject,
    mut v_m_1033_: *mut LeanObject,
    mut v_00_u03c3s_1034_: *mut LeanObject,
    mut v_ps_1035_: *mut LeanObject,
    mut v_instWP_1036_: *mut LeanObject,
    mut v_excessArgs_1037_: *mut LeanObject,
    mut v_a_1038_: *mut LeanObject,
    mut v_a_1039_: *mut LeanObject,
    mut v_a_1040_: *mut LeanObject,
    mut v_a_1041_: *mut LeanObject,
    mut v_a_1042_: *mut LeanObject,
    mut v_a_1043_: *mut LeanObject,
    mut v_a_1044_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_specBackwardRuleCache_1047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_invariants_1048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vcs_1049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_simpState_1050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fuel_1051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inlineHandledInvariants_1052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_preTacFailed_1053_: u8 = 0;
    let mut v_fst_1054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_specBackwardRuleCache_1062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_splitBackwardRuleCache_1063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_invariants_1064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vcs_1065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_simpState_1066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fuel_1067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inlineHandledInvariants_1068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_preTacFailed_1069_: u8 = 0;
    let mut v___x_1070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_matcherApp_1080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_matcherName_1081_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_splitInfo_1032_) {
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
                    v_matcherApp_1080_ = lean_ctor_get(v_splitInfo_1032_, 0);
                    v_matcherName_1081_ = lean_ctor_get(v_matcherApp_1080_, 1);
                    lean_inc(v_matcherName_1081_);
                    v___y_1060_ = v_matcherName_1081_;
                    state = 2;
                    continue;
                }
            },
            1 => {
                v___x_1056_ = lean_alloc_ctor(0, 7, (1) as u32);
                lean_ctor_set(v___x_1056_, 0, v_specBackwardRuleCache_1047_);
                lean_ctor_set(v___x_1056_, 1, v_snd_1055_);
                lean_ctor_set(v___x_1056_, 2, v_invariants_1048_);
                lean_ctor_set(v___x_1056_, 3, v_vcs_1049_);
                lean_ctor_set(v___x_1056_, 4, v_simpState_1050_);
                lean_ctor_set(v___x_1056_, 5, v_fuel_1051_);
                lean_ctor_set(v___x_1056_, 6, v_inlineHandledInvariants_1052_);
                lean_ctor_set_uint8(
                    v___x_1056_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                    v_preTacFailed_1053_,
                );
                v___x_1057_ = lean_st_ref_set(v_a_1038_, v___x_1056_);
                v___x_1058_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1058_, 0, v_fst_1054_);
                return v___x_1058_;
            }
            2 => {
                v___x_1061_ = lean_st_ref_get(v_a_1038_);
                v_specBackwardRuleCache_1062_ = lean_ctor_get(v___x_1061_, 0);
                lean_inc_ref(v_specBackwardRuleCache_1062_);
                v_splitBackwardRuleCache_1063_ = lean_ctor_get(v___x_1061_, 1);
                lean_inc_ref(v_splitBackwardRuleCache_1063_);
                v_invariants_1064_ = lean_ctor_get(v___x_1061_, 2);
                lean_inc_ref(v_invariants_1064_);
                v_vcs_1065_ = lean_ctor_get(v___x_1061_, 3);
                lean_inc_ref(v_vcs_1065_);
                v_simpState_1066_ = lean_ctor_get(v___x_1061_, 4);
                lean_inc_ref(v_simpState_1066_);
                v_fuel_1067_ = lean_ctor_get(v___x_1061_, 5);
                lean_inc(v_fuel_1067_);
                v_inlineHandledInvariants_1068_ = lean_ctor_get(v___x_1061_, 6);
                lean_inc_ref(v_inlineHandledInvariants_1068_);
                v_preTacFailed_1069_ = lean_ctor_get_uint8(
                    v___x_1061_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                );
                lean_dec(v___x_1061_);
                v___x_1070_ = lean_array_get_size(v_excessArgs_1037_);
                lean_inc_ref(v_m_1033_);
                v___x_1071_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1071_, 0, v_m_1033_);
                lean_ctor_set(v___x_1071_, 1, v___x_1070_);
                v___x_1072_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1072_, 0, v___y_1060_);
                lean_ctor_set(v___x_1072_, 1, v___x_1071_);
                v___x_1073_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(v_splitBackwardRuleCache_1063_, v___x_1072_);
                if lean_obj_tag(v___x_1073_) == 1 {
                    lean_dec_ref_known(v___x_1072_, 2);
                    lean_dec_ref(v_excessArgs_1037_);
                    lean_dec_ref(v_instWP_1036_);
                    lean_dec_ref(v_ps_1035_);
                    lean_dec_ref(v_00_u03c3s_1034_);
                    lean_dec_ref(v_m_1033_);
                    lean_dec_ref(v_splitInfo_1032_);
                    v_val_1074_ = lean_ctor_get(v___x_1073_, 0);
                    lean_inc(v_val_1074_);
                    lean_dec_ref_known(v___x_1073_, 1);
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
                    lean_dec(v___x_1073_);
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
                    if lean_obj_tag(v___x_1075_) == 0 {
                        v_a_1076_ = lean_ctor_get(v___x_1075_, 0);
                        lean_inc_n(v_a_1076_, 2);
                        lean_dec_ref_known(v___x_1075_, 1);
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
                        lean_dec_ref_known(v___x_1072_, 2);
                        lean_dec_ref(v_inlineHandledInvariants_1068_);
                        lean_dec(v_fuel_1067_);
                        lean_dec_ref(v_simpState_1066_);
                        lean_dec_ref(v_vcs_1065_);
                        lean_dec_ref(v_invariants_1064_);
                        lean_dec_ref(v_splitBackwardRuleCache_1063_);
                        lean_dec_ref(v_specBackwardRuleCache_1062_);
                        return v___x_1075_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached___redArg___boxed(
    mut v_splitInfo_1082_: *mut LeanObject,
    mut v_m_1083_: *mut LeanObject,
    mut v_00_u03c3s_1084_: *mut LeanObject,
    mut v_ps_1085_: *mut LeanObject,
    mut v_instWP_1086_: *mut LeanObject,
    mut v_excessArgs_1087_: *mut LeanObject,
    mut v_a_1088_: *mut LeanObject,
    mut v_a_1089_: *mut LeanObject,
    mut v_a_1090_: *mut LeanObject,
    mut v_a_1091_: *mut LeanObject,
    mut v_a_1092_: *mut LeanObject,
    mut v_a_1093_: *mut LeanObject,
    mut v_a_1094_: *mut LeanObject,
    mut v_a_1095_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1096_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_1094_);
    lean_dec_ref(v_a_1093_);
    lean_dec(v_a_1092_);
    lean_dec_ref(v_a_1091_);
    lean_dec(v_a_1090_);
    lean_dec_ref(v_a_1089_);
    lean_dec(v_a_1088_);
    return v_res_1096_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSplitInfoCached(
    mut v_splitInfo_1097_: *mut LeanObject,
    mut v_m_1098_: *mut LeanObject,
    mut v_00_u03c3s_1099_: *mut LeanObject,
    mut v_ps_1100_: *mut LeanObject,
    mut v_instWP_1101_: *mut LeanObject,
    mut v_excessArgs_1102_: *mut LeanObject,
    mut v_a_1103_: *mut LeanObject,
    mut v_a_1104_: *mut LeanObject,
    mut v_a_1105_: *mut LeanObject,
    mut v_a_1106_: *mut LeanObject,
    mut v_a_1107_: *mut LeanObject,
    mut v_a_1108_: *mut LeanObject,
    mut v_a_1109_: *mut LeanObject,
    mut v_a_1110_: *mut LeanObject,
    mut v_a_1111_: *mut LeanObject,
    mut v_a_1112_: *mut LeanObject,
    mut v_a_1113_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1115_: *mut LeanObject = core::ptr::null_mut();
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
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_splitInfo_1116_: *mut LeanObject = *_args.add(0);
    let mut v_m_1117_: *mut LeanObject = *_args.add(1);
    let mut v_00_u03c3s_1118_: *mut LeanObject = *_args.add(2);
    let mut v_ps_1119_: *mut LeanObject = *_args.add(3);
    let mut v_instWP_1120_: *mut LeanObject = *_args.add(4);
    let mut v_excessArgs_1121_: *mut LeanObject = *_args.add(5);
    let mut v_a_1122_: *mut LeanObject = *_args.add(6);
    let mut v_a_1123_: *mut LeanObject = *_args.add(7);
    let mut v_a_1124_: *mut LeanObject = *_args.add(8);
    let mut v_a_1125_: *mut LeanObject = *_args.add(9);
    let mut v_a_1126_: *mut LeanObject = *_args.add(10);
    let mut v_a_1127_: *mut LeanObject = *_args.add(11);
    let mut v_a_1128_: *mut LeanObject = *_args.add(12);
    let mut v_a_1129_: *mut LeanObject = *_args.add(13);
    let mut v_a_1130_: *mut LeanObject = *_args.add(14);
    let mut v_a_1131_: *mut LeanObject = *_args.add(15);
    let mut v_a_1132_: *mut LeanObject = *_args.add(16);
    let mut v_a_1133_: *mut LeanObject = *_args.add(17);
    let mut v_res_1134_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_1132_);
    lean_dec_ref(v_a_1131_);
    lean_dec(v_a_1130_);
    lean_dec_ref(v_a_1129_);
    lean_dec(v_a_1128_);
    lean_dec_ref(v_a_1127_);
    lean_dec(v_a_1126_);
    lean_dec_ref(v_a_1125_);
    lean_dec(v_a_1124_);
    lean_dec(v_a_1123_);
    lean_dec_ref(v_a_1122_);
    return v_res_1134_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Tactic_Do_VCGen_Split(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleConstruction(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache(
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
pub unsafe fn initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Tactic_Do_VCGen_Split(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleConstruction(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache(builtin);
}
