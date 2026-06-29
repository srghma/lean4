// Lean compiler output
// Module: Lean.Meta.Match.SimpH
// Imports: Lean.Meta.Basic Lean.Meta.Tactic.Contradiction
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Data::Array::Basic::l_Array_reverse___redArg;
use crate::r#gen::Init::Data::List::Basic::{
    l_List_appendTR___redArg, l_List_isEmpty___redArg, l_List_reverse___redArg,
};
use crate::r#gen::Init::Prelude::{
    l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_instInhabitedOfMonad___redArg,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_instMonadCoreM___lam__0___boxed, l_Lean_Core_instMonadCoreM___lam__1___boxed,
    l_Lean_Exception_isRuntime,
};
use crate::r#gen::Lean::Exception::l_Lean_Exception_isInterrupt;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_fvarId_x21, l_Lean_Expr_hasFVar, l_Lean_Expr_hasMVar, l_Lean_Expr_isFVar,
    l_Lean_Expr_mvarId_x21, l_Lean_instBEqFVarId_beq, l_Lean_instBEqMVarId_beq, l_Lean_mkFVar,
};
use crate::r#gen::Lean::LocalContext::l_Lean_LocalContext_getFVarIds;
use crate::r#gen::Lean::Meta::Basic::{
    initialize_Lean_Meta_Basic,
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp, l_Lean_Meta_Context_config,
    l_Lean_Meta_Context_configKey, l_Lean_Meta_SavedState_restore___redArg,
    l_Lean_Meta_TransparencyMode_toUInt64, l_Lean_Meta_instMonadMetaM___lam__0___boxed,
    l_Lean_Meta_instMonadMetaM___lam__1___boxed, l_Lean_Meta_isExprDefEq,
    l_Lean_Meta_saveState___redArg, runtime_initialize_Lean_Meta_Basic,
};
use crate::r#gen::Lean::Meta::MatchUtil::{l_Lean_Meta_matchEq_x3f, l_Lean_Meta_matchHEq_x3f};
use crate::r#gen::Lean::Meta::Tactic::Clear::{l_Lean_MVarId_clear, l_Lean_MVarId_tryClearMany};
use crate::r#gen::Lean::Meta::Tactic::Contradiction::{
    initialize_Lean_Meta_Tactic_Contradiction, l_Lean_MVarId_contradictionCore,
    runtime_initialize_Lean_Meta_Tactic_Contradiction,
};
use crate::r#gen::Lean::Meta::Tactic::FVarSubst::l_Lean_Meta_FVarSubst_apply;
use crate::r#gen::Lean::Meta::Tactic::Injection::{l_Lean_Meta_injection, l_Lean_Meta_injections};
use crate::r#gen::Lean::Meta::Tactic::Intro::l_Lean_Meta_introNCore;
use crate::r#gen::Lean::Meta::Tactic::Revert::l_Lean_MVarId_revert;
use crate::r#gen::Lean::Meta::Tactic::Subst::{
    l_Lean_Meta_heqToEq, l_Lean_Meta_substCore, l_Lean_Meta_substVars,
};
use crate::r#gen::Lean::Meta::Tactic::Util::{
    l_Lean_MVarId_getType, l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar,
};
use crate::r#gen::Lean::MetavarContext::l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit;
use crate::lean_imports_rs::Init::Data::Array::Basic::{lean_array_uget_borrowed, lean_mk_array};
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_lor, lean_uint64_shift_left, lean_uint64_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_of_nat, lean_usize_sub,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_array_mk, lean_array_push, lean_array_to_list,
    lean_mk_empty_array_with_capacity, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub,
    lean_panic_fn_borrowed, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Meta::Basic::lean_infer_type;
pub static l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_applySubst___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_applySubst___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_applySubst___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__2_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__3_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__4_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__1___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___closed__0_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 77, 97, 116, 99, 104, 46, 83, 105, 109, 112,
        72, 0,
    ],
};
static mut l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___closed__1_value:
    crate::leanh::LeanStringObject<64> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 64,
    m_capacity: 64,
    m_length: 63,
    m_data: [
        95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 77,
        97, 116, 99, 104, 46, 83, 105, 109, 112, 72, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101,
        116, 97, 46, 77, 97, 116, 99, 104, 46, 83, 105, 109, 112, 72, 46, 115, 117, 98, 115, 116,
        82, 72, 83, 0,
    ],
};
static mut l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___closed__2_value:
    crate::leanh::LeanStringObject<108> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 108,
    m_capacity: 108,
    m_length: 107,
    m_data: [
        97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110,
        58, 32, 40, 32, 95, 95, 100, 111, 95, 108, 105, 102, 116, 46, 95, 64, 46, 76, 101, 97, 110,
        46, 77, 101, 116, 97, 46, 77, 97, 116, 99, 104, 46, 83, 105, 109, 112, 72, 46, 50, 51, 52,
        53, 54, 55, 54, 50, 51, 53, 46, 95, 104, 121, 103, 67, 116, 120, 46, 95, 104, 121, 103, 46,
        49, 48, 46, 48, 32, 41, 46, 120, 115, 46, 99, 111, 110, 116, 97, 105, 110, 115, 32, 114,
        104, 115, 10, 32, 32, 0,
    ],
};
static mut l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___closed__2_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_contradiction___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 8) as u16, other: 1, tag: 0 }, m_objs: [((( 16 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,1 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_contradiction___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_contradiction___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___lam__0___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Match_simpH___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Match_simpH___closed__0: u64 = 0;
pub unsafe fn l_List_filterMapTR_go___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_applySubst_spec__0(
    mut v_s_1397_: *mut crate::leanh::LeanObject,
    mut v_a_1398_: *mut crate::leanh::LeanObject,
    mut v_a_1399_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_1398_) == 0 {
                    crate::leanh::lean_dec(v_s_1397_);
                    v___x_1400_ = lean_array_to_list(v_a_1399_);
                    return v___x_1400_;
                } else {
                    v_head_1401_ = crate::leanh::lean_ctor_get(v_a_1398_, 0);
                    crate::leanh::lean_inc(v_head_1401_);
                    v_tail_1402_ = crate::leanh::lean_ctor_get(v_a_1398_, 1);
                    crate::leanh::lean_inc(v_tail_1402_);
                    crate::leanh::lean_dec_ref_known(v_a_1398_, 2);
                    v___x_1403_ = l_Lean_mkFVar(v_head_1401_);
                    crate::leanh::lean_inc(v_s_1397_);
                    v___x_1404_ = l_Lean_Meta_FVarSubst_apply(v_s_1397_, v___x_1403_);
                    crate::leanh::lean_dec_ref(v___x_1403_);
                    if crate::leanh::lean_obj_tag(v___x_1404_) == 1 {
                        v_fvarId_1405_ = crate::leanh::lean_ctor_get(v___x_1404_, 0);
                        crate::leanh::lean_inc(v_fvarId_1405_);
                        crate::leanh::lean_dec_ref_known(v___x_1404_, 1);
                        v___x_1406_ = lean_array_push(v_a_1399_, v_fvarId_1405_);
                        v_a_1398_ = v_tail_1402_;
                        v_a_1399_ = v___x_1406_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v___x_1404_);
                        v_a_1398_ = v_tail_1402_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_applySubst(
    mut v_s_1411_: *mut crate::leanh::LeanObject,
    mut v_fvarIds_1412_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1413_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_applySubst___closed__0;
    v___x_1414_ = l_List_filterMapTR_go___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_applySubst_spec__0(v_s_1411_, v_fvarIds_1412_, v___x_1413_);
    return v___x_1414_;
}
pub unsafe fn _init_l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1415_ = l_instMonadEIO(crate::leanh::lean_box(0));
    return v___x_1415_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1(
    mut v_msg_1420_: *mut crate::leanh::LeanObject,
    mut v___y_1421_: *mut crate::leanh::LeanObject,
    mut v___y_1422_: *mut crate::leanh::LeanObject,
    mut v___y_1423_: *mut crate::leanh::LeanObject,
    mut v___y_1424_: *mut crate::leanh::LeanObject,
    mut v___y_1425_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1432_: u8 = 0;
    let mut v_toFunctor_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1439_: u8 = 0;
    let mut v___f_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1456_: u8 = 0;
    let mut v_toFunctor_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1463_: u8 = 0;
    let mut v___f_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1653__overap_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1483_: u8 = 0;
    let mut v_unused_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1485_: u8 = 0;
    let mut v_unused_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1489_: u8 = 0;
    let mut v_unused_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1491_: u8 = 0;
    let mut v_unused_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1427_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__0_once), _init_l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__0);
                v___x_1428_ = l_StateRefT_x27_instMonad___redArg(v___x_1427_);
                v_toApplicative_1429_ = crate::leanh::lean_ctor_get(v___x_1428_, 0);
                v_isSharedCheck_1491_ = (!crate::leanh::lean_is_exclusive(v___x_1428_)) as u8;
                if v_isSharedCheck_1491_ == 0 {
                    v_unused_1492_ = crate::leanh::lean_ctor_get(v___x_1428_, 1);
                    crate::leanh::lean_dec(v_unused_1492_);
                    v___x_1431_ = v___x_1428_;
                    v_isShared_1432_ = v_isSharedCheck_1491_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_1429_);
                    crate::leanh::lean_dec(v___x_1428_);
                    v___x_1431_ = crate::leanh::lean_box(0);
                    v_isShared_1432_ = v_isSharedCheck_1491_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_1433_ = crate::leanh::lean_ctor_get(v_toApplicative_1429_, 0);
                v_toSeq_1434_ = crate::leanh::lean_ctor_get(v_toApplicative_1429_, 2);
                v_toSeqLeft_1435_ = crate::leanh::lean_ctor_get(v_toApplicative_1429_, 3);
                v_toSeqRight_1436_ = crate::leanh::lean_ctor_get(v_toApplicative_1429_, 4);
                v_isSharedCheck_1489_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_1429_)) as u8;
                if v_isSharedCheck_1489_ == 0 {
                    v_unused_1490_ = crate::leanh::lean_ctor_get(v_toApplicative_1429_, 1);
                    crate::leanh::lean_dec(v_unused_1490_);
                    v___x_1438_ = v_toApplicative_1429_;
                    v_isShared_1439_ = v_isSharedCheck_1489_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_1436_);
                    crate::leanh::lean_inc(v_toSeqLeft_1435_);
                    crate::leanh::lean_inc(v_toSeq_1434_);
                    crate::leanh::lean_inc(v_toFunctor_1433_);
                    crate::leanh::lean_dec(v_toApplicative_1429_);
                    v___x_1438_ = crate::leanh::lean_box(0);
                    v_isShared_1439_ = v_isSharedCheck_1489_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_1440_ = l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__1;
                v___f_1441_ = l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__2;
                crate::leanh::lean_inc_ref(v_toFunctor_1433_);
                v___f_1442_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1442_, 0, v_toFunctor_1433_);
                v___f_1443_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1443_, 0, v_toFunctor_1433_);
                v___x_1444_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1444_, 0, v___f_1442_);
                crate::leanh::lean_ctor_set(v___x_1444_, 1, v___f_1443_);
                v___f_1445_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1445_, 0, v_toSeqRight_1436_);
                v___f_1446_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1446_, 0, v_toSeqLeft_1435_);
                v___f_1447_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1447_, 0, v_toSeq_1434_);
                if v_isShared_1439_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1438_, 4, v___f_1445_);
                    crate::leanh::lean_ctor_set(v___x_1438_, 3, v___f_1446_);
                    crate::leanh::lean_ctor_set(v___x_1438_, 2, v___f_1447_);
                    crate::leanh::lean_ctor_set(v___x_1438_, 1, v___f_1440_);
                    crate::leanh::lean_ctor_set(v___x_1438_, 0, v___x_1444_);
                    v___x_1449_ = v___x_1438_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1488_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1488_, 0, v___x_1444_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1488_, 1, v___f_1440_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1488_, 2, v___f_1447_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1488_, 3, v___f_1446_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1488_, 4, v___f_1445_);
                    v___x_1449_ = v_reuseFailAlloc_1488_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1432_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1431_, 1, v___f_1441_);
                    crate::leanh::lean_ctor_set(v___x_1431_, 0, v___x_1449_);
                    v___x_1451_ = v___x_1431_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1487_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1487_, 0, v___x_1449_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1487_, 1, v___f_1441_);
                    v___x_1451_ = v_reuseFailAlloc_1487_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1452_ = l_StateRefT_x27_instMonad___redArg(v___x_1451_);
                v_toApplicative_1453_ = crate::leanh::lean_ctor_get(v___x_1452_, 0);
                v_isSharedCheck_1485_ = (!crate::leanh::lean_is_exclusive(v___x_1452_)) as u8;
                if v_isSharedCheck_1485_ == 0 {
                    v_unused_1486_ = crate::leanh::lean_ctor_get(v___x_1452_, 1);
                    crate::leanh::lean_dec(v_unused_1486_);
                    v___x_1455_ = v___x_1452_;
                    v_isShared_1456_ = v_isSharedCheck_1485_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_1453_);
                    crate::leanh::lean_dec(v___x_1452_);
                    v___x_1455_ = crate::leanh::lean_box(0);
                    v_isShared_1456_ = v_isSharedCheck_1485_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_1457_ = crate::leanh::lean_ctor_get(v_toApplicative_1453_, 0);
                v_toSeq_1458_ = crate::leanh::lean_ctor_get(v_toApplicative_1453_, 2);
                v_toSeqLeft_1459_ = crate::leanh::lean_ctor_get(v_toApplicative_1453_, 3);
                v_toSeqRight_1460_ = crate::leanh::lean_ctor_get(v_toApplicative_1453_, 4);
                v_isSharedCheck_1483_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_1453_)) as u8;
                if v_isSharedCheck_1483_ == 0 {
                    v_unused_1484_ = crate::leanh::lean_ctor_get(v_toApplicative_1453_, 1);
                    crate::leanh::lean_dec(v_unused_1484_);
                    v___x_1462_ = v_toApplicative_1453_;
                    v_isShared_1463_ = v_isSharedCheck_1483_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_1460_);
                    crate::leanh::lean_inc(v_toSeqLeft_1459_);
                    crate::leanh::lean_inc(v_toSeq_1458_);
                    crate::leanh::lean_inc(v_toFunctor_1457_);
                    crate::leanh::lean_dec(v_toApplicative_1453_);
                    v___x_1462_ = crate::leanh::lean_box(0);
                    v_isShared_1463_ = v_isSharedCheck_1483_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_1464_ = l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__3;
                v___f_1465_ = l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___closed__4;
                crate::leanh::lean_inc_ref(v_toFunctor_1457_);
                v___f_1466_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1466_, 0, v_toFunctor_1457_);
                v___f_1467_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1467_, 0, v_toFunctor_1457_);
                v___x_1468_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1468_, 0, v___f_1466_);
                crate::leanh::lean_ctor_set(v___x_1468_, 1, v___f_1467_);
                v___f_1469_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1469_, 0, v_toSeqRight_1460_);
                v___f_1470_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1470_, 0, v_toSeqLeft_1459_);
                v___f_1471_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1471_, 0, v_toSeq_1458_);
                if v_isShared_1463_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1462_, 4, v___f_1469_);
                    crate::leanh::lean_ctor_set(v___x_1462_, 3, v___f_1470_);
                    crate::leanh::lean_ctor_set(v___x_1462_, 2, v___f_1471_);
                    crate::leanh::lean_ctor_set(v___x_1462_, 1, v___f_1464_);
                    crate::leanh::lean_ctor_set(v___x_1462_, 0, v___x_1468_);
                    v___x_1473_ = v___x_1462_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1482_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1482_, 0, v___x_1468_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1482_, 1, v___f_1464_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1482_, 2, v___f_1471_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1482_, 3, v___f_1470_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1482_, 4, v___f_1469_);
                    v___x_1473_ = v_reuseFailAlloc_1482_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_1456_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1455_, 1, v___f_1465_);
                    crate::leanh::lean_ctor_set(v___x_1455_, 0, v___x_1473_);
                    v___x_1475_ = v___x_1455_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1481_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1481_, 0, v___x_1473_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1481_, 1, v___f_1465_);
                    v___x_1475_ = v_reuseFailAlloc_1481_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_1476_ = l_StateRefT_x27_instMonad___redArg(v___x_1475_);
                v___x_1477_ = crate::leanh::lean_box(0);
                v___x_1478_ = l_instInhabitedOfMonad___redArg(v___x_1476_, v___x_1477_);
                v___x_1653__overap_1479_ = lean_panic_fn_borrowed(v___x_1478_, v_msg_1420_);
                crate::leanh::lean_dec(v___x_1478_);
                crate::leanh::lean_inc(v___y_1425_);
                crate::leanh::lean_inc_ref(v___y_1424_);
                crate::leanh::lean_inc(v___y_1423_);
                crate::leanh::lean_inc_ref(v___y_1422_);
                crate::leanh::lean_inc(v___y_1421_);
                v___x_1480_ = crate::leanh::lean_apply_6(
                    v___x_1653__overap_1479_,
                    v___y_1421_,
                    v___y_1422_,
                    v___y_1423_,
                    v___y_1424_,
                    v___y_1425_,
                    crate::leanh::lean_box(0),
                );
                return v___x_1480_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1___boxed(
    mut v_msg_1493_: *mut crate::leanh::LeanObject,
    mut v___y_1494_: *mut crate::leanh::LeanObject,
    mut v___y_1495_: *mut crate::leanh::LeanObject,
    mut v___y_1496_: *mut crate::leanh::LeanObject,
    mut v___y_1497_: *mut crate::leanh::LeanObject,
    mut v___y_1498_: *mut crate::leanh::LeanObject,
    mut v___y_1499_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1500_ =
        l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1(
            v_msg_1493_,
            v___y_1494_,
            v___y_1495_,
            v___y_1496_,
            v___y_1497_,
            v___y_1498_,
        );
    crate::leanh::lean_dec(v___y_1498_);
    crate::leanh::lean_dec_ref(v___y_1497_);
    crate::leanh::lean_dec(v___y_1496_);
    crate::leanh::lean_dec_ref(v___y_1495_);
    crate::leanh::lean_dec(v___y_1494_);
    return v_res_1500_;
}
pub unsafe fn l_List_elem___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__0(
    mut v_a_1501_: *mut crate::leanh::LeanObject,
    mut v_x_1502_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1503_: u8 = 0;
    let mut v_head_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1502_) == 0 {
                    v___x_1503_ = 0;
                    return v___x_1503_;
                } else {
                    v_head_1504_ = crate::leanh::lean_ctor_get(v_x_1502_, 0);
                    v_tail_1505_ = crate::leanh::lean_ctor_get(v_x_1502_, 1);
                    v___x_1506_ = l_Lean_instBEqFVarId_beq(v_a_1501_, v_head_1504_);
                    if v___x_1506_ == 0 {
                        v_x_1502_ = v_tail_1505_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1506_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_elem___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__0___boxed(
    mut v_a_1508_: *mut crate::leanh::LeanObject,
    mut v_x_1509_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1510_: u8 = 0;
    let mut v_r_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1510_ = l_List_elem___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__0(v_a_1508_, v_x_1509_);
    crate::leanh::lean_dec(v_x_1509_);
    crate::leanh::lean_dec(v_a_1508_);
    v_r_1511_ = crate::leanh::lean_box((v_res_1510_) as usize);
    return v_r_1511_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_eraseTR_go___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__2_spec__2(
    mut v_as_1512_: *mut crate::leanh::LeanObject,
    mut v_i_1513_: usize,
    mut v_stop_1514_: usize,
    mut v_b_1515_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1516_: u8 = 0;
    let mut v___x_1517_: usize = 0;
    let mut v___x_1518_: usize = 0;
    let mut v___x_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1516_ = lean_usize_dec_eq(v_i_1513_, v_stop_1514_);
                if v___x_1516_ == 0 {
                    v___x_1517_ = 1usize;
                    v___x_1518_ = lean_usize_sub(v_i_1513_, v___x_1517_);
                    v___x_1519_ = lean_array_uget_borrowed(v_as_1512_, v___x_1518_);
                    crate::leanh::lean_inc(v___x_1519_);
                    v___x_1520_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1520_, 0, v___x_1519_);
                    crate::leanh::lean_ctor_set(v___x_1520_, 1, v_b_1515_);
                    v_i_1513_ = v___x_1518_;
                    v_b_1515_ = v___x_1520_;
                    state = 0;
                    continue;
                } else {
                    return v_b_1515_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_eraseTR_go___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__2_spec__2___boxed(
    mut v_as_1522_: *mut crate::leanh::LeanObject,
    mut v_i_1523_: *mut crate::leanh::LeanObject,
    mut v_stop_1524_: *mut crate::leanh::LeanObject,
    mut v_b_1525_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1526_: usize = 0;
    let mut v_stop_boxed_1527_: usize = 0;
    let mut v_res_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1526_ = crate::leanh::lean_unbox_usize(v_i_1523_);
    crate::leanh::lean_dec(v_i_1523_);
    v_stop_boxed_1527_ = crate::leanh::lean_unbox_usize(v_stop_1524_);
    crate::leanh::lean_dec(v_stop_1524_);
    v_res_1528_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_eraseTR_go___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__2_spec__2(v_as_1522_, v_i_boxed_1526_, v_stop_boxed_1527_, v_b_1525_);
    crate::leanh::lean_dec_ref(v_as_1522_);
    return v_res_1528_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_eraseTR_go___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__2(
    mut v_l_1529_: *mut crate::leanh::LeanObject,
    mut v_a_1530_: *mut crate::leanh::LeanObject,
    mut v_a_1531_: *mut crate::leanh::LeanObject,
    mut v_a_1532_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: u8 = 0;
    let mut v___x_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: u8 = 0;
    let mut v___x_1541_: usize = 0;
    let mut v___x_1542_: usize = 0;
    let mut v___x_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_1531_) == 0 {
                    crate::leanh::lean_dec_ref(v_a_1532_);
                    crate::leanh::lean_inc(v_l_1529_);
                    return v_l_1529_;
                } else {
                    v_head_1533_ = crate::leanh::lean_ctor_get(v_a_1531_, 0);
                    crate::leanh::lean_inc(v_head_1533_);
                    v_tail_1534_ = crate::leanh::lean_ctor_get(v_a_1531_, 1);
                    crate::leanh::lean_inc(v_tail_1534_);
                    crate::leanh::lean_dec_ref_known(v_a_1531_, 2);
                    v___x_1535_ = l_Lean_instBEqFVarId_beq(v_head_1533_, v_a_1530_);
                    if v___x_1535_ == 0 {
                        v___x_1536_ = lean_array_push(v_a_1532_, v_head_1533_);
                        v_a_1531_ = v_tail_1534_;
                        v_a_1532_ = v___x_1536_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_head_1533_);
                        v___x_1538_ = lean_array_get_size(v_a_1532_);
                        v___x_1539_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_1540_ = lean_nat_dec_lt(v___x_1539_, v___x_1538_);
                        if v___x_1540_ == 0 {
                            crate::leanh::lean_dec_ref(v_a_1532_);
                            return v_tail_1534_;
                        } else {
                            v___x_1541_ = lean_usize_of_nat(v___x_1538_);
                            v___x_1542_ = 0usize;
                            v___x_1543_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_eraseTR_go___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__2_spec__2(v_a_1532_, v___x_1541_, v___x_1542_, v_tail_1534_);
                            crate::leanh::lean_dec_ref(v_a_1532_);
                            return v___x_1543_;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_eraseTR_go___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__2___boxed(
    mut v_l_1544_: *mut crate::leanh::LeanObject,
    mut v_a_1545_: *mut crate::leanh::LeanObject,
    mut v_a_1546_: *mut crate::leanh::LeanObject,
    mut v_a_1547_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1548_ = l___private_Init_Data_List_Impl_0__List_eraseTR_go___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__2(v_l_1544_, v_a_1545_, v_a_1546_, v_a_1547_);
    crate::leanh::lean_dec(v_a_1545_);
    crate::leanh::lean_dec(v_l_1544_);
    return v_res_1548_;
}
pub unsafe fn _init_l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1552_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___closed__2;
    v___x_1553_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_1554_ = crate::leanh::lean_unsigned_to_nat(46);
    v___x_1555_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___closed__1;
    v___x_1556_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___closed__0;
    v___x_1557_ = l_mkPanicMessageWithDecl(
        v___x_1556_,
        v___x_1555_,
        v___x_1554_,
        v___x_1553_,
        v___x_1552_,
    );
    return v___x_1557_;
}
pub unsafe fn l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS(
    mut v_eq_1558_: *mut crate::leanh::LeanObject,
    mut v_rhs_1559_: *mut crate::leanh::LeanObject,
    mut v_a_1560_: *mut crate::leanh::LeanObject,
    mut v_a_1561_: *mut crate::leanh::LeanObject,
    mut v_a_1562_: *mut crate::leanh::LeanObject,
    mut v_a_1563_: *mut crate::leanh::LeanObject,
    mut v_a_1564_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: u8 = 0;
    let mut v___x_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: u8 = 0;
    let mut v___x_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1579_: u8 = 0;
    let mut v_fst_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eqs_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eqsNew_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1588_: u8 = 0;
    let mut v___x_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1602_: u8 = 0;
    let mut v_unused_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1604_: u8 = 0;
    let mut v_a_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1608_: u8 = 0;
    let mut v___x_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1612_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1566_ = lean_st_ref_get(v_a_1560_);
                v_xs_1567_ = crate::leanh::lean_ctor_get(v___x_1566_, 1);
                crate::leanh::lean_inc(v_xs_1567_);
                crate::leanh::lean_dec(v___x_1566_);
                v___x_1568_ = l_List_elem___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__0(v_rhs_1559_, v_xs_1567_);
                crate::leanh::lean_dec(v_xs_1567_);
                if v___x_1568_ == 0 {
                    crate::leanh::lean_dec(v_eq_1558_);
                    v___x_1569_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___closed__3_once), _init_l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___closed__3);
                    v___x_1570_ = l_panic___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__1(v___x_1569_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_);
                    return v___x_1570_;
                } else {
                    v___x_1571_ = lean_st_ref_get(v_a_1560_);
                    v_mvarId_1572_ = crate::leanh::lean_ctor_get(v___x_1571_, 0);
                    crate::leanh::lean_inc(v_mvarId_1572_);
                    crate::leanh::lean_dec(v___x_1571_);
                    v___x_1573_ = crate::leanh::lean_box(0);
                    v___x_1574_ = 0;
                    v___x_1575_ = l_Lean_Meta_substCore(
                        v_mvarId_1572_,
                        v_eq_1558_,
                        v___x_1568_,
                        v___x_1573_,
                        v___x_1568_,
                        v___x_1574_,
                        v_a_1561_,
                        v_a_1562_,
                        v_a_1563_,
                        v_a_1564_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1575_) == 0 {
                        v_a_1576_ = crate::leanh::lean_ctor_get(v___x_1575_, 0);
                        v_isSharedCheck_1604_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1575_)) as u8;
                        if v_isSharedCheck_1604_ == 0 {
                            v___x_1578_ = v___x_1575_;
                            v_isShared_1579_ = v_isSharedCheck_1604_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1576_);
                            crate::leanh::lean_dec(v___x_1575_);
                            v___x_1578_ = crate::leanh::lean_box(0);
                            v_isShared_1579_ = v_isSharedCheck_1604_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1605_ = crate::leanh::lean_ctor_get(v___x_1575_, 0);
                        v_isSharedCheck_1612_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1575_)) as u8;
                        if v_isSharedCheck_1612_ == 0 {
                            v___x_1607_ = v___x_1575_;
                            v_isShared_1608_ = v_isSharedCheck_1612_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1605_);
                            crate::leanh::lean_dec(v___x_1575_);
                            v___x_1607_ = crate::leanh::lean_box(0);
                            v_isShared_1608_ = v_isSharedCheck_1612_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_1580_ = crate::leanh::lean_ctor_get(v_a_1576_, 0);
                crate::leanh::lean_inc(v_fst_1580_);
                v_snd_1581_ = crate::leanh::lean_ctor_get(v_a_1576_, 1);
                crate::leanh::lean_inc(v_snd_1581_);
                crate::leanh::lean_dec(v_a_1576_);
                v___x_1582_ = lean_st_ref_take(v_a_1560_);
                v_xs_1583_ = crate::leanh::lean_ctor_get(v___x_1582_, 1);
                v_eqs_1584_ = crate::leanh::lean_ctor_get(v___x_1582_, 2);
                v_eqsNew_1585_ = crate::leanh::lean_ctor_get(v___x_1582_, 3);
                v_isSharedCheck_1602_ = (!crate::leanh::lean_is_exclusive(v___x_1582_)) as u8;
                if v_isSharedCheck_1602_ == 0 {
                    v_unused_1603_ = crate::leanh::lean_ctor_get(v___x_1582_, 0);
                    crate::leanh::lean_dec(v_unused_1603_);
                    v___x_1587_ = v___x_1582_;
                    v_isShared_1588_ = v_isSharedCheck_1602_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_eqsNew_1585_);
                    crate::leanh::lean_inc(v_eqs_1584_);
                    crate::leanh::lean_inc(v_xs_1583_);
                    crate::leanh::lean_dec(v___x_1582_);
                    v___x_1587_ = crate::leanh::lean_box(0);
                    v_isShared_1588_ = v_isSharedCheck_1602_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1589_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_applySubst___closed__0;
                crate::leanh::lean_inc(v_xs_1583_);
                v___x_1590_ = l___private_Init_Data_List_Impl_0__List_eraseTR_go___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__2(v_xs_1583_, v_rhs_1559_, v_xs_1583_, v___x_1589_);
                crate::leanh::lean_dec(v_xs_1583_);
                crate::leanh::lean_inc_n(v_fst_1580_, 2);
                v___x_1591_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_applySubst(
                    v_fst_1580_,
                    v___x_1590_,
                );
                v___x_1592_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_applySubst(
                    v_fst_1580_,
                    v_eqs_1584_,
                );
                v___x_1593_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_applySubst(
                    v_fst_1580_,
                    v_eqsNew_1585_,
                );
                if v_isShared_1588_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1587_, 3, v___x_1593_);
                    crate::leanh::lean_ctor_set(v___x_1587_, 2, v___x_1592_);
                    crate::leanh::lean_ctor_set(v___x_1587_, 1, v___x_1591_);
                    crate::leanh::lean_ctor_set(v___x_1587_, 0, v_snd_1581_);
                    v___x_1595_ = v___x_1587_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1601_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1601_, 0, v_snd_1581_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1601_, 1, v___x_1591_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1601_, 2, v___x_1592_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1601_, 3, v___x_1593_);
                    v___x_1595_ = v_reuseFailAlloc_1601_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1596_ = lean_st_ref_set(v_a_1560_, v___x_1595_);
                v___x_1597_ = crate::leanh::lean_box(0);
                if v_isShared_1579_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1578_, 0, v___x_1597_);
                    v___x_1599_ = v___x_1578_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1600_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1600_, 0, v___x_1597_);
                    v___x_1599_ = v_reuseFailAlloc_1600_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1599_;
            }
            5 => {
                if v_isShared_1608_ == 0 {
                    v___x_1610_ = v___x_1607_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1611_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1611_, 0, v_a_1605_);
                    v___x_1610_ = v_reuseFailAlloc_1611_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1610_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS___boxed(
    mut v_eq_1613_: *mut crate::leanh::LeanObject,
    mut v_rhs_1614_: *mut crate::leanh::LeanObject,
    mut v_a_1615_: *mut crate::leanh::LeanObject,
    mut v_a_1616_: *mut crate::leanh::LeanObject,
    mut v_a_1617_: *mut crate::leanh::LeanObject,
    mut v_a_1618_: *mut crate::leanh::LeanObject,
    mut v_a_1619_: *mut crate::leanh::LeanObject,
    mut v_a_1620_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1621_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS(
        v_eq_1613_,
        v_rhs_1614_,
        v_a_1615_,
        v_a_1616_,
        v_a_1617_,
        v_a_1618_,
        v_a_1619_,
    );
    crate::leanh::lean_dec(v_a_1619_);
    crate::leanh::lean_dec_ref(v_a_1618_);
    crate::leanh::lean_dec(v_a_1617_);
    crate::leanh::lean_dec_ref(v_a_1616_);
    crate::leanh::lean_dec(v_a_1615_);
    crate::leanh::lean_dec(v_rhs_1614_);
    return v_res_1621_;
}
pub unsafe fn l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_isDone___redArg(
    mut v_a_1622_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eqs_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1626_: u8 = 0;
    let mut v___x_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1624_ = lean_st_ref_get(v_a_1622_);
    v_eqs_1625_ = crate::leanh::lean_ctor_get(v___x_1624_, 2);
    crate::leanh::lean_inc(v_eqs_1625_);
    crate::leanh::lean_dec(v___x_1624_);
    v___x_1626_ = l_List_isEmpty___redArg(v_eqs_1625_);
    crate::leanh::lean_dec(v_eqs_1625_);
    v___x_1627_ = crate::leanh::lean_box((v___x_1626_) as usize);
    v___x_1628_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1628_, 0, v___x_1627_);
    return v___x_1628_;
}
pub unsafe fn l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_isDone___redArg___boxed(
    mut v_a_1629_: *mut crate::leanh::LeanObject,
    mut v_a_1630_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1631_ =
        l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_isDone___redArg(v_a_1629_);
    crate::leanh::lean_dec(v_a_1629_);
    return v_res_1631_;
}
pub unsafe fn l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_isDone(
    mut v_a_1632_: *mut crate::leanh::LeanObject,
    mut v_a_1633_: *mut crate::leanh::LeanObject,
    mut v_a_1634_: *mut crate::leanh::LeanObject,
    mut v_a_1635_: *mut crate::leanh::LeanObject,
    mut v_a_1636_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1638_ =
        l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_isDone___redArg(v_a_1632_);
    return v___x_1638_;
}
pub unsafe fn l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_isDone___boxed(
    mut v_a_1639_: *mut crate::leanh::LeanObject,
    mut v_a_1640_: *mut crate::leanh::LeanObject,
    mut v_a_1641_: *mut crate::leanh::LeanObject,
    mut v_a_1642_: *mut crate::leanh::LeanObject,
    mut v_a_1643_: *mut crate::leanh::LeanObject,
    mut v_a_1644_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1645_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_isDone(
        v_a_1639_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_,
    );
    crate::leanh::lean_dec(v_a_1643_);
    crate::leanh::lean_dec_ref(v_a_1642_);
    crate::leanh::lean_dec(v_a_1641_);
    crate::leanh::lean_dec_ref(v_a_1640_);
    crate::leanh::lean_dec(v_a_1639_);
    return v_res_1645_;
}
pub unsafe fn l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_contradiction(
    mut v_mvarId_1650_: *mut crate::leanh::LeanObject,
    mut v_a_1651_: *mut crate::leanh::LeanObject,
    mut v_a_1652_: *mut crate::leanh::LeanObject,
    mut v_a_1653_: *mut crate::leanh::LeanObject,
    mut v_a_1654_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1656_ =
        l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_contradiction___closed__0;
    v___x_1657_ = l_Lean_MVarId_contradictionCore(
        v_mvarId_1650_,
        v___x_1656_,
        v_a_1651_,
        v_a_1652_,
        v_a_1653_,
        v_a_1654_,
    );
    return v___x_1657_;
}
pub unsafe fn l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_contradiction___boxed(
    mut v_mvarId_1658_: *mut crate::leanh::LeanObject,
    mut v_a_1659_: *mut crate::leanh::LeanObject,
    mut v_a_1660_: *mut crate::leanh::LeanObject,
    mut v_a_1661_: *mut crate::leanh::LeanObject,
    mut v_a_1662_: *mut crate::leanh::LeanObject,
    mut v_a_1663_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1664_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_contradiction(
        v_mvarId_1658_,
        v_a_1659_,
        v_a_1660_,
        v_a_1661_,
        v_a_1662_,
    );
    crate::leanh::lean_dec(v_a_1662_);
    crate::leanh::lean_dec_ref(v_a_1661_);
    crate::leanh::lean_dec(v_a_1660_);
    crate::leanh::lean_dec_ref(v_a_1659_);
    return v_res_1664_;
}
pub unsafe fn l_Lean_commitWhen___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction_spec__0(
    mut v_x_1665_: *mut crate::leanh::LeanObject,
    mut v___y_1666_: *mut crate::leanh::LeanObject,
    mut v___y_1667_: *mut crate::leanh::LeanObject,
    mut v___y_1668_: *mut crate::leanh::LeanObject,
    mut v___y_1669_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1676_: u8 = 0;
    let mut v___x_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1680_: u8 = 0;
    let mut v___x_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1684_: u8 = 0;
    let mut v_unused_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1689_: u8 = 0;
    let mut v___x_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1693_: u8 = 0;
    let mut v___y_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: u8 = 0;
    let mut v___x_1698_: u8 = 0;
    let mut v___x_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: u8 = 0;
    let mut v___x_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1705_: u8 = 0;
    let mut v___x_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1709_: u8 = 0;
    let mut v_unused_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1714_: u8 = 0;
    let mut v___x_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1718_: u8 = 0;
    let mut v_a_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1723_: u8 = 0;
    let mut v___x_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1727_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1671_ = l_Lean_Meta_saveState___redArg(v___y_1667_, v___y_1669_);
                if crate::leanh::lean_obj_tag(v___x_1671_) == 0 {
                    v_a_1672_ = crate::leanh::lean_ctor_get(v___x_1671_, 0);
                    crate::leanh::lean_inc(v_a_1672_);
                    crate::leanh::lean_dec_ref_known(v___x_1671_, 1);
                    crate::leanh::lean_inc(v___y_1669_);
                    crate::leanh::lean_inc_ref(v___y_1668_);
                    crate::leanh::lean_inc(v___y_1667_);
                    crate::leanh::lean_inc_ref(v___y_1666_);
                    v___x_1699_ = crate::leanh::lean_apply_5(
                        v_x_1665_,
                        v___y_1666_,
                        v___y_1667_,
                        v___y_1668_,
                        v___y_1669_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_1699_) == 0 {
                        v_a_1700_ = crate::leanh::lean_ctor_get(v___x_1699_, 0);
                        crate::leanh::lean_inc(v_a_1700_);
                        v___x_1701_ = (crate::leanh::lean_unbox(v_a_1700_) as u8);
                        if v___x_1701_ == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_1699_, 1);
                            v___x_1702_ = l_Lean_Meta_SavedState_restore___redArg(
                                v_a_1672_,
                                v___y_1667_,
                                v___y_1669_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_1702_) == 0 {
                                crate::leanh::lean_dec(v_a_1672_);
                                v_isSharedCheck_1709_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1702_)) as u8;
                                if v_isSharedCheck_1709_ == 0 {
                                    v_unused_1710_ = crate::leanh::lean_ctor_get(v___x_1702_, 0);
                                    crate::leanh::lean_dec(v_unused_1710_);
                                    v___x_1704_ = v___x_1702_;
                                    v_isShared_1705_ = v_isSharedCheck_1709_;
                                    state = 7;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v___x_1702_);
                                    v___x_1704_ = crate::leanh::lean_box(0);
                                    v_isShared_1705_ = v_isSharedCheck_1709_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_1700_);
                                v_a_1711_ = crate::leanh::lean_ctor_get(v___x_1702_, 0);
                                v_isSharedCheck_1718_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1702_)) as u8;
                                if v_isSharedCheck_1718_ == 0 {
                                    v___x_1713_ = v___x_1702_;
                                    v_isShared_1714_ = v_isSharedCheck_1718_;
                                    state = 9;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1711_);
                                    crate::leanh::lean_dec(v___x_1702_);
                                    v___x_1713_ = crate::leanh::lean_box(0);
                                    v_isShared_1714_ = v_isSharedCheck_1718_;
                                    state = 9;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_1700_);
                            crate::leanh::lean_dec(v_a_1672_);
                            return v___x_1699_;
                        }
                    } else {
                        v_a_1719_ = crate::leanh::lean_ctor_get(v___x_1699_, 0);
                        crate::leanh::lean_inc(v_a_1719_);
                        v___y_1695_ = v___x_1699_;
                        v_a_1696_ = v_a_1719_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_x_1665_);
                    v_a_1720_ = crate::leanh::lean_ctor_get(v___x_1671_, 0);
                    v_isSharedCheck_1727_ = (!crate::leanh::lean_is_exclusive(v___x_1671_)) as u8;
                    if v_isSharedCheck_1727_ == 0 {
                        v___x_1722_ = v___x_1671_;
                        v_isShared_1723_ = v_isSharedCheck_1727_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1720_);
                        crate::leanh::lean_dec(v___x_1671_);
                        v___x_1722_ = crate::leanh::lean_box(0);
                        v_isShared_1723_ = v_isSharedCheck_1727_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_1676_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_1674_);
                    v___x_1677_ = l_Lean_Meta_SavedState_restore___redArg(
                        v_a_1672_,
                        v___y_1667_,
                        v___y_1669_,
                    );
                    crate::leanh::lean_dec(v_a_1672_);
                    if crate::leanh::lean_obj_tag(v___x_1677_) == 0 {
                        v_isSharedCheck_1684_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1677_)) as u8;
                        if v_isSharedCheck_1684_ == 0 {
                            v_unused_1685_ = crate::leanh::lean_ctor_get(v___x_1677_, 0);
                            crate::leanh::lean_dec(v_unused_1685_);
                            v___x_1679_ = v___x_1677_;
                            v_isShared_1680_ = v_isSharedCheck_1684_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_1677_);
                            v___x_1679_ = crate::leanh::lean_box(0);
                            v_isShared_1680_ = v_isSharedCheck_1684_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___y_1675_);
                        v_a_1686_ = crate::leanh::lean_ctor_get(v___x_1677_, 0);
                        v_isSharedCheck_1693_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1677_)) as u8;
                        if v_isSharedCheck_1693_ == 0 {
                            v___x_1688_ = v___x_1677_;
                            v_isShared_1689_ = v_isSharedCheck_1693_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1686_);
                            crate::leanh::lean_dec(v___x_1677_);
                            v___x_1688_ = crate::leanh::lean_box(0);
                            v_isShared_1689_ = v_isSharedCheck_1693_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_1675_);
                    crate::leanh::lean_dec(v_a_1672_);
                    return v___y_1674_;
                }
            }
            2 => {
                if v_isShared_1680_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1679_, 1);
                    crate::leanh::lean_ctor_set(v___x_1679_, 0, v___y_1675_);
                    v___x_1682_ = v___x_1679_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1683_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1683_, 0, v___y_1675_);
                    v___x_1682_ = v_reuseFailAlloc_1683_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1682_;
            }
            4 => {
                if v_isShared_1689_ == 0 {
                    v___x_1691_ = v___x_1688_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1692_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1692_, 0, v_a_1686_);
                    v___x_1691_ = v_reuseFailAlloc_1692_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1691_;
            }
            6 => {
                v___x_1697_ = l_Lean_Exception_isInterrupt(v_a_1696_);
                if v___x_1697_ == 0 {
                    crate::leanh::lean_inc_ref(v_a_1696_);
                    v___x_1698_ = l_Lean_Exception_isRuntime(v_a_1696_);
                    v___y_1674_ = v___y_1695_;
                    v___y_1675_ = v_a_1696_;
                    v___y_1676_ = v___x_1698_;
                    state = 1;
                    continue;
                } else {
                    v___y_1674_ = v___y_1695_;
                    v___y_1675_ = v_a_1696_;
                    v___y_1676_ = v___x_1697_;
                    state = 1;
                    continue;
                }
            }
            7 => {
                if v_isShared_1705_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1704_, 0, v_a_1700_);
                    v___x_1707_ = v___x_1704_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1708_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1708_, 0, v_a_1700_);
                    v___x_1707_ = v_reuseFailAlloc_1708_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1707_;
            }
            9 => {
                crate::leanh::lean_inc(v_a_1711_);
                if v_isShared_1714_ == 0 {
                    v___x_1716_ = v___x_1713_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1717_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1717_, 0, v_a_1711_);
                    v___x_1716_ = v_reuseFailAlloc_1717_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___y_1695_ = v___x_1716_;
                v_a_1696_ = v_a_1711_;
                state = 6;
                continue;
            }
            11 => {
                if v_isShared_1723_ == 0 {
                    v___x_1725_ = v___x_1722_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1726_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1726_, 0, v_a_1720_);
                    v___x_1725_ = v_reuseFailAlloc_1726_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1725_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_commitWhen___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction_spec__0___boxed(
    mut v_x_1728_: *mut crate::leanh::LeanObject,
    mut v___y_1729_: *mut crate::leanh::LeanObject,
    mut v___y_1730_: *mut crate::leanh::LeanObject,
    mut v___y_1731_: *mut crate::leanh::LeanObject,
    mut v___y_1732_: *mut crate::leanh::LeanObject,
    mut v___y_1733_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1734_ = l_Lean_commitWhen___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction_spec__0(v_x_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_);
    crate::leanh::lean_dec(v___y_1732_);
    crate::leanh::lean_dec_ref(v___y_1731_);
    crate::leanh::lean_dec(v___y_1730_);
    crate::leanh::lean_dec_ref(v___y_1729_);
    return v_res_1734_;
}
pub unsafe fn l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction___lam__0(
    mut v_mvarId_1735_: *mut crate::leanh::LeanObject,
    mut v_forbidden_1736_: *mut crate::leanh::LeanObject,
    mut v___y_1737_: *mut crate::leanh::LeanObject,
    mut v___y_1738_: *mut crate::leanh::LeanObject,
    mut v___y_1739_: *mut crate::leanh::LeanObject,
    mut v___y_1740_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1750_: u8 = 0;
    let mut v___x_1751_: u8 = 0;
    let mut v___x_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_forbidden_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: u8 = 0;
    let mut v___x_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1761_: u8 = 0;
    let mut v_a_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1765_: u8 = 0;
    let mut v___x_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1769_: u8 = 0;
    let mut v_a_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1773_: u8 = 0;
    let mut v___x_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1777_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1742_ = l_Lean_Meta_substVars(
                    v_mvarId_1735_,
                    v___y_1737_,
                    v___y_1738_,
                    v___y_1739_,
                    v___y_1740_,
                );
                if crate::leanh::lean_obj_tag(v___x_1742_) == 0 {
                    v_a_1743_ = crate::leanh::lean_ctor_get(v___x_1742_, 0);
                    crate::leanh::lean_inc_n(v_a_1743_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_1742_, 1);
                    v___x_1744_ = crate::leanh::lean_box(0);
                    v___x_1745_ = crate::leanh::lean_unsigned_to_nat(5);
                    v___x_1746_ = l_Lean_Meta_injections(
                        v_a_1743_,
                        v___x_1744_,
                        v___x_1745_,
                        v_forbidden_1736_,
                        v___y_1737_,
                        v___y_1738_,
                        v___y_1739_,
                        v___y_1740_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1746_) == 0 {
                        v_a_1747_ = crate::leanh::lean_ctor_get(v___x_1746_, 0);
                        v_isSharedCheck_1761_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1746_)) as u8;
                        if v_isSharedCheck_1761_ == 0 {
                            v___x_1749_ = v___x_1746_;
                            v_isShared_1750_ = v_isSharedCheck_1761_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1747_);
                            crate::leanh::lean_dec(v___x_1746_);
                            v___x_1749_ = crate::leanh::lean_box(0);
                            v_isShared_1750_ = v_isSharedCheck_1761_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_1743_);
                        v_a_1762_ = crate::leanh::lean_ctor_get(v___x_1746_, 0);
                        v_isSharedCheck_1769_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1746_)) as u8;
                        if v_isSharedCheck_1769_ == 0 {
                            v___x_1764_ = v___x_1746_;
                            v_isShared_1765_ = v_isSharedCheck_1769_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1762_);
                            crate::leanh::lean_dec(v___x_1746_);
                            v___x_1764_ = crate::leanh::lean_box(0);
                            v_isShared_1765_ = v_isSharedCheck_1769_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_forbidden_1736_);
                    v_a_1770_ = crate::leanh::lean_ctor_get(v___x_1742_, 0);
                    v_isSharedCheck_1777_ = (!crate::leanh::lean_is_exclusive(v___x_1742_)) as u8;
                    if v_isSharedCheck_1777_ == 0 {
                        v___x_1772_ = v___x_1742_;
                        v_isShared_1773_ = v_isSharedCheck_1777_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1770_);
                        crate::leanh::lean_dec(v___x_1742_);
                        v___x_1772_ = crate::leanh::lean_box(0);
                        v_isShared_1773_ = v_isSharedCheck_1777_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_1747_) == 0 {
                    crate::leanh::lean_dec(v_a_1743_);
                    v___x_1751_ = 1;
                    v___x_1752_ = crate::leanh::lean_box((v___x_1751_) as usize);
                    if v_isShared_1750_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1749_, 0, v___x_1752_);
                        v___x_1754_ = v___x_1749_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1755_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1755_, 0, v___x_1752_);
                        v___x_1754_ = v_reuseFailAlloc_1755_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1749_);
                    v_mvarId_1756_ = crate::leanh::lean_ctor_get(v_a_1747_, 0);
                    crate::leanh::lean_inc(v_mvarId_1756_);
                    v_forbidden_1757_ = crate::leanh::lean_ctor_get(v_a_1747_, 2);
                    crate::leanh::lean_inc(v_forbidden_1757_);
                    crate::leanh::lean_dec_ref_known(v_a_1747_, 3);
                    v___x_1758_ = l_Lean_instBEqMVarId_beq(v_mvarId_1756_, v_a_1743_);
                    if v___x_1758_ == 0 {
                        crate::leanh::lean_dec(v_a_1743_);
                        v___x_1759_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction(v_mvarId_1756_, v_forbidden_1757_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
                        return v___x_1759_;
                    } else {
                        crate::leanh::lean_dec(v_forbidden_1757_);
                        crate::leanh::lean_dec(v_mvarId_1756_);
                        v___x_1760_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_contradiction(v_a_1743_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
                        return v___x_1760_;
                    }
                }
            }
            2 => {
                return v___x_1754_;
            }
            3 => {
                if v_isShared_1765_ == 0 {
                    v___x_1767_ = v___x_1764_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1768_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1768_, 0, v_a_1762_);
                    v___x_1767_ = v_reuseFailAlloc_1768_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1767_;
            }
            5 => {
                if v_isShared_1773_ == 0 {
                    v___x_1775_ = v___x_1772_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1776_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1776_, 0, v_a_1770_);
                    v___x_1775_ = v_reuseFailAlloc_1776_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1775_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction___lam__0___boxed(
    mut v_mvarId_1778_: *mut crate::leanh::LeanObject,
    mut v_forbidden_1779_: *mut crate::leanh::LeanObject,
    mut v___y_1780_: *mut crate::leanh::LeanObject,
    mut v___y_1781_: *mut crate::leanh::LeanObject,
    mut v___y_1782_: *mut crate::leanh::LeanObject,
    mut v___y_1783_: *mut crate::leanh::LeanObject,
    mut v___y_1784_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1785_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction___lam__0(v_mvarId_1778_, v_forbidden_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_);
    crate::leanh::lean_dec(v___y_1783_);
    crate::leanh::lean_dec_ref(v___y_1782_);
    crate::leanh::lean_dec(v___y_1781_);
    crate::leanh::lean_dec_ref(v___y_1780_);
    return v_res_1785_;
}
pub unsafe fn l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction(
    mut v_mvarId_1786_: *mut crate::leanh::LeanObject,
    mut v_forbidden_1787_: *mut crate::leanh::LeanObject,
    mut v_a_1788_: *mut crate::leanh::LeanObject,
    mut v_a_1789_: *mut crate::leanh::LeanObject,
    mut v_a_1790_: *mut crate::leanh::LeanObject,
    mut v_a_1791_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1793_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction___lam__0___boxed as *mut core::ffi::c_void, 7, 2);
    crate::leanh::lean_closure_set(v___f_1793_, 0, v_mvarId_1786_);
    crate::leanh::lean_closure_set(v___f_1793_, 1, v_forbidden_1787_);
    v___x_1794_ = l_Lean_commitWhen___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction_spec__0(v___f_1793_, v_a_1788_, v_a_1789_, v_a_1790_, v_a_1791_);
    return v___x_1794_;
}
pub unsafe fn l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction___boxed(
    mut v_mvarId_1795_: *mut crate::leanh::LeanObject,
    mut v_forbidden_1796_: *mut crate::leanh::LeanObject,
    mut v_a_1797_: *mut crate::leanh::LeanObject,
    mut v_a_1798_: *mut crate::leanh::LeanObject,
    mut v_a_1799_: *mut crate::leanh::LeanObject,
    mut v_a_1800_: *mut crate::leanh::LeanObject,
    mut v_a_1801_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1802_ =
        l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction(
            v_mvarId_1795_,
            v_forbidden_1796_,
            v_a_1797_,
            v_a_1798_,
            v_a_1799_,
            v_a_1800_,
        );
    crate::leanh::lean_dec(v_a_1800_);
    crate::leanh::lean_dec_ref(v_a_1799_);
    crate::leanh::lean_dec(v_a_1798_);
    crate::leanh::lean_dec_ref(v_a_1797_);
    return v_res_1802_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0___redArg___lam__0(
    mut v_x_1803_: *mut crate::leanh::LeanObject,
    mut v___y_1804_: *mut crate::leanh::LeanObject,
    mut v___y_1805_: *mut crate::leanh::LeanObject,
    mut v___y_1806_: *mut crate::leanh::LeanObject,
    mut v___y_1807_: *mut crate::leanh::LeanObject,
    mut v___y_1808_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_1804_);
    v___x_1810_ = crate::leanh::lean_apply_6(
        v_x_1803_,
        v___y_1804_,
        v___y_1805_,
        v___y_1806_,
        v___y_1807_,
        v___y_1808_,
        crate::leanh::lean_box(0),
    );
    return v___x_1810_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0___redArg___lam__0___boxed(
    mut v_x_1811_: *mut crate::leanh::LeanObject,
    mut v___y_1812_: *mut crate::leanh::LeanObject,
    mut v___y_1813_: *mut crate::leanh::LeanObject,
    mut v___y_1814_: *mut crate::leanh::LeanObject,
    mut v___y_1815_: *mut crate::leanh::LeanObject,
    mut v___y_1816_: *mut crate::leanh::LeanObject,
    mut v___y_1817_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1818_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0___redArg___lam__0(v_x_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_);
    crate::leanh::lean_dec(v___y_1812_);
    return v_res_1818_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0___redArg(
    mut v_mvarId_1819_: *mut crate::leanh::LeanObject,
    mut v_x_1820_: *mut crate::leanh::LeanObject,
    mut v___y_1821_: *mut crate::leanh::LeanObject,
    mut v___y_1822_: *mut crate::leanh::LeanObject,
    mut v___y_1823_: *mut crate::leanh::LeanObject,
    mut v___y_1824_: *mut crate::leanh::LeanObject,
    mut v___y_1825_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1832_: u8 = 0;
    let mut v___x_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1836_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_1821_);
                v___f_1827_ = crate::leanh::lean_alloc_closure(l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 7, 2);
                crate::leanh::lean_closure_set(v___f_1827_, 0, v_x_1820_);
                crate::leanh::lean_closure_set(v___f_1827_, 1, v___y_1821_);
                v___x_1828_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    crate::leanh::lean_box(0),
                    v_mvarId_1819_,
                    v___f_1827_,
                    v___y_1822_,
                    v___y_1823_,
                    v___y_1824_,
                    v___y_1825_,
                );
                if crate::leanh::lean_obj_tag(v___x_1828_) == 0 {
                    return v___x_1828_;
                } else {
                    v_a_1829_ = crate::leanh::lean_ctor_get(v___x_1828_, 0);
                    v_isSharedCheck_1836_ = (!crate::leanh::lean_is_exclusive(v___x_1828_)) as u8;
                    if v_isSharedCheck_1836_ == 0 {
                        v___x_1831_ = v___x_1828_;
                        v_isShared_1832_ = v_isSharedCheck_1836_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1829_);
                        crate::leanh::lean_dec(v___x_1828_);
                        v___x_1831_ = crate::leanh::lean_box(0);
                        v_isShared_1832_ = v_isSharedCheck_1836_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1832_ == 0 {
                    v___x_1834_ = v___x_1831_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1835_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1835_, 0, v_a_1829_);
                    v___x_1834_ = v_reuseFailAlloc_1835_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1834_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0___redArg___boxed(
    mut v_mvarId_1837_: *mut crate::leanh::LeanObject,
    mut v_x_1838_: *mut crate::leanh::LeanObject,
    mut v___y_1839_: *mut crate::leanh::LeanObject,
    mut v___y_1840_: *mut crate::leanh::LeanObject,
    mut v___y_1841_: *mut crate::leanh::LeanObject,
    mut v___y_1842_: *mut crate::leanh::LeanObject,
    mut v___y_1843_: *mut crate::leanh::LeanObject,
    mut v___y_1844_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1845_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0___redArg(v_mvarId_1837_, v_x_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_);
    crate::leanh::lean_dec(v___y_1843_);
    crate::leanh::lean_dec_ref(v___y_1842_);
    crate::leanh::lean_dec(v___y_1841_);
    crate::leanh::lean_dec_ref(v___y_1840_);
    crate::leanh::lean_dec(v___y_1839_);
    return v_res_1845_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0(
    mut v_00_u03b1_1846_: *mut crate::leanh::LeanObject,
    mut v_mvarId_1847_: *mut crate::leanh::LeanObject,
    mut v_x_1848_: *mut crate::leanh::LeanObject,
    mut v___y_1849_: *mut crate::leanh::LeanObject,
    mut v___y_1850_: *mut crate::leanh::LeanObject,
    mut v___y_1851_: *mut crate::leanh::LeanObject,
    mut v___y_1852_: *mut crate::leanh::LeanObject,
    mut v___y_1853_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1855_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0___redArg(v_mvarId_1847_, v_x_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_);
    return v___x_1855_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0___boxed(
    mut v_00_u03b1_1856_: *mut crate::leanh::LeanObject,
    mut v_mvarId_1857_: *mut crate::leanh::LeanObject,
    mut v_x_1858_: *mut crate::leanh::LeanObject,
    mut v___y_1859_: *mut crate::leanh::LeanObject,
    mut v___y_1860_: *mut crate::leanh::LeanObject,
    mut v___y_1861_: *mut crate::leanh::LeanObject,
    mut v___y_1862_: *mut crate::leanh::LeanObject,
    mut v___y_1863_: *mut crate::leanh::LeanObject,
    mut v___y_1864_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1865_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0(v_00_u03b1_1856_, v_mvarId_1857_, v_x_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
    crate::leanh::lean_dec(v___y_1863_);
    crate::leanh::lean_dec_ref(v___y_1862_);
    crate::leanh::lean_dec(v___y_1861_);
    crate::leanh::lean_dec_ref(v___y_1860_);
    crate::leanh::lean_dec(v___y_1859_);
    return v_res_1865_;
}
pub unsafe fn l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___lam__0(
    mut v_____r_1866_: *mut crate::leanh::LeanObject,
    mut v___y_1867_: *mut crate::leanh::LeanObject,
    mut v___y_1868_: *mut crate::leanh::LeanObject,
    mut v___y_1869_: *mut crate::leanh::LeanObject,
    mut v___y_1870_: *mut crate::leanh::LeanObject,
    mut v___y_1871_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1873_: u8 = 0;
    let mut v___x_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1873_ = 1;
    v___x_1874_ = crate::leanh::lean_box((v___x_1873_) as usize);
    v___x_1875_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1875_, 0, v___x_1874_);
    return v___x_1875_;
}
pub unsafe fn l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___lam__0___boxed(
    mut v_____r_1876_: *mut crate::leanh::LeanObject,
    mut v___y_1877_: *mut crate::leanh::LeanObject,
    mut v___y_1878_: *mut crate::leanh::LeanObject,
    mut v___y_1879_: *mut crate::leanh::LeanObject,
    mut v___y_1880_: *mut crate::leanh::LeanObject,
    mut v___y_1881_: *mut crate::leanh::LeanObject,
    mut v___y_1882_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1883_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___lam__0(
        v_____r_1876_,
        v___y_1877_,
        v___y_1878_,
        v___y_1879_,
        v___y_1880_,
        v___y_1881_,
    );
    crate::leanh::lean_dec(v___y_1881_);
    crate::leanh::lean_dec_ref(v___y_1880_);
    crate::leanh::lean_dec(v___y_1879_);
    crate::leanh::lean_dec_ref(v___y_1878_);
    crate::leanh::lean_dec(v___y_1877_);
    return v_res_1883_;
}
pub unsafe fn l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___lam__1(
    mut v_eqs_1884_: *mut crate::leanh::LeanObject,
    mut v___f_1885_: *mut crate::leanh::LeanObject,
    mut v_mvarId_1886_: *mut crate::leanh::LeanObject,
    mut v_xs_1887_: *mut crate::leanh::LeanObject,
    mut v___y_1888_: *mut crate::leanh::LeanObject,
    mut v___y_1889_: *mut crate::leanh::LeanObject,
    mut v___y_1890_: *mut crate::leanh::LeanObject,
    mut v___y_1891_: *mut crate::leanh::LeanObject,
    mut v___y_1892_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1898_: u8 = 0;
    let mut v___y_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1906_: u8 = 0;
    let mut v___x_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eqs_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eqsNew_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1914_: u8 = 0;
    let mut v___x_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1924_: u8 = 0;
    let mut v___x_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1937_: u8 = 0;
    let mut v___x_1938_: u8 = 0;
    let mut v___x_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newEqs_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eqs_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eqsNew_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1951_: u8 = 0;
    let mut v___x_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1960_: u8 = 0;
    let mut v_unused_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1962_: u8 = 0;
    let mut v_a_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: u8 = 0;
    let mut v___x_1965_: u8 = 0;
    let mut v___x_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eqsNew_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1972_: u8 = 0;
    let mut v___x_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: u8 = 0;
    let mut v___x_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1992_: u8 = 0;
    let mut v_fst_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1997_: u8 = 0;
    let mut v___x_1998_: u8 = 0;
    let mut v___x_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eqs_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eqsNew_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2005_: u8 = 0;
    let mut v___x_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2017_: u8 = 0;
    let mut v_unused_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2024_: u8 = 0;
    let mut v___x_2025_: u8 = 0;
    let mut v___x_2026_: u8 = 0;
    let mut v___x_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2031_: u8 = 0;
    let mut v_isSharedCheck_2032_: u8 = 0;
    let mut v_isSharedCheck_2033_: u8 = 0;
    let mut v_a_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2037_: u8 = 0;
    let mut v___x_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2041_: u8 = 0;
    let mut v_a_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2045_: u8 = 0;
    let mut v___x_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2049_: u8 = 0;
    let mut v___x_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: u8 = 0;
    let mut v___y_2060_: u8 = 0;
    let mut v___x_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2065_: u8 = 0;
    let mut v___x_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2070_: u8 = 0;
    let mut v_unused_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2075_: u8 = 0;
    let mut v___x_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2079_: u8 = 0;
    let mut v___x_2080_: u8 = 0;
    let mut v___x_2081_: u8 = 0;
    let mut v___x_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: u8 = 0;
    let mut v___x_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2088_: u8 = 0;
    let mut v___x_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eqs_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eqsNew_2092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2095_: u8 = 0;
    let mut v___x_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2104_: u8 = 0;
    let mut v_unused_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2106_: u8 = 0;
    let mut v_a_2107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2110_: u8 = 0;
    let mut v___x_2112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2114_: u8 = 0;
    let mut v_a_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2118_: u8 = 0;
    let mut v___x_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2122_: u8 = 0;
    let mut v_a_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2126_: u8 = 0;
    let mut v___x_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2130_: u8 = 0;
    let mut v_reuseFailAlloc_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2132_: u8 = 0;
    let mut v_unused_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2134_: u8 = 0;
    let mut v___x_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_eqs_1884_) == 1 {
                    v_head_1894_ = crate::leanh::lean_ctor_get(v_eqs_1884_, 0);
                    v_tail_1895_ = crate::leanh::lean_ctor_get(v_eqs_1884_, 1);
                    v_isSharedCheck_2134_ = (!crate::leanh::lean_is_exclusive(v_eqs_1884_)) as u8;
                    if v_isSharedCheck_2134_ == 0 {
                        v___x_1897_ = v_eqs_1884_;
                        v_isShared_1898_ = v_isSharedCheck_2134_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1895_);
                        crate::leanh::lean_inc(v_head_1894_);
                        crate::leanh::lean_dec(v_eqs_1884_);
                        v___x_1897_ = crate::leanh::lean_box(0);
                        v_isShared_1898_ = v_isSharedCheck_2134_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_mvarId_1886_);
                    crate::leanh::lean_dec(v_eqs_1884_);
                    v___x_2135_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc(v___y_1892_);
                    crate::leanh::lean_inc_ref(v___y_1891_);
                    crate::leanh::lean_inc(v___y_1890_);
                    crate::leanh::lean_inc_ref(v___y_1889_);
                    crate::leanh::lean_inc(v___y_1888_);
                    v___x_2136_ = crate::leanh::lean_apply_7(
                        v___f_1885_,
                        v___x_2135_,
                        v___y_1888_,
                        v___y_1889_,
                        v___y_1890_,
                        v___y_1891_,
                        v___y_1892_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_2136_;
                }
            }
            1 => {
                v___x_1966_ = lean_st_ref_take(v___y_1888_);
                v_mvarId_1967_ = crate::leanh::lean_ctor_get(v___x_1966_, 0);
                v_xs_1968_ = crate::leanh::lean_ctor_get(v___x_1966_, 1);
                v_eqsNew_1969_ = crate::leanh::lean_ctor_get(v___x_1966_, 3);
                v_isSharedCheck_2132_ = (!crate::leanh::lean_is_exclusive(v___x_1966_)) as u8;
                if v_isSharedCheck_2132_ == 0 {
                    v_unused_2133_ = crate::leanh::lean_ctor_get(v___x_1966_, 2);
                    crate::leanh::lean_dec(v_unused_2133_);
                    v___x_1971_ = v___x_1966_;
                    v_isShared_1972_ = v_isSharedCheck_2132_;
                    state = 11;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_eqsNew_1969_);
                    crate::leanh::lean_inc(v_xs_1968_);
                    crate::leanh::lean_inc(v_mvarId_1967_);
                    crate::leanh::lean_dec(v___x_1966_);
                    v___x_1971_ = crate::leanh::lean_box(0);
                    v_isShared_1972_ = v_isSharedCheck_2132_;
                    state = 11;
                    continue;
                }
            }
            2 => {
                if v___y_1906_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_1901_);
                    v___x_1907_ = lean_st_ref_take(v___y_1904_);
                    v_mvarId_1908_ = crate::leanh::lean_ctor_get(v___x_1907_, 0);
                    v_xs_1909_ = crate::leanh::lean_ctor_get(v___x_1907_, 1);
                    v_eqs_1910_ = crate::leanh::lean_ctor_get(v___x_1907_, 2);
                    v_eqsNew_1911_ = crate::leanh::lean_ctor_get(v___x_1907_, 3);
                    v_isSharedCheck_1924_ = (!crate::leanh::lean_is_exclusive(v___x_1907_)) as u8;
                    if v_isSharedCheck_1924_ == 0 {
                        v___x_1913_ = v___x_1907_;
                        v_isShared_1914_ = v_isSharedCheck_1924_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_eqsNew_1911_);
                        crate::leanh::lean_inc(v_eqs_1910_);
                        crate::leanh::lean_inc(v_xs_1909_);
                        crate::leanh::lean_inc(v_mvarId_1908_);
                        crate::leanh::lean_dec(v___x_1907_);
                        v___x_1913_ = crate::leanh::lean_box(0);
                        v_isShared_1914_ = v_isSharedCheck_1924_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1897_);
                    crate::leanh::lean_dec(v_head_1894_);
                    crate::leanh::lean_dec_ref(v___f_1885_);
                    v___x_1925_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1925_, 0, v___y_1901_);
                    return v___x_1925_;
                }
            }
            3 => {
                if v_isShared_1898_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1897_, 1, v_eqsNew_1911_);
                    v___x_1916_ = v___x_1897_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1923_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1923_, 0, v_head_1894_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1923_, 1, v_eqsNew_1911_);
                    v___x_1916_ = v_reuseFailAlloc_1923_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1914_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1913_, 3, v___x_1916_);
                    v___x_1918_ = v___x_1913_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1922_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1922_, 0, v_mvarId_1908_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1922_, 1, v_xs_1909_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1922_, 2, v_eqs_1910_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1922_, 3, v___x_1916_);
                    v___x_1918_ = v_reuseFailAlloc_1922_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1919_ = lean_st_ref_set(v___y_1904_, v___x_1918_);
                v___x_1920_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v___y_1903_);
                crate::leanh::lean_inc_ref(v___y_1905_);
                crate::leanh::lean_inc(v___y_1900_);
                crate::leanh::lean_inc_ref(v___y_1902_);
                crate::leanh::lean_inc(v___y_1904_);
                v___x_1921_ = crate::leanh::lean_apply_7(
                    v___f_1885_,
                    v___x_1920_,
                    v___y_1904_,
                    v___y_1902_,
                    v___y_1900_,
                    v___y_1905_,
                    v___y_1903_,
                    crate::leanh::lean_box(0),
                );
                return v___x_1921_;
            }
            6 => {
                v___x_1932_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v_head_1894_);
                v___x_1933_ = l_Lean_Meta_injection(
                    v_mvarId_1886_,
                    v_head_1894_,
                    v___x_1932_,
                    v___y_1928_,
                    v___y_1929_,
                    v___y_1930_,
                    v___y_1931_,
                );
                if crate::leanh::lean_obj_tag(v___x_1933_) == 0 {
                    crate::leanh::lean_del_object(v___x_1897_);
                    crate::leanh::lean_dec(v_head_1894_);
                    v_a_1934_ = crate::leanh::lean_ctor_get(v___x_1933_, 0);
                    v_isSharedCheck_1962_ = (!crate::leanh::lean_is_exclusive(v___x_1933_)) as u8;
                    if v_isSharedCheck_1962_ == 0 {
                        v___x_1936_ = v___x_1933_;
                        v_isShared_1937_ = v_isSharedCheck_1962_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1934_);
                        crate::leanh::lean_dec(v___x_1933_);
                        v___x_1936_ = crate::leanh::lean_box(0);
                        v_isShared_1937_ = v_isSharedCheck_1962_;
                        state = 7;
                        continue;
                    }
                } else {
                    v_a_1963_ = crate::leanh::lean_ctor_get(v___x_1933_, 0);
                    crate::leanh::lean_inc(v_a_1963_);
                    crate::leanh::lean_dec_ref_known(v___x_1933_, 1);
                    v___x_1964_ = l_Lean_Exception_isInterrupt(v_a_1963_);
                    if v___x_1964_ == 0 {
                        crate::leanh::lean_inc(v_a_1963_);
                        v___x_1965_ = l_Lean_Exception_isRuntime(v_a_1963_);
                        v___y_1900_ = v___y_1929_;
                        v___y_1901_ = v_a_1963_;
                        v___y_1902_ = v___y_1928_;
                        v___y_1903_ = v___y_1931_;
                        v___y_1904_ = v___y_1927_;
                        v___y_1905_ = v___y_1930_;
                        v___y_1906_ = v___x_1965_;
                        state = 2;
                        continue;
                    } else {
                        v___y_1900_ = v___y_1929_;
                        v___y_1901_ = v_a_1963_;
                        v___y_1902_ = v___y_1928_;
                        v___y_1903_ = v___y_1931_;
                        v___y_1904_ = v___y_1927_;
                        v___y_1905_ = v___y_1930_;
                        v___y_1906_ = v___x_1964_;
                        state = 2;
                        continue;
                    }
                }
            }
            7 => {
                if crate::leanh::lean_obj_tag(v_a_1934_) == 0 {
                    crate::leanh::lean_dec_ref(v___f_1885_);
                    v___x_1938_ = 0;
                    v___x_1939_ = crate::leanh::lean_box((v___x_1938_) as usize);
                    if v_isShared_1937_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1936_, 0, v___x_1939_);
                        v___x_1941_ = v___x_1936_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_1942_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1942_, 0, v___x_1939_);
                        v___x_1941_ = v_reuseFailAlloc_1942_;
                        state = 8;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1936_);
                    v_mvarId_1943_ = crate::leanh::lean_ctor_get(v_a_1934_, 0);
                    crate::leanh::lean_inc(v_mvarId_1943_);
                    v_newEqs_1944_ = crate::leanh::lean_ctor_get(v_a_1934_, 1);
                    crate::leanh::lean_inc_ref(v_newEqs_1944_);
                    crate::leanh::lean_dec_ref_known(v_a_1934_, 3);
                    v___x_1945_ = lean_st_ref_take(v___y_1927_);
                    v_xs_1946_ = crate::leanh::lean_ctor_get(v___x_1945_, 1);
                    v_eqs_1947_ = crate::leanh::lean_ctor_get(v___x_1945_, 2);
                    v_eqsNew_1948_ = crate::leanh::lean_ctor_get(v___x_1945_, 3);
                    v_isSharedCheck_1960_ = (!crate::leanh::lean_is_exclusive(v___x_1945_)) as u8;
                    if v_isSharedCheck_1960_ == 0 {
                        v_unused_1961_ = crate::leanh::lean_ctor_get(v___x_1945_, 0);
                        crate::leanh::lean_dec(v_unused_1961_);
                        v___x_1950_ = v___x_1945_;
                        v_isShared_1951_ = v_isSharedCheck_1960_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_eqsNew_1948_);
                        crate::leanh::lean_inc(v_eqs_1947_);
                        crate::leanh::lean_inc(v_xs_1946_);
                        crate::leanh::lean_dec(v___x_1945_);
                        v___x_1950_ = crate::leanh::lean_box(0);
                        v_isShared_1951_ = v_isSharedCheck_1960_;
                        state = 9;
                        continue;
                    }
                }
            }
            8 => {
                return v___x_1941_;
            }
            9 => {
                v___x_1952_ = lean_array_to_list(v_newEqs_1944_);
                v___x_1953_ = l_List_appendTR___redArg(v___x_1952_, v_eqs_1947_);
                if v_isShared_1951_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1950_, 2, v___x_1953_);
                    crate::leanh::lean_ctor_set(v___x_1950_, 0, v_mvarId_1943_);
                    v___x_1955_ = v___x_1950_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1959_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1959_, 0, v_mvarId_1943_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1959_, 1, v_xs_1946_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1959_, 2, v___x_1953_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1959_, 3, v_eqsNew_1948_);
                    v___x_1955_ = v_reuseFailAlloc_1959_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_1956_ = lean_st_ref_set(v___y_1927_, v___x_1955_);
                v___x_1957_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v___y_1931_);
                crate::leanh::lean_inc_ref(v___y_1930_);
                crate::leanh::lean_inc(v___y_1929_);
                crate::leanh::lean_inc_ref(v___y_1928_);
                crate::leanh::lean_inc(v___y_1927_);
                v___x_1958_ = crate::leanh::lean_apply_7(
                    v___f_1885_,
                    v___x_1957_,
                    v___y_1927_,
                    v___y_1928_,
                    v___y_1929_,
                    v___y_1930_,
                    v___y_1931_,
                    crate::leanh::lean_box(0),
                );
                return v___x_1958_;
            }
            11 => {
                if v_isShared_1972_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1971_, 2, v_tail_1895_);
                    v___x_1974_ = v___x_1971_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2131_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2131_, 0, v_mvarId_1967_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2131_, 1, v_xs_1968_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2131_, 2, v_tail_1895_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2131_, 3, v_eqsNew_1969_);
                    v___x_1974_ = v_reuseFailAlloc_2131_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_1975_ = lean_st_ref_set(v___y_1888_, v___x_1974_);
                crate::leanh::lean_inc(v_head_1894_);
                v___x_1976_ = l_Lean_mkFVar(v_head_1894_);
                crate::leanh::lean_inc(v___y_1892_);
                crate::leanh::lean_inc_ref(v___y_1891_);
                crate::leanh::lean_inc(v___y_1890_);
                crate::leanh::lean_inc_ref(v___y_1889_);
                v___x_1977_ = lean_infer_type(
                    v___x_1976_,
                    v___y_1889_,
                    v___y_1890_,
                    v___y_1891_,
                    v___y_1892_,
                );
                if crate::leanh::lean_obj_tag(v___x_1977_) == 0 {
                    v_a_1978_ = crate::leanh::lean_ctor_get(v___x_1977_, 0);
                    crate::leanh::lean_inc_n(v_a_1978_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_1977_, 1);
                    v___x_2050_ = l_Lean_Meta_matchEq_x3f(
                        v_a_1978_,
                        v___y_1889_,
                        v___y_1890_,
                        v___y_1891_,
                        v___y_1892_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2050_) == 0 {
                        v_a_2051_ = crate::leanh::lean_ctor_get(v___x_2050_, 0);
                        crate::leanh::lean_inc(v_a_2051_);
                        crate::leanh::lean_dec_ref_known(v___x_2050_, 1);
                        if crate::leanh::lean_obj_tag(v_a_2051_) == 1 {
                            v_val_2052_ = crate::leanh::lean_ctor_get(v_a_2051_, 0);
                            crate::leanh::lean_inc(v_val_2052_);
                            crate::leanh::lean_dec_ref_known(v_a_2051_, 1);
                            v_snd_2053_ = crate::leanh::lean_ctor_get(v_val_2052_, 1);
                            crate::leanh::lean_inc(v_snd_2053_);
                            crate::leanh::lean_dec(v_val_2052_);
                            v_fst_2054_ = crate::leanh::lean_ctor_get(v_snd_2053_, 0);
                            crate::leanh::lean_inc(v_fst_2054_);
                            v_snd_2055_ = crate::leanh::lean_ctor_get(v_snd_2053_, 1);
                            crate::leanh::lean_inc_n(v_snd_2055_, 2);
                            crate::leanh::lean_dec(v_snd_2053_);
                            v___x_2056_ = l_Lean_Meta_isExprDefEq(
                                v_fst_2054_,
                                v_snd_2055_,
                                v___y_1889_,
                                v___y_1890_,
                                v___y_1891_,
                                v___y_1892_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_2056_) == 0 {
                                v_a_2057_ = crate::leanh::lean_ctor_get(v___x_2056_, 0);
                                crate::leanh::lean_inc(v_a_2057_);
                                crate::leanh::lean_dec_ref_known(v___x_2056_, 1);
                                v___x_2058_ = 1;
                                v___x_2080_ = (crate::leanh::lean_unbox(v_a_2057_) as u8);
                                crate::leanh::lean_dec(v_a_2057_);
                                if v___x_2080_ == 0 {
                                    v___x_2081_ = l_Lean_Expr_isFVar(v_snd_2055_);
                                    if v___x_2081_ == 0 {
                                        v___y_2060_ = v___x_2081_;
                                        state = 26;
                                        continue;
                                    } else {
                                        v___x_2082_ = l_Lean_Expr_fvarId_x21(v_snd_2055_);
                                        v___x_2083_ = l_List_elem___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS_spec__0(v___x_2082_, v_xs_1887_);
                                        crate::leanh::lean_dec(v___x_2082_);
                                        v___y_2060_ = v___x_2083_;
                                        state = 26;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_snd_2055_);
                                    crate::leanh::lean_dec(v_a_1978_);
                                    crate::leanh::lean_del_object(v___x_1897_);
                                    crate::leanh::lean_dec_ref(v___f_1885_);
                                    v___x_2084_ = l_Lean_MVarId_clear(
                                        v_mvarId_1886_,
                                        v_head_1894_,
                                        v___y_1889_,
                                        v___y_1890_,
                                        v___y_1891_,
                                        v___y_1892_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_2084_) == 0 {
                                        v_a_2085_ = crate::leanh::lean_ctor_get(v___x_2084_, 0);
                                        v_isSharedCheck_2106_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_2084_)) as u8;
                                        if v_isSharedCheck_2106_ == 0 {
                                            v___x_2087_ = v___x_2084_;
                                            v_isShared_2088_ = v_isSharedCheck_2106_;
                                            state = 31;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_2085_);
                                            crate::leanh::lean_dec(v___x_2084_);
                                            v___x_2087_ = crate::leanh::lean_box(0);
                                            v_isShared_2088_ = v_isSharedCheck_2106_;
                                            state = 31;
                                            continue;
                                        }
                                    } else {
                                        v_a_2107_ = crate::leanh::lean_ctor_get(v___x_2084_, 0);
                                        v_isSharedCheck_2114_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_2084_)) as u8;
                                        if v_isSharedCheck_2114_ == 0 {
                                            v___x_2109_ = v___x_2084_;
                                            v_isShared_2110_ = v_isSharedCheck_2114_;
                                            state = 35;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_2107_);
                                            crate::leanh::lean_dec(v___x_2084_);
                                            v___x_2109_ = crate::leanh::lean_box(0);
                                            v_isShared_2110_ = v_isSharedCheck_2114_;
                                            state = 35;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_snd_2055_);
                                crate::leanh::lean_dec(v_a_1978_);
                                crate::leanh::lean_del_object(v___x_1897_);
                                crate::leanh::lean_dec(v_head_1894_);
                                crate::leanh::lean_dec(v_mvarId_1886_);
                                crate::leanh::lean_dec_ref(v___f_1885_);
                                return v___x_2056_;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_2051_);
                            v___y_1980_ = v___y_1888_;
                            v___y_1981_ = v___y_1889_;
                            v___y_1982_ = v___y_1890_;
                            v___y_1983_ = v___y_1891_;
                            v___y_1984_ = v___y_1892_;
                            state = 13;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_1978_);
                        crate::leanh::lean_del_object(v___x_1897_);
                        crate::leanh::lean_dec(v_head_1894_);
                        crate::leanh::lean_dec(v_mvarId_1886_);
                        crate::leanh::lean_dec_ref(v___f_1885_);
                        v_a_2115_ = crate::leanh::lean_ctor_get(v___x_2050_, 0);
                        v_isSharedCheck_2122_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2050_)) as u8;
                        if v_isSharedCheck_2122_ == 0 {
                            v___x_2117_ = v___x_2050_;
                            v_isShared_2118_ = v_isSharedCheck_2122_;
                            state = 37;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2115_);
                            crate::leanh::lean_dec(v___x_2050_);
                            v___x_2117_ = crate::leanh::lean_box(0);
                            v_isShared_2118_ = v_isSharedCheck_2122_;
                            state = 37;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1897_);
                    crate::leanh::lean_dec(v_head_1894_);
                    crate::leanh::lean_dec(v_mvarId_1886_);
                    crate::leanh::lean_dec_ref(v___f_1885_);
                    v_a_2123_ = crate::leanh::lean_ctor_get(v___x_1977_, 0);
                    v_isSharedCheck_2130_ = (!crate::leanh::lean_is_exclusive(v___x_1977_)) as u8;
                    if v_isSharedCheck_2130_ == 0 {
                        v___x_2125_ = v___x_1977_;
                        v_isShared_2126_ = v_isSharedCheck_2130_;
                        state = 39;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2123_);
                        crate::leanh::lean_dec(v___x_1977_);
                        v___x_2125_ = crate::leanh::lean_box(0);
                        v_isShared_2126_ = v_isSharedCheck_2130_;
                        state = 39;
                        continue;
                    }
                }
            }
            13 => {
                v___x_1985_ = l_Lean_Meta_matchHEq_x3f(
                    v_a_1978_,
                    v___y_1981_,
                    v___y_1982_,
                    v___y_1983_,
                    v___y_1984_,
                );
                if crate::leanh::lean_obj_tag(v___x_1985_) == 0 {
                    v_a_1986_ = crate::leanh::lean_ctor_get(v___x_1985_, 0);
                    crate::leanh::lean_inc(v_a_1986_);
                    crate::leanh::lean_dec_ref_known(v___x_1985_, 1);
                    if crate::leanh::lean_obj_tag(v_a_1986_) == 1 {
                        crate::leanh::lean_dec_ref_known(v_a_1986_, 1);
                        v___x_1987_ = 1;
                        crate::leanh::lean_inc(v_head_1894_);
                        crate::leanh::lean_inc(v_mvarId_1886_);
                        v___x_1988_ = l_Lean_Meta_heqToEq(
                            v_mvarId_1886_,
                            v_head_1894_,
                            v___x_1987_,
                            v___y_1981_,
                            v___y_1982_,
                            v___y_1983_,
                            v___y_1984_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1988_) == 0 {
                            v_a_1989_ = crate::leanh::lean_ctor_get(v___x_1988_, 0);
                            v_isSharedCheck_2033_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1988_)) as u8;
                            if v_isSharedCheck_2033_ == 0 {
                                v___x_1991_ = v___x_1988_;
                                v_isShared_1992_ = v_isSharedCheck_2033_;
                                state = 14;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1989_);
                                crate::leanh::lean_dec(v___x_1988_);
                                v___x_1991_ = crate::leanh::lean_box(0);
                                v_isShared_1992_ = v_isSharedCheck_2033_;
                                state = 14;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_1897_);
                            crate::leanh::lean_dec(v_head_1894_);
                            crate::leanh::lean_dec(v_mvarId_1886_);
                            crate::leanh::lean_dec_ref(v___f_1885_);
                            v_a_2034_ = crate::leanh::lean_ctor_get(v___x_1988_, 0);
                            v_isSharedCheck_2041_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1988_)) as u8;
                            if v_isSharedCheck_2041_ == 0 {
                                v___x_2036_ = v___x_1988_;
                                v_isShared_2037_ = v_isSharedCheck_2041_;
                                state = 22;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2034_);
                                crate::leanh::lean_dec(v___x_1988_);
                                v___x_2036_ = crate::leanh::lean_box(0);
                                v_isShared_2037_ = v_isSharedCheck_2041_;
                                state = 22;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_1986_);
                        v___y_1927_ = v___y_1980_;
                        v___y_1928_ = v___y_1981_;
                        v___y_1929_ = v___y_1982_;
                        v___y_1930_ = v___y_1983_;
                        v___y_1931_ = v___y_1984_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1897_);
                    crate::leanh::lean_dec(v_head_1894_);
                    crate::leanh::lean_dec(v_mvarId_1886_);
                    crate::leanh::lean_dec_ref(v___f_1885_);
                    v_a_2042_ = crate::leanh::lean_ctor_get(v___x_1985_, 0);
                    v_isSharedCheck_2049_ = (!crate::leanh::lean_is_exclusive(v___x_1985_)) as u8;
                    if v_isSharedCheck_2049_ == 0 {
                        v___x_2044_ = v___x_1985_;
                        v_isShared_2045_ = v_isSharedCheck_2049_;
                        state = 24;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2042_);
                        crate::leanh::lean_dec(v___x_1985_);
                        v___x_2044_ = crate::leanh::lean_box(0);
                        v_isShared_2045_ = v_isSharedCheck_2049_;
                        state = 24;
                        continue;
                    }
                }
            }
            14 => {
                v_fst_1993_ = crate::leanh::lean_ctor_get(v_a_1989_, 0);
                v_snd_1994_ = crate::leanh::lean_ctor_get(v_a_1989_, 1);
                v_isSharedCheck_2032_ = (!crate::leanh::lean_is_exclusive(v_a_1989_)) as u8;
                if v_isSharedCheck_2032_ == 0 {
                    v___x_1996_ = v_a_1989_;
                    v_isShared_1997_ = v_isSharedCheck_2032_;
                    state = 15;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1994_);
                    crate::leanh::lean_inc(v_fst_1993_);
                    crate::leanh::lean_dec(v_a_1989_);
                    v___x_1996_ = crate::leanh::lean_box(0);
                    v_isShared_1997_ = v_isSharedCheck_2032_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v___x_1998_ = l_Lean_instBEqMVarId_beq(v_snd_1994_, v_mvarId_1886_);
                if v___x_1998_ == 0 {
                    crate::leanh::lean_del_object(v___x_1897_);
                    crate::leanh::lean_dec(v_head_1894_);
                    crate::leanh::lean_dec(v_mvarId_1886_);
                    crate::leanh::lean_dec_ref(v___f_1885_);
                    v___x_1999_ = lean_st_ref_take(v___y_1980_);
                    v_xs_2000_ = crate::leanh::lean_ctor_get(v___x_1999_, 1);
                    v_eqs_2001_ = crate::leanh::lean_ctor_get(v___x_1999_, 2);
                    v_eqsNew_2002_ = crate::leanh::lean_ctor_get(v___x_1999_, 3);
                    v_isSharedCheck_2017_ = (!crate::leanh::lean_is_exclusive(v___x_1999_)) as u8;
                    if v_isSharedCheck_2017_ == 0 {
                        v_unused_2018_ = crate::leanh::lean_ctor_get(v___x_1999_, 0);
                        crate::leanh::lean_dec(v_unused_2018_);
                        v___x_2004_ = v___x_1999_;
                        v_isShared_2005_ = v_isSharedCheck_2017_;
                        state = 16;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_eqsNew_2002_);
                        crate::leanh::lean_inc(v_eqs_2001_);
                        crate::leanh::lean_inc(v_xs_2000_);
                        crate::leanh::lean_dec(v___x_1999_);
                        v___x_2004_ = crate::leanh::lean_box(0);
                        v_isShared_2005_ = v_isSharedCheck_2017_;
                        state = 16;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1996_);
                    crate::leanh::lean_dec(v_snd_1994_);
                    crate::leanh::lean_dec(v_fst_1993_);
                    crate::leanh::lean_del_object(v___x_1991_);
                    v___x_2019_ = crate::leanh::lean_box(1);
                    crate::leanh::lean_inc(v_mvarId_1886_);
                    v___x_2020_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_trySubstVarsAndContradiction(v_mvarId_1886_, v___x_2019_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_);
                    if crate::leanh::lean_obj_tag(v___x_2020_) == 0 {
                        v_a_2021_ = crate::leanh::lean_ctor_get(v___x_2020_, 0);
                        v_isSharedCheck_2031_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2020_)) as u8;
                        if v_isSharedCheck_2031_ == 0 {
                            v___x_2023_ = v___x_2020_;
                            v_isShared_2024_ = v_isSharedCheck_2031_;
                            state = 20;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2021_);
                            crate::leanh::lean_dec(v___x_2020_);
                            v___x_2023_ = crate::leanh::lean_box(0);
                            v_isShared_2024_ = v_isSharedCheck_2031_;
                            state = 20;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_1897_);
                        crate::leanh::lean_dec(v_head_1894_);
                        crate::leanh::lean_dec(v_mvarId_1886_);
                        crate::leanh::lean_dec_ref(v___f_1885_);
                        return v___x_2020_;
                    }
                }
            }
            16 => {
                if v_isShared_1997_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1996_, 1);
                    crate::leanh::lean_ctor_set(v___x_1996_, 1, v_eqs_2001_);
                    v___x_2007_ = v___x_1996_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_2016_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2016_, 0, v_fst_1993_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2016_, 1, v_eqs_2001_);
                    v___x_2007_ = v_reuseFailAlloc_2016_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                if v_isShared_2005_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2004_, 2, v___x_2007_);
                    crate::leanh::lean_ctor_set(v___x_2004_, 0, v_snd_1994_);
                    v___x_2009_ = v___x_2004_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2015_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2015_, 0, v_snd_1994_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2015_, 1, v_xs_2000_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2015_, 2, v___x_2007_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2015_, 3, v_eqsNew_2002_);
                    v___x_2009_ = v_reuseFailAlloc_2015_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                v___x_2010_ = lean_st_ref_set(v___y_1980_, v___x_2009_);
                v___x_2011_ = crate::leanh::lean_box((v___x_1987_) as usize);
                if v_isShared_1992_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1991_, 0, v___x_2011_);
                    v___x_2013_ = v___x_1991_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_2014_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2014_, 0, v___x_2011_);
                    v___x_2013_ = v_reuseFailAlloc_2014_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_2013_;
            }
            20 => {
                v___x_2025_ = (crate::leanh::lean_unbox(v_a_2021_) as u8);
                crate::leanh::lean_dec(v_a_2021_);
                if v___x_2025_ == 0 {
                    crate::leanh::lean_del_object(v___x_2023_);
                    v___y_1927_ = v___y_1980_;
                    v___y_1928_ = v___y_1981_;
                    v___y_1929_ = v___y_1982_;
                    v___y_1930_ = v___y_1983_;
                    v___y_1931_ = v___y_1984_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_del_object(v___x_1897_);
                    crate::leanh::lean_dec(v_head_1894_);
                    crate::leanh::lean_dec(v_mvarId_1886_);
                    crate::leanh::lean_dec_ref(v___f_1885_);
                    v___x_2026_ = 0;
                    v___x_2027_ = crate::leanh::lean_box((v___x_2026_) as usize);
                    if v_isShared_2024_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2023_, 0, v___x_2027_);
                        v___x_2029_ = v___x_2023_;
                        state = 21;
                        continue;
                    } else {
                        v_reuseFailAlloc_2030_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2030_, 0, v___x_2027_);
                        v___x_2029_ = v_reuseFailAlloc_2030_;
                        state = 21;
                        continue;
                    }
                }
            }
            21 => {
                return v___x_2029_;
            }
            22 => {
                if v_isShared_2037_ == 0 {
                    v___x_2039_ = v___x_2036_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_2040_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2040_, 0, v_a_2034_);
                    v___x_2039_ = v_reuseFailAlloc_2040_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_2039_;
            }
            24 => {
                if v_isShared_2045_ == 0 {
                    v___x_2047_ = v___x_2044_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_2048_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2048_, 0, v_a_2042_);
                    v___x_2047_ = v_reuseFailAlloc_2048_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_2047_;
            }
            26 => {
                if v___y_2060_ == 0 {
                    crate::leanh::lean_dec(v_snd_2055_);
                    v___y_1980_ = v___y_1888_;
                    v___y_1981_ = v___y_1889_;
                    v___y_1982_ = v___y_1890_;
                    v___y_1983_ = v___y_1891_;
                    v___y_1984_ = v___y_1892_;
                    state = 13;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_a_1978_);
                    crate::leanh::lean_del_object(v___x_1897_);
                    crate::leanh::lean_dec(v_mvarId_1886_);
                    crate::leanh::lean_dec_ref(v___f_1885_);
                    v___x_2061_ = l_Lean_Expr_fvarId_x21(v_snd_2055_);
                    crate::leanh::lean_dec(v_snd_2055_);
                    v___x_2062_ =
                        l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_substRHS(
                            v_head_1894_,
                            v___x_2061_,
                            v___y_1888_,
                            v___y_1889_,
                            v___y_1890_,
                            v___y_1891_,
                            v___y_1892_,
                        );
                    crate::leanh::lean_dec(v___x_2061_);
                    if crate::leanh::lean_obj_tag(v___x_2062_) == 0 {
                        v_isSharedCheck_2070_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2062_)) as u8;
                        if v_isSharedCheck_2070_ == 0 {
                            v_unused_2071_ = crate::leanh::lean_ctor_get(v___x_2062_, 0);
                            crate::leanh::lean_dec(v_unused_2071_);
                            v___x_2064_ = v___x_2062_;
                            v_isShared_2065_ = v_isSharedCheck_2070_;
                            state = 27;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_2062_);
                            v___x_2064_ = crate::leanh::lean_box(0);
                            v_isShared_2065_ = v_isSharedCheck_2070_;
                            state = 27;
                            continue;
                        }
                    } else {
                        v_a_2072_ = crate::leanh::lean_ctor_get(v___x_2062_, 0);
                        v_isSharedCheck_2079_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2062_)) as u8;
                        if v_isSharedCheck_2079_ == 0 {
                            v___x_2074_ = v___x_2062_;
                            v_isShared_2075_ = v_isSharedCheck_2079_;
                            state = 29;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2072_);
                            crate::leanh::lean_dec(v___x_2062_);
                            v___x_2074_ = crate::leanh::lean_box(0);
                            v_isShared_2075_ = v_isSharedCheck_2079_;
                            state = 29;
                            continue;
                        }
                    }
                }
            }
            27 => {
                v___x_2066_ = crate::leanh::lean_box((v___x_2058_) as usize);
                if v_isShared_2065_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2064_, 0, v___x_2066_);
                    v___x_2068_ = v___x_2064_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_2069_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2069_, 0, v___x_2066_);
                    v___x_2068_ = v_reuseFailAlloc_2069_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_2068_;
            }
            29 => {
                if v_isShared_2075_ == 0 {
                    v___x_2077_ = v___x_2074_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_2078_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_a_2072_);
                    v___x_2077_ = v_reuseFailAlloc_2078_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_2077_;
            }
            31 => {
                v___x_2089_ = lean_st_ref_take(v___y_1888_);
                v_xs_2090_ = crate::leanh::lean_ctor_get(v___x_2089_, 1);
                v_eqs_2091_ = crate::leanh::lean_ctor_get(v___x_2089_, 2);
                v_eqsNew_2092_ = crate::leanh::lean_ctor_get(v___x_2089_, 3);
                v_isSharedCheck_2104_ = (!crate::leanh::lean_is_exclusive(v___x_2089_)) as u8;
                if v_isSharedCheck_2104_ == 0 {
                    v_unused_2105_ = crate::leanh::lean_ctor_get(v___x_2089_, 0);
                    crate::leanh::lean_dec(v_unused_2105_);
                    v___x_2094_ = v___x_2089_;
                    v_isShared_2095_ = v_isSharedCheck_2104_;
                    state = 32;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_eqsNew_2092_);
                    crate::leanh::lean_inc(v_eqs_2091_);
                    crate::leanh::lean_inc(v_xs_2090_);
                    crate::leanh::lean_dec(v___x_2089_);
                    v___x_2094_ = crate::leanh::lean_box(0);
                    v_isShared_2095_ = v_isSharedCheck_2104_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_2095_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2094_, 0, v_a_2085_);
                    v___x_2097_ = v___x_2094_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_2103_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2103_, 0, v_a_2085_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2103_, 1, v_xs_2090_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2103_, 2, v_eqs_2091_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2103_, 3, v_eqsNew_2092_);
                    v___x_2097_ = v_reuseFailAlloc_2103_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                v___x_2098_ = lean_st_ref_set(v___y_1888_, v___x_2097_);
                v___x_2099_ = crate::leanh::lean_box((v___x_2058_) as usize);
                if v_isShared_2088_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2087_, 0, v___x_2099_);
                    v___x_2101_ = v___x_2087_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_2102_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2102_, 0, v___x_2099_);
                    v___x_2101_ = v_reuseFailAlloc_2102_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                return v___x_2101_;
            }
            35 => {
                if v_isShared_2110_ == 0 {
                    v___x_2112_ = v___x_2109_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_2113_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2113_, 0, v_a_2107_);
                    v___x_2112_ = v_reuseFailAlloc_2113_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                return v___x_2112_;
            }
            37 => {
                if v_isShared_2118_ == 0 {
                    v___x_2120_ = v___x_2117_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_2121_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2121_, 0, v_a_2115_);
                    v___x_2120_ = v_reuseFailAlloc_2121_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_2120_;
            }
            39 => {
                if v_isShared_2126_ == 0 {
                    v___x_2128_ = v___x_2125_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_2129_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2129_, 0, v_a_2123_);
                    v___x_2128_ = v_reuseFailAlloc_2129_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                return v___x_2128_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___lam__1___boxed(
    mut v_eqs_2137_: *mut crate::leanh::LeanObject,
    mut v___f_2138_: *mut crate::leanh::LeanObject,
    mut v_mvarId_2139_: *mut crate::leanh::LeanObject,
    mut v_xs_2140_: *mut crate::leanh::LeanObject,
    mut v___y_2141_: *mut crate::leanh::LeanObject,
    mut v___y_2142_: *mut crate::leanh::LeanObject,
    mut v___y_2143_: *mut crate::leanh::LeanObject,
    mut v___y_2144_: *mut crate::leanh::LeanObject,
    mut v___y_2145_: *mut crate::leanh::LeanObject,
    mut v___y_2146_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2147_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___lam__1(
        v_eqs_2137_,
        v___f_2138_,
        v_mvarId_2139_,
        v_xs_2140_,
        v___y_2141_,
        v___y_2142_,
        v___y_2143_,
        v___y_2144_,
        v___y_2145_,
    );
    crate::leanh::lean_dec(v___y_2145_);
    crate::leanh::lean_dec_ref(v___y_2144_);
    crate::leanh::lean_dec(v___y_2143_);
    crate::leanh::lean_dec_ref(v___y_2142_);
    crate::leanh::lean_dec(v___y_2141_);
    crate::leanh::lean_dec(v_xs_2140_);
    return v_res_2147_;
}
pub unsafe fn l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq(
    mut v_a_2149_: *mut crate::leanh::LeanObject,
    mut v_a_2150_: *mut crate::leanh::LeanObject,
    mut v_a_2151_: *mut crate::leanh::LeanObject,
    mut v_a_2152_: *mut crate::leanh::LeanObject,
    mut v_a_2153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eqs_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2155_ = lean_st_ref_get(v_a_2149_);
    v_mvarId_2156_ = crate::leanh::lean_ctor_get(v___x_2155_, 0);
    crate::leanh::lean_inc_n(v_mvarId_2156_, 2);
    v_xs_2157_ = crate::leanh::lean_ctor_get(v___x_2155_, 1);
    crate::leanh::lean_inc(v_xs_2157_);
    v_eqs_2158_ = crate::leanh::lean_ctor_get(v___x_2155_, 2);
    crate::leanh::lean_inc(v_eqs_2158_);
    crate::leanh::lean_dec(v___x_2155_);
    v___f_2159_ =
        l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___closed__0;
    v___y_2160_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___lam__1___boxed
            as *mut core::ffi::c_void,
        10,
        4,
    );
    crate::leanh::lean_closure_set(v___y_2160_, 0, v_eqs_2158_);
    crate::leanh::lean_closure_set(v___y_2160_, 1, v___f_2159_);
    crate::leanh::lean_closure_set(v___y_2160_, 2, v_mvarId_2156_);
    crate::leanh::lean_closure_set(v___y_2160_, 3, v_xs_2157_);
    v___x_2161_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq_spec__0___redArg(v_mvarId_2156_, v___y_2160_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_, v_a_2153_);
    return v___x_2161_;
}
pub unsafe fn l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq___boxed(
    mut v_a_2162_: *mut crate::leanh::LeanObject,
    mut v_a_2163_: *mut crate::leanh::LeanObject,
    mut v_a_2164_: *mut crate::leanh::LeanObject,
    mut v_a_2165_: *mut crate::leanh::LeanObject,
    mut v_a_2166_: *mut crate::leanh::LeanObject,
    mut v_a_2167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2168_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq(
        v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_,
    );
    crate::leanh::lean_dec(v_a_2166_);
    crate::leanh::lean_dec_ref(v_a_2165_);
    crate::leanh::lean_dec(v_a_2164_);
    crate::leanh::lean_dec_ref(v_a_2163_);
    crate::leanh::lean_dec(v_a_2162_);
    return v_res_2168_;
}
pub unsafe fn l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_go(
    mut v_a_2169_: *mut crate::leanh::LeanObject,
    mut v_a_2170_: *mut crate::leanh::LeanObject,
    mut v_a_2171_: *mut crate::leanh::LeanObject,
    mut v_a_2172_: *mut crate::leanh::LeanObject,
    mut v_a_2173_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: u8 = 0;
    let mut v___x_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2175_ =
                    l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_isDone___redArg(
                        v_a_2169_,
                    );
                if crate::leanh::lean_obj_tag(v___x_2175_) == 0 {
                    v_a_2176_ = crate::leanh::lean_ctor_get(v___x_2175_, 0);
                    crate::leanh::lean_inc(v_a_2176_);
                    v___x_2177_ = (crate::leanh::lean_unbox(v_a_2176_) as u8);
                    crate::leanh::lean_dec(v_a_2176_);
                    if v___x_2177_ == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2175_, 1);
                        v___x_2178_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_processNextEq(v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_, v_a_2173_);
                        if crate::leanh::lean_obj_tag(v___x_2178_) == 0 {
                            v_a_2179_ = crate::leanh::lean_ctor_get(v___x_2178_, 0);
                            crate::leanh::lean_inc(v_a_2179_);
                            v___x_2180_ = (crate::leanh::lean_unbox(v_a_2179_) as u8);
                            crate::leanh::lean_dec(v_a_2179_);
                            if v___x_2180_ == 0 {
                                return v___x_2178_;
                            } else {
                                crate::leanh::lean_dec_ref_known(v___x_2178_, 1);
                                state = 0;
                                continue;
                            }
                        } else {
                            return v___x_2178_;
                        }
                    } else {
                        return v___x_2175_;
                    }
                } else {
                    return v___x_2175_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_go___boxed(
    mut v_a_2182_: *mut crate::leanh::LeanObject,
    mut v_a_2183_: *mut crate::leanh::LeanObject,
    mut v_a_2184_: *mut crate::leanh::LeanObject,
    mut v_a_2185_: *mut crate::leanh::LeanObject,
    mut v_a_2186_: *mut crate::leanh::LeanObject,
    mut v_a_2187_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2188_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_go(
        v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_,
    );
    crate::leanh::lean_dec(v_a_2186_);
    crate::leanh::lean_dec_ref(v_a_2185_);
    crate::leanh::lean_dec(v_a_2184_);
    crate::leanh::lean_dec_ref(v_a_2183_);
    crate::leanh::lean_dec(v_a_2182_);
    return v_res_2188_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0___redArg___lam__0(
    mut v_k_2189_: *mut crate::leanh::LeanObject,
    mut v_b_2190_: *mut crate::leanh::LeanObject,
    mut v_c_2191_: *mut crate::leanh::LeanObject,
    mut v___y_2192_: *mut crate::leanh::LeanObject,
    mut v___y_2193_: *mut crate::leanh::LeanObject,
    mut v___y_2194_: *mut crate::leanh::LeanObject,
    mut v___y_2195_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_2195_);
    crate::leanh::lean_inc_ref(v___y_2194_);
    crate::leanh::lean_inc(v___y_2193_);
    crate::leanh::lean_inc_ref(v___y_2192_);
    v___x_2197_ = crate::leanh::lean_apply_7(
        v_k_2189_,
        v_b_2190_,
        v_c_2191_,
        v___y_2192_,
        v___y_2193_,
        v___y_2194_,
        v___y_2195_,
        crate::leanh::lean_box(0),
    );
    return v___x_2197_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0___redArg___lam__0___boxed(
    mut v_k_2198_: *mut crate::leanh::LeanObject,
    mut v_b_2199_: *mut crate::leanh::LeanObject,
    mut v_c_2200_: *mut crate::leanh::LeanObject,
    mut v___y_2201_: *mut crate::leanh::LeanObject,
    mut v___y_2202_: *mut crate::leanh::LeanObject,
    mut v___y_2203_: *mut crate::leanh::LeanObject,
    mut v___y_2204_: *mut crate::leanh::LeanObject,
    mut v___y_2205_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2206_ =
        l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0___redArg___lam__0(
            v_k_2198_,
            v_b_2199_,
            v_c_2200_,
            v___y_2201_,
            v___y_2202_,
            v___y_2203_,
            v___y_2204_,
        );
    crate::leanh::lean_dec(v___y_2204_);
    crate::leanh::lean_dec_ref(v___y_2203_);
    crate::leanh::lean_dec(v___y_2202_);
    crate::leanh::lean_dec_ref(v___y_2201_);
    return v_res_2206_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0___redArg(
    mut v_type_2207_: *mut crate::leanh::LeanObject,
    mut v_k_2208_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_2209_: u8,
    mut v___y_2210_: *mut crate::leanh::LeanObject,
    mut v___y_2211_: *mut crate::leanh::LeanObject,
    mut v___y_2212_: *mut crate::leanh::LeanObject,
    mut v___y_2213_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: u8 = 0;
    let mut v___x_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2222_: u8 = 0;
    let mut v___x_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2226_: u8 = 0;
    let mut v_a_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2230_: u8 = 0;
    let mut v___x_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2234_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_2215_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                crate::leanh::lean_closure_set(v___f_2215_, 0, v_k_2208_);
                v___x_2216_ = 0;
                v___x_2217_ = crate::leanh::lean_box(0);
                v___x_2218_ =
                    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(
                        crate::leanh::lean_box(0),
                        v___x_2216_,
                        v___x_2217_,
                        v_type_2207_,
                        v___f_2215_,
                        v_cleanupAnnotations_2209_,
                        v___x_2216_,
                        v___y_2210_,
                        v___y_2211_,
                        v___y_2212_,
                        v___y_2213_,
                    );
                if crate::leanh::lean_obj_tag(v___x_2218_) == 0 {
                    v_a_2219_ = crate::leanh::lean_ctor_get(v___x_2218_, 0);
                    v_isSharedCheck_2226_ = (!crate::leanh::lean_is_exclusive(v___x_2218_)) as u8;
                    if v_isSharedCheck_2226_ == 0 {
                        v___x_2221_ = v___x_2218_;
                        v_isShared_2222_ = v_isSharedCheck_2226_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2219_);
                        crate::leanh::lean_dec(v___x_2218_);
                        v___x_2221_ = crate::leanh::lean_box(0);
                        v_isShared_2222_ = v_isSharedCheck_2226_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2227_ = crate::leanh::lean_ctor_get(v___x_2218_, 0);
                    v_isSharedCheck_2234_ = (!crate::leanh::lean_is_exclusive(v___x_2218_)) as u8;
                    if v_isSharedCheck_2234_ == 0 {
                        v___x_2229_ = v___x_2218_;
                        v_isShared_2230_ = v_isSharedCheck_2234_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2227_);
                        crate::leanh::lean_dec(v___x_2218_);
                        v___x_2229_ = crate::leanh::lean_box(0);
                        v_isShared_2230_ = v_isSharedCheck_2234_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2222_ == 0 {
                    v___x_2224_ = v___x_2221_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2225_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2225_, 0, v_a_2219_);
                    v___x_2224_ = v_reuseFailAlloc_2225_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2224_;
            }
            3 => {
                if v_isShared_2230_ == 0 {
                    v___x_2232_ = v___x_2229_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2233_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2233_, 0, v_a_2227_);
                    v___x_2232_ = v_reuseFailAlloc_2233_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2232_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0___redArg___boxed(
    mut v_type_2235_: *mut crate::leanh::LeanObject,
    mut v_k_2236_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_2237_: *mut crate::leanh::LeanObject,
    mut v___y_2238_: *mut crate::leanh::LeanObject,
    mut v___y_2239_: *mut crate::leanh::LeanObject,
    mut v___y_2240_: *mut crate::leanh::LeanObject,
    mut v___y_2241_: *mut crate::leanh::LeanObject,
    mut v___y_2242_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_2243_: u8 = 0;
    let mut v_res_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_2243_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_2237_) as u8);
    v_res_2244_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0___redArg(
        v_type_2235_,
        v_k_2236_,
        v_cleanupAnnotations_boxed_2243_,
        v___y_2238_,
        v___y_2239_,
        v___y_2240_,
        v___y_2241_,
    );
    crate::leanh::lean_dec(v___y_2241_);
    crate::leanh::lean_dec_ref(v___y_2240_);
    crate::leanh::lean_dec(v___y_2239_);
    crate::leanh::lean_dec_ref(v___y_2238_);
    return v_res_2244_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0(
    mut v_00_u03b1_2245_: *mut crate::leanh::LeanObject,
    mut v_type_2246_: *mut crate::leanh::LeanObject,
    mut v_k_2247_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_2248_: u8,
    mut v___y_2249_: *mut crate::leanh::LeanObject,
    mut v___y_2250_: *mut crate::leanh::LeanObject,
    mut v___y_2251_: *mut crate::leanh::LeanObject,
    mut v___y_2252_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2254_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0___redArg(
        v_type_2246_,
        v_k_2247_,
        v_cleanupAnnotations_2248_,
        v___y_2249_,
        v___y_2250_,
        v___y_2251_,
        v___y_2252_,
    );
    return v___x_2254_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0___boxed(
    mut v_00_u03b1_2255_: *mut crate::leanh::LeanObject,
    mut v_type_2256_: *mut crate::leanh::LeanObject,
    mut v_k_2257_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_2258_: *mut crate::leanh::LeanObject,
    mut v___y_2259_: *mut crate::leanh::LeanObject,
    mut v___y_2260_: *mut crate::leanh::LeanObject,
    mut v___y_2261_: *mut crate::leanh::LeanObject,
    mut v___y_2262_: *mut crate::leanh::LeanObject,
    mut v___y_2263_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_2264_: u8 = 0;
    let mut v_res_2265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_2264_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_2258_) as u8);
    v_res_2265_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0(
        v_00_u03b1_2255_,
        v_type_2256_,
        v_k_2257_,
        v_cleanupAnnotations_boxed_2264_,
        v___y_2259_,
        v___y_2260_,
        v___y_2261_,
        v___y_2262_,
    );
    crate::leanh::lean_dec(v___y_2262_);
    crate::leanh::lean_dec_ref(v___y_2261_);
    crate::leanh::lean_dec(v___y_2260_);
    crate::leanh::lean_dec_ref(v___y_2259_);
    return v_res_2265_;
}
pub unsafe fn l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___lam__0(
    mut v_x_2266_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2267_: u8 = 0;
    v___x_2267_ = 0;
    return v___x_2267_;
}
pub unsafe fn l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___lam__0___boxed(
    mut v_x_2268_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2269_: u8 = 0;
    let mut v_r_2270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2269_ =
        l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___lam__0(v_x_2268_);
    crate::leanh::lean_dec(v_x_2268_);
    v_r_2270_ = crate::leanh::lean_box((v_res_2269_) as usize);
    return v_r_2270_;
}
pub unsafe fn l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___lam__1(
    mut v_fvarId_2271_: *mut crate::leanh::LeanObject,
    mut v_x_2272_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2273_: u8 = 0;
    v___x_2273_ = l_Lean_instBEqFVarId_beq(v_fvarId_2271_, v_x_2272_);
    return v___x_2273_;
}
pub unsafe fn l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___lam__1___boxed(
    mut v_fvarId_2274_: *mut crate::leanh::LeanObject,
    mut v_x_2275_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2276_: u8 = 0;
    let mut v_r_2277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2276_ = l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___lam__1(
        v_fvarId_2274_,
        v_x_2275_,
    );
    crate::leanh::lean_dec(v_x_2275_);
    crate::leanh::lean_dec(v_fvarId_2274_);
    v_r_2277_ = crate::leanh::lean_box((v_res_2276_) as usize);
    return v_r_2277_;
}
pub unsafe fn _init_l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2279_ = crate::leanh::lean_box(0);
    v___x_2280_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_2281_ = lean_mk_array(v___x_2280_, v___x_2279_);
    return v___x_2281_;
}
pub unsafe fn _init_l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2282_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___closed__1_once
        ),
        _init_l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___closed__1,
    );
    v___x_2283_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2284_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2284_, 0, v___x_2283_);
    crate::leanh::lean_ctor_set(v___x_2284_, 1, v___x_2282_);
    return v___x_2284_;
}
pub unsafe fn l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg(
    mut v_e_2285_: *mut crate::leanh::LeanObject,
    mut v_fvarId_2286_: *mut crate::leanh::LeanObject,
    mut v___y_2287_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2291_: u8 = 0;
    let mut v_mctx_2292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2300_: u8 = 0;
    let mut v___x_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2307_: u8 = 0;
    let mut v_unused_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: u8 = 0;
    let mut v_mctx_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: u8 = 0;
    let mut v___x_2321_: u8 = 0;
    let mut v___x_2322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2289_ = lean_st_ref_get(v___y_2287_);
                v_mctx_2315_ = crate::leanh::lean_ctor_get(v___x_2289_, 0);
                crate::leanh::lean_inc_ref_n(v_mctx_2315_, 2);
                crate::leanh::lean_dec(v___x_2289_);
                v___f_2316_ = l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___closed__0;
                v___f_2317_ = crate::leanh::lean_alloc_closure(l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___lam__1___boxed as *mut core::ffi::c_void, 2, 1);
                crate::leanh::lean_closure_set(v___f_2317_, 0, v_fvarId_2286_);
                v___x_2318_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___closed__2_once), _init_l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___closed__2);
                v___x_2319_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2319_, 0, v___x_2318_);
                crate::leanh::lean_ctor_set(v___x_2319_, 1, v_mctx_2315_);
                v___x_2320_ = l_Lean_Expr_hasFVar(v_e_2285_);
                if v___x_2320_ == 0 {
                    v___x_2321_ = l_Lean_Expr_hasMVar(v_e_2285_);
                    if v___x_2321_ == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2319_, 2);
                        crate::leanh::lean_dec_ref(v___f_2317_);
                        crate::leanh::lean_dec_ref(v_e_2285_);
                        v_fst_2291_ = v___x_2321_;
                        v_mctx_2292_ = v_mctx_2315_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_mctx_2315_);
                        v___x_2322_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(
                            v___f_2317_,
                            v___f_2316_,
                            v_e_2285_,
                            v___x_2319_,
                        );
                        v___y_2310_ = v___x_2322_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_mctx_2315_);
                    v___x_2323_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(
                        v___f_2317_,
                        v___f_2316_,
                        v_e_2285_,
                        v___x_2319_,
                    );
                    v___y_2310_ = v___x_2323_;
                    state = 4;
                    continue;
                }
            }
            1 => {
                v___x_2293_ = lean_st_ref_take(v___y_2287_);
                v_cache_2294_ = crate::leanh::lean_ctor_get(v___x_2293_, 1);
                v_zetaDeltaFVarIds_2295_ = crate::leanh::lean_ctor_get(v___x_2293_, 2);
                v_postponed_2296_ = crate::leanh::lean_ctor_get(v___x_2293_, 3);
                v_diag_2297_ = crate::leanh::lean_ctor_get(v___x_2293_, 4);
                v_isSharedCheck_2307_ = (!crate::leanh::lean_is_exclusive(v___x_2293_)) as u8;
                if v_isSharedCheck_2307_ == 0 {
                    v_unused_2308_ = crate::leanh::lean_ctor_get(v___x_2293_, 0);
                    crate::leanh::lean_dec(v_unused_2308_);
                    v___x_2299_ = v___x_2293_;
                    v_isShared_2300_ = v_isSharedCheck_2307_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_2297_);
                    crate::leanh::lean_inc(v_postponed_2296_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_2295_);
                    crate::leanh::lean_inc(v_cache_2294_);
                    crate::leanh::lean_dec(v___x_2293_);
                    v___x_2299_ = crate::leanh::lean_box(0);
                    v_isShared_2300_ = v_isSharedCheck_2307_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_2300_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2299_, 0, v_mctx_2292_);
                    v___x_2302_ = v___x_2299_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2306_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2306_, 0, v_mctx_2292_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2306_, 1, v_cache_2294_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2306_,
                        2,
                        v_zetaDeltaFVarIds_2295_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2306_, 3, v_postponed_2296_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2306_, 4, v_diag_2297_);
                    v___x_2302_ = v_reuseFailAlloc_2306_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2303_ = lean_st_ref_set(v___y_2287_, v___x_2302_);
                v___x_2304_ = crate::leanh::lean_box((v_fst_2291_) as usize);
                v___x_2305_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2305_, 0, v___x_2304_);
                return v___x_2305_;
            }
            4 => {
                v_snd_2311_ = crate::leanh::lean_ctor_get(v___y_2310_, 1);
                crate::leanh::lean_inc(v_snd_2311_);
                v_fst_2312_ = crate::leanh::lean_ctor_get(v___y_2310_, 0);
                crate::leanh::lean_inc(v_fst_2312_);
                crate::leanh::lean_dec_ref(v___y_2310_);
                v_mctx_2313_ = crate::leanh::lean_ctor_get(v_snd_2311_, 1);
                crate::leanh::lean_inc_ref(v_mctx_2313_);
                crate::leanh::lean_dec(v_snd_2311_);
                v___x_2314_ = (crate::leanh::lean_unbox(v_fst_2312_) as u8);
                crate::leanh::lean_dec(v_fst_2312_);
                v_fst_2291_ = v___x_2314_;
                v_mctx_2292_ = v_mctx_2313_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg___boxed(
    mut v_e_2324_: *mut crate::leanh::LeanObject,
    mut v_fvarId_2325_: *mut crate::leanh::LeanObject,
    mut v___y_2326_: *mut crate::leanh::LeanObject,
    mut v___y_2327_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2328_ = l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg(
        v_e_2324_,
        v_fvarId_2325_,
        v___y_2326_,
    );
    crate::leanh::lean_dec(v___y_2326_);
    return v_res_2328_;
}
pub unsafe fn l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1(
    mut v_e_2329_: *mut crate::leanh::LeanObject,
    mut v_fvarId_2330_: *mut crate::leanh::LeanObject,
    mut v___y_2331_: *mut crate::leanh::LeanObject,
    mut v___y_2332_: *mut crate::leanh::LeanObject,
    mut v___y_2333_: *mut crate::leanh::LeanObject,
    mut v___y_2334_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2336_ = l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg(
        v_e_2329_,
        v_fvarId_2330_,
        v___y_2332_,
    );
    return v___x_2336_;
}
pub unsafe fn l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___boxed(
    mut v_e_2337_: *mut crate::leanh::LeanObject,
    mut v_fvarId_2338_: *mut crate::leanh::LeanObject,
    mut v___y_2339_: *mut crate::leanh::LeanObject,
    mut v___y_2340_: *mut crate::leanh::LeanObject,
    mut v___y_2341_: *mut crate::leanh::LeanObject,
    mut v___y_2342_: *mut crate::leanh::LeanObject,
    mut v___y_2343_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2344_ = l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1(
        v_e_2337_,
        v_fvarId_2338_,
        v___y_2339_,
        v___y_2340_,
        v___y_2341_,
        v___y_2342_,
    );
    crate::leanh::lean_dec(v___y_2342_);
    crate::leanh::lean_dec_ref(v___y_2341_);
    crate::leanh::lean_dec(v___y_2340_);
    crate::leanh::lean_dec_ref(v___y_2339_);
    return v_res_2344_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Match_simpH_spec__3___redArg(
    mut v_mvarId_2345_: *mut crate::leanh::LeanObject,
    mut v_x_2346_: *mut crate::leanh::LeanObject,
    mut v___y_2347_: *mut crate::leanh::LeanObject,
    mut v___y_2348_: *mut crate::leanh::LeanObject,
    mut v___y_2349_: *mut crate::leanh::LeanObject,
    mut v___y_2350_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2356_: u8 = 0;
    let mut v___x_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2360_: u8 = 0;
    let mut v_a_2361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2364_: u8 = 0;
    let mut v___x_2366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2368_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2352_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    crate::leanh::lean_box(0),
                    v_mvarId_2345_,
                    v_x_2346_,
                    v___y_2347_,
                    v___y_2348_,
                    v___y_2349_,
                    v___y_2350_,
                );
                if crate::leanh::lean_obj_tag(v___x_2352_) == 0 {
                    v_a_2353_ = crate::leanh::lean_ctor_get(v___x_2352_, 0);
                    v_isSharedCheck_2360_ = (!crate::leanh::lean_is_exclusive(v___x_2352_)) as u8;
                    if v_isSharedCheck_2360_ == 0 {
                        v___x_2355_ = v___x_2352_;
                        v_isShared_2356_ = v_isSharedCheck_2360_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2353_);
                        crate::leanh::lean_dec(v___x_2352_);
                        v___x_2355_ = crate::leanh::lean_box(0);
                        v_isShared_2356_ = v_isSharedCheck_2360_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2361_ = crate::leanh::lean_ctor_get(v___x_2352_, 0);
                    v_isSharedCheck_2368_ = (!crate::leanh::lean_is_exclusive(v___x_2352_)) as u8;
                    if v_isSharedCheck_2368_ == 0 {
                        v___x_2363_ = v___x_2352_;
                        v_isShared_2364_ = v_isSharedCheck_2368_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2361_);
                        crate::leanh::lean_dec(v___x_2352_);
                        v___x_2363_ = crate::leanh::lean_box(0);
                        v_isShared_2364_ = v_isSharedCheck_2368_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2356_ == 0 {
                    v___x_2358_ = v___x_2355_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2359_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2359_, 0, v_a_2353_);
                    v___x_2358_ = v_reuseFailAlloc_2359_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2358_;
            }
            3 => {
                if v_isShared_2364_ == 0 {
                    v___x_2366_ = v___x_2363_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2367_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2367_, 0, v_a_2361_);
                    v___x_2366_ = v_reuseFailAlloc_2367_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2366_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Match_simpH_spec__3___redArg___boxed(
    mut v_mvarId_2369_: *mut crate::leanh::LeanObject,
    mut v_x_2370_: *mut crate::leanh::LeanObject,
    mut v___y_2371_: *mut crate::leanh::LeanObject,
    mut v___y_2372_: *mut crate::leanh::LeanObject,
    mut v___y_2373_: *mut crate::leanh::LeanObject,
    mut v___y_2374_: *mut crate::leanh::LeanObject,
    mut v___y_2375_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2376_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Match_simpH_spec__3___redArg(
        v_mvarId_2369_,
        v_x_2370_,
        v___y_2371_,
        v___y_2372_,
        v___y_2373_,
        v___y_2374_,
    );
    crate::leanh::lean_dec(v___y_2374_);
    crate::leanh::lean_dec_ref(v___y_2373_);
    crate::leanh::lean_dec(v___y_2372_);
    crate::leanh::lean_dec_ref(v___y_2371_);
    return v_res_2376_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Match_simpH_spec__3(
    mut v_00_u03b1_2377_: *mut crate::leanh::LeanObject,
    mut v_mvarId_2378_: *mut crate::leanh::LeanObject,
    mut v_x_2379_: *mut crate::leanh::LeanObject,
    mut v___y_2380_: *mut crate::leanh::LeanObject,
    mut v___y_2381_: *mut crate::leanh::LeanObject,
    mut v___y_2382_: *mut crate::leanh::LeanObject,
    mut v___y_2383_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2385_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Match_simpH_spec__3___redArg(
        v_mvarId_2378_,
        v_x_2379_,
        v___y_2380_,
        v___y_2381_,
        v___y_2382_,
        v___y_2383_,
    );
    return v___x_2385_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Match_simpH_spec__3___boxed(
    mut v_00_u03b1_2386_: *mut crate::leanh::LeanObject,
    mut v_mvarId_2387_: *mut crate::leanh::LeanObject,
    mut v_x_2388_: *mut crate::leanh::LeanObject,
    mut v___y_2389_: *mut crate::leanh::LeanObject,
    mut v___y_2390_: *mut crate::leanh::LeanObject,
    mut v___y_2391_: *mut crate::leanh::LeanObject,
    mut v___y_2392_: *mut crate::leanh::LeanObject,
    mut v___y_2393_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2394_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Match_simpH_spec__3(
        v_00_u03b1_2386_,
        v_mvarId_2387_,
        v_x_2388_,
        v___y_2389_,
        v___y_2390_,
        v___y_2391_,
        v___y_2392_,
    );
    crate::leanh::lean_dec(v___y_2392_);
    crate::leanh::lean_dec_ref(v___y_2391_);
    crate::leanh::lean_dec(v___y_2390_);
    crate::leanh::lean_dec_ref(v___y_2389_);
    return v_res_2394_;
}
pub unsafe fn l_Lean_Meta_Match_simpH___lam__0(
    mut v_numEqs_2395_: *mut crate::leanh::LeanObject,
    mut v_ys_2396_: *mut crate::leanh::LeanObject,
    mut v_x_2397_: *mut crate::leanh::LeanObject,
    mut v___y_2398_: *mut crate::leanh::LeanObject,
    mut v___y_2399_: *mut crate::leanh::LeanObject,
    mut v___y_2400_: *mut crate::leanh::LeanObject,
    mut v___y_2401_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2403_ = lean_array_get_size(v_ys_2396_);
    v___x_2404_ = lean_nat_sub(v___x_2403_, v_numEqs_2395_);
    v___x_2405_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2405_, 0, v___x_2404_);
    return v___x_2405_;
}
pub unsafe fn l_Lean_Meta_Match_simpH___lam__0___boxed(
    mut v_numEqs_2406_: *mut crate::leanh::LeanObject,
    mut v_ys_2407_: *mut crate::leanh::LeanObject,
    mut v_x_2408_: *mut crate::leanh::LeanObject,
    mut v___y_2409_: *mut crate::leanh::LeanObject,
    mut v___y_2410_: *mut crate::leanh::LeanObject,
    mut v___y_2411_: *mut crate::leanh::LeanObject,
    mut v___y_2412_: *mut crate::leanh::LeanObject,
    mut v___y_2413_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2414_ = l_Lean_Meta_Match_simpH___lam__0(
        v_numEqs_2406_,
        v_ys_2407_,
        v_x_2408_,
        v___y_2409_,
        v___y_2410_,
        v___y_2411_,
        v___y_2412_,
    );
    crate::leanh::lean_dec(v___y_2412_);
    crate::leanh::lean_dec_ref(v___y_2411_);
    crate::leanh::lean_dec(v___y_2410_);
    crate::leanh::lean_dec_ref(v___y_2409_);
    crate::leanh::lean_dec_ref(v_x_2408_);
    crate::leanh::lean_dec_ref(v_ys_2407_);
    crate::leanh::lean_dec(v_numEqs_2406_);
    return v_res_2414_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Match_simpH_spec__2(
    mut v_a_2415_: *mut crate::leanh::LeanObject,
    mut v_as_2416_: *mut crate::leanh::LeanObject,
    mut v_i_2417_: usize,
    mut v_stop_2418_: usize,
    mut v_b_2419_: *mut crate::leanh::LeanObject,
    mut v___y_2420_: *mut crate::leanh::LeanObject,
    mut v___y_2421_: *mut crate::leanh::LeanObject,
    mut v___y_2422_: *mut crate::leanh::LeanObject,
    mut v___y_2423_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2425_: u8 = 0;
    let mut v___x_2426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: usize = 0;
    let mut v___x_2432_: usize = 0;
    let mut v___x_2434_: u8 = 0;
    let mut v___x_2435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2439_: u8 = 0;
    let mut v___x_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2443_: u8 = 0;
    let mut v___x_2444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2425_ = lean_usize_dec_eq(v_i_2417_, v_stop_2418_);
                if v___x_2425_ == 0 {
                    v___x_2426_ = lean_array_uget_borrowed(v_as_2416_, v_i_2417_);
                    crate::leanh::lean_inc(v___x_2426_);
                    crate::leanh::lean_inc_ref(v_a_2415_);
                    v___x_2427_ =
                        l_Lean_exprDependsOn___at___00Lean_Meta_Match_simpH_spec__1___redArg(
                            v_a_2415_,
                            v___x_2426_,
                            v___y_2421_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_2427_) == 0 {
                        v_a_2428_ = crate::leanh::lean_ctor_get(v___x_2427_, 0);
                        crate::leanh::lean_inc(v_a_2428_);
                        crate::leanh::lean_dec_ref_known(v___x_2427_, 1);
                        v___x_2434_ = (crate::leanh::lean_unbox(v_a_2428_) as u8);
                        crate::leanh::lean_dec(v_a_2428_);
                        if v___x_2434_ == 0 {
                            v_a_2430_ = v_b_2419_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v___x_2426_);
                            v___x_2435_ = lean_array_push(v_b_2419_, v___x_2426_);
                            v_a_2430_ = v___x_2435_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_b_2419_);
                        crate::leanh::lean_dec_ref(v_a_2415_);
                        v_a_2436_ = crate::leanh::lean_ctor_get(v___x_2427_, 0);
                        v_isSharedCheck_2443_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2427_)) as u8;
                        if v_isSharedCheck_2443_ == 0 {
                            v___x_2438_ = v___x_2427_;
                            v_isShared_2439_ = v_isSharedCheck_2443_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2436_);
                            crate::leanh::lean_dec(v___x_2427_);
                            v___x_2438_ = crate::leanh::lean_box(0);
                            v_isShared_2439_ = v_isSharedCheck_2443_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_a_2415_);
                    v___x_2444_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2444_, 0, v_b_2419_);
                    return v___x_2444_;
                }
            }
            1 => {
                v___x_2431_ = 1usize;
                v___x_2432_ = lean_usize_add(v_i_2417_, v___x_2431_);
                v_i_2417_ = v___x_2432_;
                v_b_2419_ = v_a_2430_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_2439_ == 0 {
                    v___x_2441_ = v___x_2438_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2442_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2442_, 0, v_a_2436_);
                    v___x_2441_ = v_reuseFailAlloc_2442_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2441_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Match_simpH_spec__2___boxed(
    mut v_a_2445_: *mut crate::leanh::LeanObject,
    mut v_as_2446_: *mut crate::leanh::LeanObject,
    mut v_i_2447_: *mut crate::leanh::LeanObject,
    mut v_stop_2448_: *mut crate::leanh::LeanObject,
    mut v_b_2449_: *mut crate::leanh::LeanObject,
    mut v___y_2450_: *mut crate::leanh::LeanObject,
    mut v___y_2451_: *mut crate::leanh::LeanObject,
    mut v___y_2452_: *mut crate::leanh::LeanObject,
    mut v___y_2453_: *mut crate::leanh::LeanObject,
    mut v___y_2454_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2455_: usize = 0;
    let mut v_stop_boxed_2456_: usize = 0;
    let mut v_res_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2455_ = crate::leanh::lean_unbox_usize(v_i_2447_);
    crate::leanh::lean_dec(v_i_2447_);
    v_stop_boxed_2456_ = crate::leanh::lean_unbox_usize(v_stop_2448_);
    crate::leanh::lean_dec(v_stop_2448_);
    v_res_2457_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Match_simpH_spec__2(v_a_2445_, v_as_2446_, v_i_boxed_2455_, v_stop_boxed_2456_, v_b_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_);
    crate::leanh::lean_dec(v___y_2453_);
    crate::leanh::lean_dec_ref(v___y_2452_);
    crate::leanh::lean_dec(v___y_2451_);
    crate::leanh::lean_dec_ref(v___y_2450_);
    crate::leanh::lean_dec_ref(v_as_2446_);
    return v_res_2457_;
}
pub unsafe fn l_Lean_Meta_Match_simpH___lam__1(
    mut v_snd_2458_: *mut crate::leanh::LeanObject,
    mut v___x_2459_: u8,
    mut v___x_2460_: *mut crate::leanh::LeanObject,
    mut v___x_2461_: *mut crate::leanh::LeanObject,
    mut v_a_2462_: *mut crate::leanh::LeanObject,
    mut v___x_2463_: *mut crate::leanh::LeanObject,
    mut v___y_2464_: *mut crate::leanh::LeanObject,
    mut v___y_2465_: *mut crate::leanh::LeanObject,
    mut v___y_2466_: *mut crate::leanh::LeanObject,
    mut v___y_2467_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2475_: u8 = 0;
    let mut v_snd_2476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2481_: u8 = 0;
    let mut v_a_2482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2485_: u8 = 0;
    let mut v___x_2487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2489_: u8 = 0;
    let mut v___y_2491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2496_: u8 = 0;
    let mut v___x_2498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2500_: u8 = 0;
    let mut v___x_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2502_: u8 = 0;
    let mut v___x_2503_: u8 = 0;
    let mut v___x_2504_: usize = 0;
    let mut v___x_2505_: usize = 0;
    let mut v___x_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: usize = 0;
    let mut v___x_2508_: usize = 0;
    let mut v___x_2509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2501_ = lean_mk_empty_array_with_capacity(v___x_2460_);
                v___x_2502_ = lean_nat_dec_lt(v___x_2460_, v___x_2461_);
                if v___x_2502_ == 0 {
                    crate::leanh::lean_dec_ref(v_a_2462_);
                    v_a_2470_ = v___x_2501_;
                    state = 1;
                    continue;
                } else {
                    v___x_2503_ = lean_nat_dec_le(v___x_2461_, v___x_2461_);
                    if v___x_2503_ == 0 {
                        if v___x_2502_ == 0 {
                            crate::leanh::lean_dec_ref(v_a_2462_);
                            v_a_2470_ = v___x_2501_;
                            state = 1;
                            continue;
                        } else {
                            v___x_2504_ = 0usize;
                            v___x_2505_ = lean_usize_of_nat(v___x_2461_);
                            v___x_2506_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Match_simpH_spec__2(v_a_2462_, v___x_2463_, v___x_2504_, v___x_2505_, v___x_2501_, v___y_2464_, v___y_2465_, v___y_2466_, v___y_2467_);
                            v___y_2491_ = v___x_2506_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v___x_2507_ = 0usize;
                        v___x_2508_ = lean_usize_of_nat(v___x_2461_);
                        v___x_2509_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Match_simpH_spec__2(v_a_2462_, v___x_2463_, v___x_2507_, v___x_2508_, v___x_2501_, v___y_2464_, v___y_2465_, v___y_2466_, v___y_2467_);
                        v___y_2491_ = v___x_2509_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2471_ = l_Lean_MVarId_revert(
                    v_snd_2458_,
                    v_a_2470_,
                    v___x_2459_,
                    v___x_2459_,
                    v___y_2464_,
                    v___y_2465_,
                    v___y_2466_,
                    v___y_2467_,
                );
                if crate::leanh::lean_obj_tag(v___x_2471_) == 0 {
                    v_a_2472_ = crate::leanh::lean_ctor_get(v___x_2471_, 0);
                    v_isSharedCheck_2481_ = (!crate::leanh::lean_is_exclusive(v___x_2471_)) as u8;
                    if v_isSharedCheck_2481_ == 0 {
                        v___x_2474_ = v___x_2471_;
                        v_isShared_2475_ = v_isSharedCheck_2481_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2472_);
                        crate::leanh::lean_dec(v___x_2471_);
                        v___x_2474_ = crate::leanh::lean_box(0);
                        v_isShared_2475_ = v_isSharedCheck_2481_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_2482_ = crate::leanh::lean_ctor_get(v___x_2471_, 0);
                    v_isSharedCheck_2489_ = (!crate::leanh::lean_is_exclusive(v___x_2471_)) as u8;
                    if v_isSharedCheck_2489_ == 0 {
                        v___x_2484_ = v___x_2471_;
                        v_isShared_2485_ = v_isSharedCheck_2489_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2482_);
                        crate::leanh::lean_dec(v___x_2471_);
                        v___x_2484_ = crate::leanh::lean_box(0);
                        v_isShared_2485_ = v_isSharedCheck_2489_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v_snd_2476_ = crate::leanh::lean_ctor_get(v_a_2472_, 1);
                crate::leanh::lean_inc(v_snd_2476_);
                crate::leanh::lean_dec(v_a_2472_);
                v___x_2477_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2477_, 0, v_snd_2476_);
                if v_isShared_2475_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2474_, 0, v___x_2477_);
                    v___x_2479_ = v___x_2474_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2480_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2480_, 0, v___x_2477_);
                    v___x_2479_ = v_reuseFailAlloc_2480_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2479_;
            }
            4 => {
                if v_isShared_2485_ == 0 {
                    v___x_2487_ = v___x_2484_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2488_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2488_, 0, v_a_2482_);
                    v___x_2487_ = v_reuseFailAlloc_2488_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2487_;
            }
            6 => {
                if crate::leanh::lean_obj_tag(v___y_2491_) == 0 {
                    v_a_2492_ = crate::leanh::lean_ctor_get(v___y_2491_, 0);
                    crate::leanh::lean_inc(v_a_2492_);
                    crate::leanh::lean_dec_ref_known(v___y_2491_, 1);
                    v_a_2470_ = v_a_2492_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_snd_2458_);
                    v_a_2493_ = crate::leanh::lean_ctor_get(v___y_2491_, 0);
                    v_isSharedCheck_2500_ = (!crate::leanh::lean_is_exclusive(v___y_2491_)) as u8;
                    if v_isSharedCheck_2500_ == 0 {
                        v___x_2495_ = v___y_2491_;
                        v_isShared_2496_ = v_isSharedCheck_2500_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2493_);
                        crate::leanh::lean_dec(v___y_2491_);
                        v___x_2495_ = crate::leanh::lean_box(0);
                        v_isShared_2496_ = v_isSharedCheck_2500_;
                        state = 7;
                        continue;
                    }
                }
            }
            7 => {
                if v_isShared_2496_ == 0 {
                    v___x_2498_ = v___x_2495_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2499_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2499_, 0, v_a_2493_);
                    v___x_2498_ = v_reuseFailAlloc_2499_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2498_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Match_simpH___lam__1___boxed(
    mut v_snd_2510_: *mut crate::leanh::LeanObject,
    mut v___x_2511_: *mut crate::leanh::LeanObject,
    mut v___x_2512_: *mut crate::leanh::LeanObject,
    mut v___x_2513_: *mut crate::leanh::LeanObject,
    mut v_a_2514_: *mut crate::leanh::LeanObject,
    mut v___x_2515_: *mut crate::leanh::LeanObject,
    mut v___y_2516_: *mut crate::leanh::LeanObject,
    mut v___y_2517_: *mut crate::leanh::LeanObject,
    mut v___y_2518_: *mut crate::leanh::LeanObject,
    mut v___y_2519_: *mut crate::leanh::LeanObject,
    mut v___y_2520_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6866__boxed_2521_: u8 = 0;
    let mut v_res_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6866__boxed_2521_ = (crate::leanh::lean_unbox(v___x_2511_) as u8);
    v_res_2522_ = l_Lean_Meta_Match_simpH___lam__1(
        v_snd_2510_,
        v___x_6866__boxed_2521_,
        v___x_2512_,
        v___x_2513_,
        v_a_2514_,
        v___x_2515_,
        v___y_2516_,
        v___y_2517_,
        v___y_2518_,
        v___y_2519_,
    );
    crate::leanh::lean_dec(v___y_2519_);
    crate::leanh::lean_dec_ref(v___y_2518_);
    crate::leanh::lean_dec(v___y_2517_);
    crate::leanh::lean_dec_ref(v___y_2516_);
    crate::leanh::lean_dec_ref(v___x_2515_);
    crate::leanh::lean_dec(v___x_2513_);
    crate::leanh::lean_dec(v___x_2512_);
    return v_res_2522_;
}
pub unsafe fn l_Lean_Meta_Match_simpH___lam__2(
    mut v_mvarId_2523_: *mut crate::leanh::LeanObject,
    mut v___x_2524_: *mut crate::leanh::LeanObject,
    mut v___x_2525_: u8,
    mut v_xs_2526_: *mut crate::leanh::LeanObject,
    mut v___y_2527_: *mut crate::leanh::LeanObject,
    mut v___y_2528_: *mut crate::leanh::LeanObject,
    mut v___y_2529_: *mut crate::leanh::LeanObject,
    mut v___y_2530_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2547_: u8 = 0;
    let mut v___x_2549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2551_: u8 = 0;
    let mut v_a_2552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2555_: u8 = 0;
    let mut v___x_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2559_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2532_ = l_Lean_MVarId_revert(
                    v_mvarId_2523_,
                    v___x_2524_,
                    v___x_2525_,
                    v___x_2525_,
                    v___y_2527_,
                    v___y_2528_,
                    v___y_2529_,
                    v___y_2530_,
                );
                if crate::leanh::lean_obj_tag(v___x_2532_) == 0 {
                    v_a_2533_ = crate::leanh::lean_ctor_get(v___x_2532_, 0);
                    crate::leanh::lean_inc(v_a_2533_);
                    crate::leanh::lean_dec_ref_known(v___x_2532_, 1);
                    v_snd_2534_ = crate::leanh::lean_ctor_get(v_a_2533_, 1);
                    crate::leanh::lean_inc_n(v_snd_2534_, 2);
                    crate::leanh::lean_dec(v_a_2533_);
                    v___x_2535_ = l_Lean_MVarId_getType(
                        v_snd_2534_,
                        v___y_2527_,
                        v___y_2528_,
                        v___y_2529_,
                        v___y_2530_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2535_) == 0 {
                        v_a_2536_ = crate::leanh::lean_ctor_get(v___x_2535_, 0);
                        crate::leanh::lean_inc(v_a_2536_);
                        crate::leanh::lean_dec_ref_known(v___x_2535_, 1);
                        v___x_2537_ = lean_array_mk(v_xs_2526_);
                        v___x_2538_ = l_Array_reverse___redArg(v___x_2537_);
                        v___x_2539_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_2540_ = lean_array_get_size(v___x_2538_);
                        v___x_2541_ = crate::leanh::lean_box((v___x_2525_) as usize);
                        crate::leanh::lean_inc(v_snd_2534_);
                        v___f_2542_ = crate::leanh::lean_alloc_closure(
                            l_Lean_Meta_Match_simpH___lam__1___boxed as *mut core::ffi::c_void,
                            11,
                            6,
                        );
                        crate::leanh::lean_closure_set(v___f_2542_, 0, v_snd_2534_);
                        crate::leanh::lean_closure_set(v___f_2542_, 1, v___x_2541_);
                        crate::leanh::lean_closure_set(v___f_2542_, 2, v___x_2539_);
                        crate::leanh::lean_closure_set(v___f_2542_, 3, v___x_2540_);
                        crate::leanh::lean_closure_set(v___f_2542_, 4, v_a_2536_);
                        crate::leanh::lean_closure_set(v___f_2542_, 5, v___x_2538_);
                        v___x_2543_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Match_simpH_spec__3___redArg(v_snd_2534_, v___f_2542_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_);
                        return v___x_2543_;
                    } else {
                        crate::leanh::lean_dec(v_snd_2534_);
                        crate::leanh::lean_dec(v_xs_2526_);
                        v_a_2544_ = crate::leanh::lean_ctor_get(v___x_2535_, 0);
                        v_isSharedCheck_2551_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2535_)) as u8;
                        if v_isSharedCheck_2551_ == 0 {
                            v___x_2546_ = v___x_2535_;
                            v_isShared_2547_ = v_isSharedCheck_2551_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2544_);
                            crate::leanh::lean_dec(v___x_2535_);
                            v___x_2546_ = crate::leanh::lean_box(0);
                            v_isShared_2547_ = v_isSharedCheck_2551_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_xs_2526_);
                    v_a_2552_ = crate::leanh::lean_ctor_get(v___x_2532_, 0);
                    v_isSharedCheck_2559_ = (!crate::leanh::lean_is_exclusive(v___x_2532_)) as u8;
                    if v_isSharedCheck_2559_ == 0 {
                        v___x_2554_ = v___x_2532_;
                        v_isShared_2555_ = v_isSharedCheck_2559_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2552_);
                        crate::leanh::lean_dec(v___x_2532_);
                        v___x_2554_ = crate::leanh::lean_box(0);
                        v_isShared_2555_ = v_isSharedCheck_2559_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2547_ == 0 {
                    v___x_2549_ = v___x_2546_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2550_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2550_, 0, v_a_2544_);
                    v___x_2549_ = v_reuseFailAlloc_2550_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2549_;
            }
            3 => {
                if v_isShared_2555_ == 0 {
                    v___x_2557_ = v___x_2554_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2558_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2558_, 0, v_a_2552_);
                    v___x_2557_ = v_reuseFailAlloc_2558_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2557_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Match_simpH___lam__2___boxed(
    mut v_mvarId_2560_: *mut crate::leanh::LeanObject,
    mut v___x_2561_: *mut crate::leanh::LeanObject,
    mut v___x_2562_: *mut crate::leanh::LeanObject,
    mut v_xs_2563_: *mut crate::leanh::LeanObject,
    mut v___y_2564_: *mut crate::leanh::LeanObject,
    mut v___y_2565_: *mut crate::leanh::LeanObject,
    mut v___y_2566_: *mut crate::leanh::LeanObject,
    mut v___y_2567_: *mut crate::leanh::LeanObject,
    mut v___y_2568_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6977__boxed_2569_: u8 = 0;
    let mut v_res_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6977__boxed_2569_ = (crate::leanh::lean_unbox(v___x_2562_) as u8);
    v_res_2570_ = l_Lean_Meta_Match_simpH___lam__2(
        v_mvarId_2560_,
        v___x_2561_,
        v___x_6977__boxed_2569_,
        v_xs_2563_,
        v___y_2564_,
        v___y_2565_,
        v___y_2566_,
        v___y_2567_,
    );
    crate::leanh::lean_dec(v___y_2567_);
    crate::leanh::lean_dec_ref(v___y_2566_);
    crate::leanh::lean_dec(v___y_2565_);
    crate::leanh::lean_dec_ref(v___y_2564_);
    return v_res_2570_;
}
pub unsafe fn _init_l_Lean_Meta_Match_simpH___closed__0() -> u64 {
    let mut v___x_2571_: u8 = 0;
    let mut v___x_2572_: u64 = 0;
    v___x_2571_ = 1;
    v___x_2572_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_2571_);
    return v___x_2572_;
}
pub unsafe fn l_Lean_Meta_Match_simpH(
    mut v_mvarId_2573_: *mut crate::leanh::LeanObject,
    mut v_numEqs_2574_: *mut crate::leanh::LeanObject,
    mut v_a_2575_: *mut crate::leanh::LeanObject,
    mut v_a_2576_: *mut crate::leanh::LeanObject,
    mut v_a_2577_: *mut crate::leanh::LeanObject,
    mut v_a_2578_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_foApprox_2581_: u8 = 0;
    let mut v_ctxApprox_2582_: u8 = 0;
    let mut v_quasiPatternApprox_2583_: u8 = 0;
    let mut v_constApprox_2584_: u8 = 0;
    let mut v_isDefEqStuckEx_2585_: u8 = 0;
    let mut v_unificationHints_2586_: u8 = 0;
    let mut v_proofIrrelevance_2587_: u8 = 0;
    let mut v_assignSyntheticOpaque_2588_: u8 = 0;
    let mut v_offsetCnstrs_2589_: u8 = 0;
    let mut v_etaStruct_2590_: u8 = 0;
    let mut v_univApprox_2591_: u8 = 0;
    let mut v_iota_2592_: u8 = 0;
    let mut v_beta_2593_: u8 = 0;
    let mut v_proj_2594_: u8 = 0;
    let mut v_zeta_2595_: u8 = 0;
    let mut v_zetaDelta_2596_: u8 = 0;
    let mut v_zetaUnused_2597_: u8 = 0;
    let mut v_zetaHave_2598_: u8 = 0;
    let mut v___x_2600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2601_: u8 = 0;
    let mut v_trackZetaDelta_2602_: u8 = 0;
    let mut v_zetaDeltaSet_2603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_2605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_2606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_2607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_2608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_2609_: u8 = 0;
    let mut v_inTypeClassResolution_2610_: u8 = 0;
    let mut v_cacheInferType_2611_: u8 = 0;
    let mut v___x_2612_: u8 = 0;
    let mut v_config_2614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2615_: u64 = 0;
    let mut v___x_2616_: u64 = 0;
    let mut v___x_2617_: u64 = 0;
    let mut v___x_2618_: u64 = 0;
    let mut v___x_2619_: u64 = 0;
    let mut v_key_2620_: u64 = 0;
    let mut v___x_2621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2626_: u8 = 0;
    let mut v___x_2627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2649_: u8 = 0;
    let mut v___x_2650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2651_: u8 = 0;
    let mut v___x_2652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_2656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_2657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eqsNew_2658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2664_: u8 = 0;
    let mut v_a_2665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2668_: u8 = 0;
    let mut v___x_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2672_: u8 = 0;
    let mut v_a_2673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2676_: u8 = 0;
    let mut v___x_2678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2680_: u8 = 0;
    let mut v_a_2681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2684_: u8 = 0;
    let mut v___x_2686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2688_: u8 = 0;
    let mut v_a_2689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2692_: u8 = 0;
    let mut v___x_2694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2696_: u8 = 0;
    let mut v_a_2697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2700_: u8 = 0;
    let mut v___x_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2704_: u8 = 0;
    let mut v_a_2705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2708_: u8 = 0;
    let mut v___x_2710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2712_: u8 = 0;
    let mut v_reuseFailAlloc_2713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2714_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2580_ = l_Lean_Meta_Context_config(v_a_2575_);
                v_foApprox_2581_ = crate::leanh::lean_ctor_get_uint8(v___x_2580_, 0 as u32);
                v_ctxApprox_2582_ = crate::leanh::lean_ctor_get_uint8(v___x_2580_, 1 as u32);
                v_quasiPatternApprox_2583_ =
                    crate::leanh::lean_ctor_get_uint8(v___x_2580_, 2 as u32);
                v_constApprox_2584_ = crate::leanh::lean_ctor_get_uint8(v___x_2580_, 3 as u32);
                v_isDefEqStuckEx_2585_ = crate::leanh::lean_ctor_get_uint8(v___x_2580_, 4 as u32);
                v_unificationHints_2586_ = crate::leanh::lean_ctor_get_uint8(v___x_2580_, 5 as u32);
                v_proofIrrelevance_2587_ = crate::leanh::lean_ctor_get_uint8(v___x_2580_, 6 as u32);
                v_assignSyntheticOpaque_2588_ =
                    crate::leanh::lean_ctor_get_uint8(v___x_2580_, 7 as u32);
                v_offsetCnstrs_2589_ = crate::leanh::lean_ctor_get_uint8(v___x_2580_, 8 as u32);
                v_etaStruct_2590_ = crate::leanh::lean_ctor_get_uint8(v___x_2580_, 10 as u32);
                v_univApprox_2591_ = crate::leanh::lean_ctor_get_uint8(v___x_2580_, 11 as u32);
                v_iota_2592_ = crate::leanh::lean_ctor_get_uint8(v___x_2580_, 12 as u32);
                v_beta_2593_ = crate::leanh::lean_ctor_get_uint8(v___x_2580_, 13 as u32);
                v_proj_2594_ = crate::leanh::lean_ctor_get_uint8(v___x_2580_, 14 as u32);
                v_zeta_2595_ = crate::leanh::lean_ctor_get_uint8(v___x_2580_, 15 as u32);
                v_zetaDelta_2596_ = crate::leanh::lean_ctor_get_uint8(v___x_2580_, 16 as u32);
                v_zetaUnused_2597_ = crate::leanh::lean_ctor_get_uint8(v___x_2580_, 17 as u32);
                v_zetaHave_2598_ = crate::leanh::lean_ctor_get_uint8(v___x_2580_, 18 as u32);
                v_isSharedCheck_2714_ = (!crate::leanh::lean_is_exclusive(v___x_2580_)) as u8;
                if v_isSharedCheck_2714_ == 0 {
                    v___x_2600_ = v___x_2580_;
                    v_isShared_2601_ = v_isSharedCheck_2714_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_2580_);
                    v___x_2600_ = crate::leanh::lean_box(0);
                    v_isShared_2601_ = v_isSharedCheck_2714_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_trackZetaDelta_2602_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_2575_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_2603_ = crate::leanh::lean_ctor_get(v_a_2575_, 1);
                v_lctx_2604_ = crate::leanh::lean_ctor_get(v_a_2575_, 2);
                v_localInstances_2605_ = crate::leanh::lean_ctor_get(v_a_2575_, 3);
                v_defEqCtx_x3f_2606_ = crate::leanh::lean_ctor_get(v_a_2575_, 4);
                v_synthPendingDepth_2607_ = crate::leanh::lean_ctor_get(v_a_2575_, 5);
                v_canUnfold_x3f_2608_ = crate::leanh::lean_ctor_get(v_a_2575_, 6);
                v_univApprox_2609_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_2575_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_2610_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_2575_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_2611_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_2575_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                );
                v___x_2612_ = 1;
                if v_isShared_2601_ == 0 {
                    v_config_2614_ = v___x_2600_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2713_ = crate::leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2713_,
                        0 as u32,
                        v_foApprox_2581_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2713_,
                        1 as u32,
                        v_ctxApprox_2582_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2713_,
                        2 as u32,
                        v_quasiPatternApprox_2583_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2713_,
                        3 as u32,
                        v_constApprox_2584_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2713_,
                        4 as u32,
                        v_isDefEqStuckEx_2585_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2713_,
                        5 as u32,
                        v_unificationHints_2586_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2713_,
                        6 as u32,
                        v_proofIrrelevance_2587_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2713_,
                        7 as u32,
                        v_assignSyntheticOpaque_2588_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2713_,
                        8 as u32,
                        v_offsetCnstrs_2589_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2713_,
                        10 as u32,
                        v_etaStruct_2590_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2713_,
                        11 as u32,
                        v_univApprox_2591_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2713_,
                        12 as u32,
                        v_iota_2592_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2713_,
                        13 as u32,
                        v_beta_2593_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2713_,
                        14 as u32,
                        v_proj_2594_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2713_,
                        15 as u32,
                        v_zeta_2595_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2713_,
                        16 as u32,
                        v_zetaDelta_2596_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2713_,
                        17 as u32,
                        v_zetaUnused_2597_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2713_,
                        18 as u32,
                        v_zetaHave_2598_,
                    );
                    v_config_2614_ = v_reuseFailAlloc_2713_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(v_config_2614_, 9 as u32, v___x_2612_);
                v___x_2615_ = l_Lean_Meta_Context_configKey(v_a_2575_);
                v___x_2616_ = 3u64;
                v___x_2617_ = lean_uint64_shift_right(v___x_2615_, v___x_2616_);
                v___x_2618_ = lean_uint64_shift_left(v___x_2617_, v___x_2616_);
                v___x_2619_ = crate::leanh::lean_uint64_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Match_simpH___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Match_simpH___closed__0_once),
                    _init_l_Lean_Meta_Match_simpH___closed__0,
                );
                v_key_2620_ = lean_uint64_lor(v___x_2618_, v___x_2619_);
                v___x_2621_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                crate::leanh::lean_ctor_set(v___x_2621_, 0, v_config_2614_);
                crate::leanh::lean_ctor_set_uint64(
                    v___x_2621_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_key_2620_,
                );
                crate::leanh::lean_inc(v_canUnfold_x3f_2608_);
                crate::leanh::lean_inc(v_synthPendingDepth_2607_);
                crate::leanh::lean_inc(v_defEqCtx_x3f_2606_);
                crate::leanh::lean_inc_ref(v_localInstances_2605_);
                crate::leanh::lean_inc_ref(v_lctx_2604_);
                crate::leanh::lean_inc(v_zetaDeltaSet_2603_);
                v___x_2622_ = crate::leanh::lean_alloc_ctor(0, 7, (4) as u32);
                crate::leanh::lean_ctor_set(v___x_2622_, 0, v___x_2621_);
                crate::leanh::lean_ctor_set(v___x_2622_, 1, v_zetaDeltaSet_2603_);
                crate::leanh::lean_ctor_set(v___x_2622_, 2, v_lctx_2604_);
                crate::leanh::lean_ctor_set(v___x_2622_, 3, v_localInstances_2605_);
                crate::leanh::lean_ctor_set(v___x_2622_, 4, v_defEqCtx_x3f_2606_);
                crate::leanh::lean_ctor_set(v___x_2622_, 5, v_synthPendingDepth_2607_);
                crate::leanh::lean_ctor_set(v___x_2622_, 6, v_canUnfold_x3f_2608_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2622_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_2602_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2622_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_2609_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2622_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_2610_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2622_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_2611_,
                );
                crate::leanh::lean_inc(v_mvarId_2573_);
                v___x_2623_ = l_Lean_MVarId_getType(
                    v_mvarId_2573_,
                    v___x_2622_,
                    v_a_2576_,
                    v_a_2577_,
                    v_a_2578_,
                );
                if crate::leanh::lean_obj_tag(v___x_2623_) == 0 {
                    v_a_2624_ = crate::leanh::lean_ctor_get(v___x_2623_, 0);
                    crate::leanh::lean_inc(v_a_2624_);
                    crate::leanh::lean_dec_ref_known(v___x_2623_, 1);
                    crate::leanh::lean_inc(v_numEqs_2574_);
                    v___f_2625_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Meta_Match_simpH___lam__0___boxed as *mut core::ffi::c_void,
                        8,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_2625_, 0, v_numEqs_2574_);
                    v___x_2626_ = 0;
                    v___x_2627_ =
                        l_Lean_Meta_forallTelescope___at___00Lean_Meta_Match_simpH_spec__0___redArg(
                            v_a_2624_,
                            v___f_2625_,
                            v___x_2626_,
                            v___x_2622_,
                            v_a_2576_,
                            v_a_2577_,
                            v_a_2578_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_2627_) == 0 {
                        v_a_2628_ = crate::leanh::lean_ctor_get(v___x_2627_, 0);
                        crate::leanh::lean_inc(v_a_2628_);
                        crate::leanh::lean_dec_ref_known(v___x_2627_, 1);
                        v___x_2629_ = l_Lean_LocalContext_getFVarIds(v_lctx_2604_);
                        v___x_2630_ = l_Lean_MVarId_tryClearMany(
                            v_mvarId_2573_,
                            v___x_2629_,
                            v___x_2622_,
                            v_a_2576_,
                            v_a_2577_,
                            v_a_2578_,
                        );
                        crate::leanh::lean_dec_ref(v___x_2629_);
                        if crate::leanh::lean_obj_tag(v___x_2630_) == 0 {
                            v_a_2631_ = crate::leanh::lean_ctor_get(v___x_2630_, 0);
                            crate::leanh::lean_inc(v_a_2631_);
                            crate::leanh::lean_dec_ref_known(v___x_2630_, 1);
                            v___x_2632_ = crate::leanh::lean_box(0);
                            v___x_2633_ = l_Lean_Meta_introNCore(
                                v_a_2631_,
                                v_a_2628_,
                                v___x_2632_,
                                v___x_2626_,
                                v___x_2626_,
                                v___x_2622_,
                                v_a_2576_,
                                v_a_2577_,
                                v_a_2578_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_2633_) == 0 {
                                v_a_2634_ = crate::leanh::lean_ctor_get(v___x_2633_, 0);
                                crate::leanh::lean_inc(v_a_2634_);
                                crate::leanh::lean_dec_ref_known(v___x_2633_, 1);
                                v_fst_2635_ = crate::leanh::lean_ctor_get(v_a_2634_, 0);
                                crate::leanh::lean_inc(v_fst_2635_);
                                v_snd_2636_ = crate::leanh::lean_ctor_get(v_a_2634_, 1);
                                crate::leanh::lean_inc(v_snd_2636_);
                                crate::leanh::lean_dec(v_a_2634_);
                                v___x_2637_ = l_Lean_Meta_introNCore(
                                    v_snd_2636_,
                                    v_numEqs_2574_,
                                    v___x_2632_,
                                    v___x_2626_,
                                    v___x_2626_,
                                    v___x_2622_,
                                    v_a_2576_,
                                    v_a_2577_,
                                    v_a_2578_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_2637_) == 0 {
                                    v_a_2638_ = crate::leanh::lean_ctor_get(v___x_2637_, 0);
                                    crate::leanh::lean_inc(v_a_2638_);
                                    crate::leanh::lean_dec_ref_known(v___x_2637_, 1);
                                    v_fst_2639_ = crate::leanh::lean_ctor_get(v_a_2638_, 0);
                                    crate::leanh::lean_inc(v_fst_2639_);
                                    v_snd_2640_ = crate::leanh::lean_ctor_get(v_a_2638_, 1);
                                    crate::leanh::lean_inc(v_snd_2640_);
                                    crate::leanh::lean_dec(v_a_2638_);
                                    v___x_2641_ = lean_array_to_list(v_fst_2635_);
                                    v___x_2642_ = lean_array_to_list(v_fst_2639_);
                                    v___x_2643_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_2643_, 0, v_snd_2640_);
                                    crate::leanh::lean_ctor_set(v___x_2643_, 1, v___x_2641_);
                                    crate::leanh::lean_ctor_set(v___x_2643_, 2, v___x_2642_);
                                    crate::leanh::lean_ctor_set(v___x_2643_, 3, v___x_2632_);
                                    v___x_2644_ = lean_st_mk_ref(v___x_2643_);
                                    v___x_2645_ = l___private_Lean_Meta_Match_SimpH_0__Lean_Meta_Match_SimpH_go(v___x_2644_, v___x_2622_, v_a_2576_, v_a_2577_, v_a_2578_);
                                    if crate::leanh::lean_obj_tag(v___x_2645_) == 0 {
                                        v_a_2646_ = crate::leanh::lean_ctor_get(v___x_2645_, 0);
                                        v_isSharedCheck_2664_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_2645_)) as u8;
                                        if v_isSharedCheck_2664_ == 0 {
                                            v___x_2648_ = v___x_2645_;
                                            v_isShared_2649_ = v_isSharedCheck_2664_;
                                            state = 3;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_2646_);
                                            crate::leanh::lean_dec(v___x_2645_);
                                            v___x_2648_ = crate::leanh::lean_box(0);
                                            v_isShared_2649_ = v_isSharedCheck_2664_;
                                            state = 3;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v___x_2644_);
                                        crate::leanh::lean_dec_ref_known(v___x_2622_, 7);
                                        v_a_2665_ = crate::leanh::lean_ctor_get(v___x_2645_, 0);
                                        v_isSharedCheck_2672_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_2645_)) as u8;
                                        if v_isSharedCheck_2672_ == 0 {
                                            v___x_2667_ = v___x_2645_;
                                            v_isShared_2668_ = v_isSharedCheck_2672_;
                                            state = 5;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_2665_);
                                            crate::leanh::lean_dec(v___x_2645_);
                                            v___x_2667_ = crate::leanh::lean_box(0);
                                            v_isShared_2668_ = v_isSharedCheck_2672_;
                                            state = 5;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_fst_2635_);
                                    crate::leanh::lean_dec_ref_known(v___x_2622_, 7);
                                    v_a_2673_ = crate::leanh::lean_ctor_get(v___x_2637_, 0);
                                    v_isSharedCheck_2680_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2637_)) as u8;
                                    if v_isSharedCheck_2680_ == 0 {
                                        v___x_2675_ = v___x_2637_;
                                        v_isShared_2676_ = v_isSharedCheck_2680_;
                                        state = 7;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_2673_);
                                        crate::leanh::lean_dec(v___x_2637_);
                                        v___x_2675_ = crate::leanh::lean_box(0);
                                        v_isShared_2676_ = v_isSharedCheck_2680_;
                                        state = 7;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec_ref_known(v___x_2622_, 7);
                                crate::leanh::lean_dec(v_numEqs_2574_);
                                v_a_2681_ = crate::leanh::lean_ctor_get(v___x_2633_, 0);
                                v_isSharedCheck_2688_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2633_)) as u8;
                                if v_isSharedCheck_2688_ == 0 {
                                    v___x_2683_ = v___x_2633_;
                                    v_isShared_2684_ = v_isSharedCheck_2688_;
                                    state = 9;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2681_);
                                    crate::leanh::lean_dec(v___x_2633_);
                                    v___x_2683_ = crate::leanh::lean_box(0);
                                    v_isShared_2684_ = v_isSharedCheck_2688_;
                                    state = 9;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_2628_);
                            crate::leanh::lean_dec_ref_known(v___x_2622_, 7);
                            crate::leanh::lean_dec(v_numEqs_2574_);
                            v_a_2689_ = crate::leanh::lean_ctor_get(v___x_2630_, 0);
                            v_isSharedCheck_2696_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2630_)) as u8;
                            if v_isSharedCheck_2696_ == 0 {
                                v___x_2691_ = v___x_2630_;
                                v_isShared_2692_ = v_isSharedCheck_2696_;
                                state = 11;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2689_);
                                crate::leanh::lean_dec(v___x_2630_);
                                v___x_2691_ = crate::leanh::lean_box(0);
                                v_isShared_2692_ = v_isSharedCheck_2696_;
                                state = 11;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v___x_2622_, 7);
                        crate::leanh::lean_dec(v_numEqs_2574_);
                        crate::leanh::lean_dec(v_mvarId_2573_);
                        v_a_2697_ = crate::leanh::lean_ctor_get(v___x_2627_, 0);
                        v_isSharedCheck_2704_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2627_)) as u8;
                        if v_isSharedCheck_2704_ == 0 {
                            v___x_2699_ = v___x_2627_;
                            v_isShared_2700_ = v_isSharedCheck_2704_;
                            state = 13;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2697_);
                            crate::leanh::lean_dec(v___x_2627_);
                            v___x_2699_ = crate::leanh::lean_box(0);
                            v_isShared_2700_ = v_isSharedCheck_2704_;
                            state = 13;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_2622_, 7);
                    crate::leanh::lean_dec(v_numEqs_2574_);
                    crate::leanh::lean_dec(v_mvarId_2573_);
                    v_a_2705_ = crate::leanh::lean_ctor_get(v___x_2623_, 0);
                    v_isSharedCheck_2712_ = (!crate::leanh::lean_is_exclusive(v___x_2623_)) as u8;
                    if v_isSharedCheck_2712_ == 0 {
                        v___x_2707_ = v___x_2623_;
                        v_isShared_2708_ = v_isSharedCheck_2712_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2705_);
                        crate::leanh::lean_dec(v___x_2623_);
                        v___x_2707_ = crate::leanh::lean_box(0);
                        v_isShared_2708_ = v_isSharedCheck_2712_;
                        state = 15;
                        continue;
                    }
                }
            }
            3 => {
                v___x_2650_ = lean_st_ref_get(v___x_2644_);
                crate::leanh::lean_dec(v___x_2644_);
                v___x_2651_ = (crate::leanh::lean_unbox(v_a_2646_) as u8);
                crate::leanh::lean_dec(v_a_2646_);
                if v___x_2651_ == 0 {
                    crate::leanh::lean_dec(v___x_2650_);
                    crate::leanh::lean_dec_ref_known(v___x_2622_, 7);
                    v___x_2652_ = crate::leanh::lean_box(0);
                    if v_isShared_2649_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2648_, 0, v___x_2652_);
                        v___x_2654_ = v___x_2648_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2655_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2655_, 0, v___x_2652_);
                        v___x_2654_ = v_reuseFailAlloc_2655_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2648_);
                    v_mvarId_2656_ = crate::leanh::lean_ctor_get(v___x_2650_, 0);
                    crate::leanh::lean_inc_n(v_mvarId_2656_, 2);
                    v_xs_2657_ = crate::leanh::lean_ctor_get(v___x_2650_, 1);
                    crate::leanh::lean_inc(v_xs_2657_);
                    v_eqsNew_2658_ = crate::leanh::lean_ctor_get(v___x_2650_, 3);
                    crate::leanh::lean_inc(v_eqsNew_2658_);
                    crate::leanh::lean_dec(v___x_2650_);
                    v___x_2659_ = l_List_reverse___redArg(v_eqsNew_2658_);
                    v___x_2660_ = lean_array_mk(v___x_2659_);
                    v___x_2661_ = crate::leanh::lean_box((v___x_2626_) as usize);
                    v___f_2662_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Meta_Match_simpH___lam__2___boxed as *mut core::ffi::c_void,
                        9,
                        4,
                    );
                    crate::leanh::lean_closure_set(v___f_2662_, 0, v_mvarId_2656_);
                    crate::leanh::lean_closure_set(v___f_2662_, 1, v___x_2660_);
                    crate::leanh::lean_closure_set(v___f_2662_, 2, v___x_2661_);
                    crate::leanh::lean_closure_set(v___f_2662_, 3, v_xs_2657_);
                    v___x_2663_ =
                        l_Lean_MVarId_withContext___at___00Lean_Meta_Match_simpH_spec__3___redArg(
                            v_mvarId_2656_,
                            v___f_2662_,
                            v___x_2622_,
                            v_a_2576_,
                            v_a_2577_,
                            v_a_2578_,
                        );
                    crate::leanh::lean_dec_ref_known(v___x_2622_, 7);
                    return v___x_2663_;
                }
            }
            4 => {
                return v___x_2654_;
            }
            5 => {
                if v_isShared_2668_ == 0 {
                    v___x_2670_ = v___x_2667_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2671_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2671_, 0, v_a_2665_);
                    v___x_2670_ = v_reuseFailAlloc_2671_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2670_;
            }
            7 => {
                if v_isShared_2676_ == 0 {
                    v___x_2678_ = v___x_2675_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2679_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2679_, 0, v_a_2673_);
                    v___x_2678_ = v_reuseFailAlloc_2679_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2678_;
            }
            9 => {
                if v_isShared_2684_ == 0 {
                    v___x_2686_ = v___x_2683_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2687_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2687_, 0, v_a_2681_);
                    v___x_2686_ = v_reuseFailAlloc_2687_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2686_;
            }
            11 => {
                if v_isShared_2692_ == 0 {
                    v___x_2694_ = v___x_2691_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2695_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2695_, 0, v_a_2689_);
                    v___x_2694_ = v_reuseFailAlloc_2695_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2694_;
            }
            13 => {
                if v_isShared_2700_ == 0 {
                    v___x_2702_ = v___x_2699_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2703_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2703_, 0, v_a_2697_);
                    v___x_2702_ = v_reuseFailAlloc_2703_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_2702_;
            }
            15 => {
                if v_isShared_2708_ == 0 {
                    v___x_2710_ = v___x_2707_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2711_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2711_, 0, v_a_2705_);
                    v___x_2710_ = v_reuseFailAlloc_2711_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_2710_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Match_simpH___boxed(
    mut v_mvarId_2715_: *mut crate::leanh::LeanObject,
    mut v_numEqs_2716_: *mut crate::leanh::LeanObject,
    mut v_a_2717_: *mut crate::leanh::LeanObject,
    mut v_a_2718_: *mut crate::leanh::LeanObject,
    mut v_a_2719_: *mut crate::leanh::LeanObject,
    mut v_a_2720_: *mut crate::leanh::LeanObject,
    mut v_a_2721_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2722_ = l_Lean_Meta_Match_simpH(
        v_mvarId_2715_,
        v_numEqs_2716_,
        v_a_2717_,
        v_a_2718_,
        v_a_2719_,
        v_a_2720_,
    );
    crate::leanh::lean_dec(v_a_2720_);
    crate::leanh::lean_dec_ref(v_a_2719_);
    crate::leanh::lean_dec(v_a_2718_);
    crate::leanh::lean_dec_ref(v_a_2717_);
    return v_res_2722_;
}
pub unsafe fn l_Lean_Meta_Match_simpH_x3f(
    mut v_h_2723_: *mut crate::leanh::LeanObject,
    mut v_numEqs_2724_: *mut crate::leanh::LeanObject,
    mut v_a_2725_: *mut crate::leanh::LeanObject,
    mut v_a_2726_: *mut crate::leanh::LeanObject,
    mut v_a_2727_: *mut crate::leanh::LeanObject,
    mut v_a_2728_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2738_: u8 = 0;
    let mut v___x_2739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2746_: u8 = 0;
    let mut v___x_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2751_: u8 = 0;
    let mut v___x_2753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2758_: u8 = 0;
    let mut v_a_2759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2762_: u8 = 0;
    let mut v___x_2764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2766_: u8 = 0;
    let mut v_isSharedCheck_2767_: u8 = 0;
    let mut v_isSharedCheck_2768_: u8 = 0;
    let mut v_a_2769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2772_: u8 = 0;
    let mut v___x_2774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2776_: u8 = 0;
    let mut v_a_2777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2780_: u8 = 0;
    let mut v___x_2782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2784_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2730_ = crate::leanh::lean_box(0);
                v___x_2731_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                    v_h_2723_,
                    v___x_2730_,
                    v_a_2725_,
                    v_a_2726_,
                    v_a_2727_,
                    v_a_2728_,
                );
                if crate::leanh::lean_obj_tag(v___x_2731_) == 0 {
                    v_a_2732_ = crate::leanh::lean_ctor_get(v___x_2731_, 0);
                    crate::leanh::lean_inc(v_a_2732_);
                    crate::leanh::lean_dec_ref_known(v___x_2731_, 1);
                    v___x_2733_ = l_Lean_Expr_mvarId_x21(v_a_2732_);
                    crate::leanh::lean_dec(v_a_2732_);
                    v___x_2734_ = l_Lean_Meta_Match_simpH(
                        v___x_2733_,
                        v_numEqs_2724_,
                        v_a_2725_,
                        v_a_2726_,
                        v_a_2727_,
                        v_a_2728_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2734_) == 0 {
                        v_a_2735_ = crate::leanh::lean_ctor_get(v___x_2734_, 0);
                        v_isSharedCheck_2768_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2734_)) as u8;
                        if v_isSharedCheck_2768_ == 0 {
                            v___x_2737_ = v___x_2734_;
                            v_isShared_2738_ = v_isSharedCheck_2768_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2735_);
                            crate::leanh::lean_dec(v___x_2734_);
                            v___x_2737_ = crate::leanh::lean_box(0);
                            v_isShared_2738_ = v_isSharedCheck_2768_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2769_ = crate::leanh::lean_ctor_get(v___x_2734_, 0);
                        v_isSharedCheck_2776_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2734_)) as u8;
                        if v_isSharedCheck_2776_ == 0 {
                            v___x_2771_ = v___x_2734_;
                            v_isShared_2772_ = v_isSharedCheck_2776_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2769_);
                            crate::leanh::lean_dec(v___x_2734_);
                            v___x_2771_ = crate::leanh::lean_box(0);
                            v_isShared_2772_ = v_isSharedCheck_2776_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_numEqs_2724_);
                    v_a_2777_ = crate::leanh::lean_ctor_get(v___x_2731_, 0);
                    v_isSharedCheck_2784_ = (!crate::leanh::lean_is_exclusive(v___x_2731_)) as u8;
                    if v_isSharedCheck_2784_ == 0 {
                        v___x_2779_ = v___x_2731_;
                        v_isShared_2780_ = v_isSharedCheck_2784_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2777_);
                        crate::leanh::lean_dec(v___x_2731_);
                        v___x_2779_ = crate::leanh::lean_box(0);
                        v_isShared_2780_ = v_isSharedCheck_2784_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_2735_) == 0 {
                    v___x_2739_ = crate::leanh::lean_box(0);
                    if v_isShared_2738_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2737_, 0, v___x_2739_);
                        v___x_2741_ = v___x_2737_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2742_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2742_, 0, v___x_2739_);
                        v___x_2741_ = v_reuseFailAlloc_2742_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2737_);
                    v_val_2743_ = crate::leanh::lean_ctor_get(v_a_2735_, 0);
                    v_isSharedCheck_2767_ = (!crate::leanh::lean_is_exclusive(v_a_2735_)) as u8;
                    if v_isSharedCheck_2767_ == 0 {
                        v___x_2745_ = v_a_2735_;
                        v_isShared_2746_ = v_isSharedCheck_2767_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2743_);
                        crate::leanh::lean_dec(v_a_2735_);
                        v___x_2745_ = crate::leanh::lean_box(0);
                        v_isShared_2746_ = v_isSharedCheck_2767_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2741_;
            }
            3 => {
                v___x_2747_ =
                    l_Lean_MVarId_getType(v_val_2743_, v_a_2725_, v_a_2726_, v_a_2727_, v_a_2728_);
                if crate::leanh::lean_obj_tag(v___x_2747_) == 0 {
                    v_a_2748_ = crate::leanh::lean_ctor_get(v___x_2747_, 0);
                    v_isSharedCheck_2758_ = (!crate::leanh::lean_is_exclusive(v___x_2747_)) as u8;
                    if v_isSharedCheck_2758_ == 0 {
                        v___x_2750_ = v___x_2747_;
                        v_isShared_2751_ = v_isSharedCheck_2758_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2748_);
                        crate::leanh::lean_dec(v___x_2747_);
                        v___x_2750_ = crate::leanh::lean_box(0);
                        v_isShared_2751_ = v_isSharedCheck_2758_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2745_);
                    v_a_2759_ = crate::leanh::lean_ctor_get(v___x_2747_, 0);
                    v_isSharedCheck_2766_ = (!crate::leanh::lean_is_exclusive(v___x_2747_)) as u8;
                    if v_isSharedCheck_2766_ == 0 {
                        v___x_2761_ = v___x_2747_;
                        v_isShared_2762_ = v_isSharedCheck_2766_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2759_);
                        crate::leanh::lean_dec(v___x_2747_);
                        v___x_2761_ = crate::leanh::lean_box(0);
                        v_isShared_2762_ = v_isSharedCheck_2766_;
                        state = 7;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_2746_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2745_, 0, v_a_2748_);
                    v___x_2753_ = v___x_2745_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2757_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2757_, 0, v_a_2748_);
                    v___x_2753_ = v_reuseFailAlloc_2757_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_2751_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2750_, 0, v___x_2753_);
                    v___x_2755_ = v___x_2750_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2756_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2756_, 0, v___x_2753_);
                    v___x_2755_ = v_reuseFailAlloc_2756_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2755_;
            }
            7 => {
                if v_isShared_2762_ == 0 {
                    v___x_2764_ = v___x_2761_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2765_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2765_, 0, v_a_2759_);
                    v___x_2764_ = v_reuseFailAlloc_2765_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2764_;
            }
            9 => {
                if v_isShared_2772_ == 0 {
                    v___x_2774_ = v___x_2771_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2775_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2775_, 0, v_a_2769_);
                    v___x_2774_ = v_reuseFailAlloc_2775_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2774_;
            }
            11 => {
                if v_isShared_2780_ == 0 {
                    v___x_2782_ = v___x_2779_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2783_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2783_, 0, v_a_2777_);
                    v___x_2782_ = v_reuseFailAlloc_2783_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2782_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Match_simpH_x3f___boxed(
    mut v_h_2785_: *mut crate::leanh::LeanObject,
    mut v_numEqs_2786_: *mut crate::leanh::LeanObject,
    mut v_a_2787_: *mut crate::leanh::LeanObject,
    mut v_a_2788_: *mut crate::leanh::LeanObject,
    mut v_a_2789_: *mut crate::leanh::LeanObject,
    mut v_a_2790_: *mut crate::leanh::LeanObject,
    mut v_a_2791_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2792_ = l_Lean_Meta_Match_simpH_x3f(
        v_h_2785_,
        v_numEqs_2786_,
        v_a_2787_,
        v_a_2788_,
        v_a_2789_,
        v_a_2790_,
    );
    crate::leanh::lean_dec(v_a_2790_);
    crate::leanh::lean_dec_ref(v_a_2789_);
    crate::leanh::lean_dec(v_a_2788_);
    crate::leanh::lean_dec_ref(v_a_2787_);
    return v_res_2792_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Match_SimpH(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Contradiction(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Match_SimpH(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Match_SimpH(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Contradiction(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Match_SimpH(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Match_SimpH(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Match_SimpH(builtin);
}
