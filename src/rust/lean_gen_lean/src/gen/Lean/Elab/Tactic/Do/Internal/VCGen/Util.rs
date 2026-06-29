// Lean compiler output
// Module: Lean.Elab.Tactic.Do.Internal.VCGen.Util
// Imports: Lean.Meta.Tactic.Grind.Main Lean.Elab.Tactic.Do.Internal.VCGen.Context Lean.Elab.Tactic.Do.Internal.VCGen.Reduce Lean.Meta.Sym.AlphaShareBuilder Lean.Meta.Sym.Intro Lean.Meta.Sym.Simp.Telescope Lean.Meta.Sym.Util
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Elab::Tactic::Do::Internal::VCGen::Context::{
    initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context,
    l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_isGrind,
    runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context,
};
use crate::r#gen::Lean::Elab::Tactic::Do::Internal::VCGen::Reduce::{
    initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce,
    l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead,
    runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appArg_x21, l_Lean_Expr_appFn_x21, l_Lean_Expr_getAppFn, l_Lean_Expr_hasMVar,
    l_Lean_Expr_isAppOf, l_Lean_Expr_isAppOfArity, l_Lean_Expr_mvarId_x21,
    l_Lean_instBEqMVarId_beq, l_Lean_instHashableMVarId_hash, l_Lean_mkApp3, l_Lean_mkAppB,
    l_Lean_mkConst,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofConstName, l_Lean_indentExpr, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp, l_Lean_Meta_Context_config,
};
use crate::r#gen::Lean::Meta::InferType::l_Lean_Meta_getLevel;
use crate::r#gen::Lean::Meta::Sym::AlphaShareBuilder::{
    initialize_Lean_Meta_Sym_AlphaShareBuilder, runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder,
};
use crate::r#gen::Lean::Meta::Sym::Apply::l_Lean_Meta_Sym_BackwardRule_apply;
use crate::r#gen::Lean::Meta::Sym::Intro::{
    initialize_Lean_Meta_Sym_Intro, l_Lean_Meta_Sym_intros, runtime_initialize_Lean_Meta_Sym_Intro,
};
use crate::r#gen::Lean::Meta::Sym::Pattern::l_Lean_Meta_Sym_isDefEqS;
use crate::r#gen::Lean::Meta::Sym::Simp::SimpM::{
    l_Lean_Meta_Sym_Simp_SimpM_run___redArg, l_Lean_Meta_Sym_Simp_simp___boxed,
};
use crate::r#gen::Lean::Meta::Sym::Simp::Telescope::{
    initialize_Lean_Meta_Sym_Simp_Telescope, l_Lean_Meta_Sym_Simp_simpTelescope___boxed,
    runtime_initialize_Lean_Meta_Sym_Simp_Telescope,
};
use crate::r#gen::Lean::Meta::Sym::Util::{
    initialize_Lean_Meta_Sym_Util, l_Lean_Meta_Sym_unfoldReducible,
    runtime_initialize_Lean_Meta_Sym_Util,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Main::{
    initialize_Lean_Meta_Tactic_Grind_Main, l_Lean_Meta_Grind_processHypotheses,
    runtime_initialize_Lean_Meta_Tactic_Grind_Main,
};
use crate::r#gen::Lean::Meta::Tactic::Replace::{
    l_Lean_MVarId_replaceTargetDefEq, l_Lean_MVarId_replaceTargetEq,
};
use crate::r#gen::Lean::Meta::Tactic::Util::{
    l_Lean_MVarId_getType, l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar,
};
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_to_usize, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_le, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_size, lean_array_push, lean_nat_add,
    lean_nat_dec_lt,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Expr::lean_expr_eqv;
pub static l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__0_value: crate::leanh::LeanStringObject<31> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 31, m_capacity: 31, m_length: 30, m_data: [91, 109, 118, 99, 103, 101, 110, 39, 32, 43, 100, 101, 98, 117, 103, 93, 32, 66, 97, 99, 107, 119, 97, 114, 100, 82, 117, 108, 101, 32, 0]};
static mut l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__2_value: crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [32, 102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 97, 112, 112, 108, 121, 32, 116, 111, 58, 0]};
static mut l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__2_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__4_value: crate::leanh::LeanStringObject<57> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 57, m_capacity: 57, m_length: 56, m_data: [10, 98, 117, 116, 32, 115, 117, 99, 99, 101, 101, 100, 101, 100, 32, 97, 102, 116, 101, 114, 32, 96, 117, 110, 102, 111, 108, 100, 82, 101, 100, 117, 99, 105, 98, 108, 101, 96, 45, 110, 111, 114, 109, 97, 108, 105, 122, 97, 116, 105, 111, 110, 32, 116, 111, 58, 0]};
static mut l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__4_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__6_value: crate::leanh::LeanStringObject<116> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 116, m_capacity: 116, m_length: 115, m_data: [10, 65, 110, 32, 101, 97, 114, 108, 105, 101, 114, 32, 115, 116, 101, 112, 32, 105, 115, 32, 109, 105, 115, 115, 105, 110, 103, 32, 97, 32, 110, 111, 114, 109, 97, 108, 105, 122, 97, 116, 105, 111, 110, 46, 32, 82, 101, 45, 114, 117, 110, 32, 119, 105, 116, 104, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 112, 112, 46, 97, 108, 108, 32, 116, 114, 117, 101, 96, 32, 116, 111, 32, 115, 101, 101, 32, 116, 104, 101, 32, 115, 116, 114, 117, 99, 116, 117, 114, 97, 108, 32, 100, 105, 102, 102, 101, 114, 101, 110, 99, 101, 46, 0]};
static mut l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__6_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__8_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__8_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__10_value: crate::leanh::LeanStringObject<35> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 35, m_capacity: 35, m_length: 34, m_data: [60, 114, 117, 108, 101, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 101, 100, 32, 102, 114, 111, 109, 32, 101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 62, 0]};
static mut l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__10_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_simpTargetTelescope___redArg___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Sym_Simp_simpTelescope___boxed as *const core::ffi::c_void,
    m_arity: 11,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_simpTargetTelescope___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_simpTargetTelescope___redArg___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_simpTargetTelescope___redArg___closed__1_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        (((100000 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_simpTargetTelescope___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_simpTargetTelescope___redArg___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__0_value:
    crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__1_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        70, 97, 105, 108, 101, 100, 32, 116, 111, 32, 105, 110, 116, 114, 111, 32, 111, 110, 32, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__3_value:
    crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [10, 67, 111, 110, 116, 101, 120, 116, 58, 32, 0],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__5_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [46, 0],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [84, 114, 117, 101, 0],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__1_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11870096045526947150 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__2_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [65, 110, 100, 0],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__3_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        9743492140944907313 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__4_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [69, 113, 0],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__5_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__4_value
        ) as *mut crate::leanh::LeanObject,
        16122875713692181903 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__6_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [114, 101, 102, 108, 0],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__6_value
) as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__7_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__4_value
        ) as *mut crate::leanh::LeanObject,
        16122875713692181903 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__7_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__7_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__6_value
        ) as *mut crate::leanh::LeanObject,
        13480818501600609864 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__7_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__8_value:
    crate::leanh::LeanStringObject<31> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 31,
    m_capacity: 31,
    m_length: 30,
    m_data: [
        114, 101, 112, 101, 97, 116, 65, 110, 100, 82, 102, 108, 58, 32, 102, 97, 105, 108, 101,
        100, 32, 116, 111, 32, 97, 112, 112, 108, 121, 32, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__8_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__9_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__10_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [105, 110, 116, 114, 111, 0],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__10_value
) as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__11_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        9743492140944907313 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__11_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__11_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__10_value
        ) as *mut crate::leanh::LeanObject,
        11695081953491693114 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__11_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__12_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [32, 116, 111, 0],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__12_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__13_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__14_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__14:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__15_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [108, 101, 102, 116, 0],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__15_value
) as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__16_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        9743492140944907313 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__16_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__16_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__15_value
        ) as *mut crate::leanh::LeanObject,
        10675986705697471500 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__16:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__16_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__17_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__17:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__18_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [114, 105, 103, 104, 116, 0],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__18:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__18_value
) as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__19_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        9743492140944907313 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__19_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__19_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__18_value
        ) as *mut crate::leanh::LeanObject,
        10515106874815532050 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__19:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__19_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__20_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__20:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__21_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        11870096045526947150 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__21_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__21_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__10_value
        ) as *mut crate::leanh::LeanObject,
        18067798339771668657 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__21:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__21_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__22_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__22:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg___lam__0(
    mut v___y_1577_: *mut crate::leanh::LeanObject,
    mut v_mctx_1578_: *mut crate::leanh::LeanObject,
    mut v_cache_1579_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_1580_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1588_: u8 = 0;
    let mut v___x_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1595_: u8 = 0;
    let mut v_unused_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1582_ = lean_st_ref_take(v___y_1577_);
                v_zetaDeltaFVarIds_1583_ = crate::leanh::lean_ctor_get(v___x_1582_, 2);
                v_postponed_1584_ = crate::leanh::lean_ctor_get(v___x_1582_, 3);
                v_diag_1585_ = crate::leanh::lean_ctor_get(v___x_1582_, 4);
                v_isSharedCheck_1595_ = (!crate::leanh::lean_is_exclusive(v___x_1582_)) as u8;
                if v_isSharedCheck_1595_ == 0 {
                    v_unused_1596_ = crate::leanh::lean_ctor_get(v___x_1582_, 1);
                    crate::leanh::lean_dec(v_unused_1596_);
                    v_unused_1597_ = crate::leanh::lean_ctor_get(v___x_1582_, 0);
                    crate::leanh::lean_dec(v_unused_1597_);
                    v___x_1587_ = v___x_1582_;
                    v_isShared_1588_ = v_isSharedCheck_1595_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_1585_);
                    crate::leanh::lean_inc(v_postponed_1584_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_1583_);
                    crate::leanh::lean_dec(v___x_1582_);
                    v___x_1587_ = crate::leanh::lean_box(0);
                    v_isShared_1588_ = v_isSharedCheck_1595_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1588_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1587_, 1, v_cache_1579_);
                    crate::leanh::lean_ctor_set(v___x_1587_, 0, v_mctx_1578_);
                    v___x_1590_ = v___x_1587_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1594_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1594_, 0, v_mctx_1578_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1594_, 1, v_cache_1579_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1594_,
                        2,
                        v_zetaDeltaFVarIds_1583_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1594_, 3, v_postponed_1584_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1594_, 4, v_diag_1585_);
                    v___x_1590_ = v_reuseFailAlloc_1594_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1591_ = lean_st_ref_set(v___y_1577_, v___x_1590_);
                v___x_1592_ = crate::leanh::lean_box(0);
                v___x_1593_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1593_, 0, v___x_1592_);
                return v___x_1593_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg___lam__0___boxed(
    mut v___y_1598_: *mut crate::leanh::LeanObject,
    mut v_mctx_1599_: *mut crate::leanh::LeanObject,
    mut v_cache_1600_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_1601_: *mut crate::leanh::LeanObject,
    mut v___y_1602_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1603_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg___lam__0(v___y_1598_, v_mctx_1599_, v_cache_1600_, v_a_x3f_1601_);
    crate::leanh::lean_dec(v_a_x3f_1601_);
    crate::leanh::lean_dec(v___y_1598_);
    return v_res_1603_;
}
pub unsafe fn l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg(
    mut v_x_1604_: *mut crate::leanh::LeanObject,
    mut v___y_1605_: *mut crate::leanh::LeanObject,
    mut v___y_1606_: *mut crate::leanh::LeanObject,
    mut v___y_1607_: *mut crate::leanh::LeanObject,
    mut v___y_1608_: *mut crate::leanh::LeanObject,
    mut v___y_1609_: *mut crate::leanh::LeanObject,
    mut v___y_1610_: *mut crate::leanh::LeanObject,
    mut v___y_1611_: *mut crate::leanh::LeanObject,
    mut v___y_1612_: *mut crate::leanh::LeanObject,
    mut v___y_1613_: *mut crate::leanh::LeanObject,
    mut v___y_1614_: *mut crate::leanh::LeanObject,
    mut v___y_1615_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1625_: u8 = 0;
    let mut v___x_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1631_: u8 = 0;
    let mut v___x_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1635_: u8 = 0;
    let mut v_unused_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1638_: u8 = 0;
    let mut v_a_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1644_: u8 = 0;
    let mut v___x_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1648_: u8 = 0;
    let mut v_unused_1649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1617_ = lean_st_ref_get(v___y_1613_);
                v___x_1618_ = lean_st_ref_get(v___y_1613_);
                v_mctx_1619_ = crate::leanh::lean_ctor_get(v___x_1617_, 0);
                crate::leanh::lean_inc_ref(v_mctx_1619_);
                crate::leanh::lean_dec(v___x_1617_);
                v_cache_1620_ = crate::leanh::lean_ctor_get(v___x_1618_, 1);
                crate::leanh::lean_inc_ref(v_cache_1620_);
                crate::leanh::lean_dec(v___x_1618_);
                crate::leanh::lean_inc(v___y_1615_);
                crate::leanh::lean_inc_ref(v___y_1614_);
                crate::leanh::lean_inc(v___y_1613_);
                crate::leanh::lean_inc_ref(v___y_1612_);
                crate::leanh::lean_inc(v___y_1611_);
                crate::leanh::lean_inc_ref(v___y_1610_);
                crate::leanh::lean_inc(v___y_1609_);
                crate::leanh::lean_inc_ref(v___y_1608_);
                crate::leanh::lean_inc(v___y_1607_);
                crate::leanh::lean_inc(v___y_1606_);
                crate::leanh::lean_inc_ref(v___y_1605_);
                v___x_1621_ = crate::leanh::lean_apply_12(
                    v_x_1604_,
                    v___y_1605_,
                    v___y_1606_,
                    v___y_1607_,
                    v___y_1608_,
                    v___y_1609_,
                    v___y_1610_,
                    v___y_1611_,
                    v___y_1612_,
                    v___y_1613_,
                    v___y_1614_,
                    v___y_1615_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_1621_) == 0 {
                    v_a_1622_ = crate::leanh::lean_ctor_get(v___x_1621_, 0);
                    v_isSharedCheck_1638_ = (!crate::leanh::lean_is_exclusive(v___x_1621_)) as u8;
                    if v_isSharedCheck_1638_ == 0 {
                        v___x_1624_ = v___x_1621_;
                        v_isShared_1625_ = v_isSharedCheck_1638_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1622_);
                        crate::leanh::lean_dec(v___x_1621_);
                        v___x_1624_ = crate::leanh::lean_box(0);
                        v_isShared_1625_ = v_isSharedCheck_1638_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1639_ = crate::leanh::lean_ctor_get(v___x_1621_, 0);
                    crate::leanh::lean_inc(v_a_1639_);
                    crate::leanh::lean_dec_ref_known(v___x_1621_, 1);
                    v___x_1640_ = crate::leanh::lean_box(0);
                    v___x_1641_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg___lam__0(v___y_1613_, v_mctx_1619_, v_cache_1620_, v___x_1640_);
                    v_isSharedCheck_1648_ = (!crate::leanh::lean_is_exclusive(v___x_1641_)) as u8;
                    if v_isSharedCheck_1648_ == 0 {
                        v_unused_1649_ = crate::leanh::lean_ctor_get(v___x_1641_, 0);
                        crate::leanh::lean_dec(v_unused_1649_);
                        v___x_1643_ = v___x_1641_;
                        v_isShared_1644_ = v_isSharedCheck_1648_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_1641_);
                        v___x_1643_ = crate::leanh::lean_box(0);
                        v_isShared_1644_ = v_isSharedCheck_1648_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_a_1622_);
                if v_isShared_1625_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1624_, 1);
                    v___x_1627_ = v___x_1624_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1637_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1637_, 0, v_a_1622_);
                    v___x_1627_ = v_reuseFailAlloc_1637_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1628_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg___lam__0(v___y_1613_, v_mctx_1619_, v_cache_1620_, v___x_1627_);
                crate::leanh::lean_dec_ref(v___x_1627_);
                v_isSharedCheck_1635_ = (!crate::leanh::lean_is_exclusive(v___x_1628_)) as u8;
                if v_isSharedCheck_1635_ == 0 {
                    v_unused_1636_ = crate::leanh::lean_ctor_get(v___x_1628_, 0);
                    crate::leanh::lean_dec(v_unused_1636_);
                    v___x_1630_ = v___x_1628_;
                    v_isShared_1631_ = v_isSharedCheck_1635_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_1628_);
                    v___x_1630_ = crate::leanh::lean_box(0);
                    v_isShared_1631_ = v_isSharedCheck_1635_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1631_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1630_, 0, v_a_1622_);
                    v___x_1633_ = v___x_1630_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1634_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1634_, 0, v_a_1622_);
                    v___x_1633_ = v_reuseFailAlloc_1634_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1633_;
            }
            5 => {
                if v_isShared_1644_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1643_, 1);
                    crate::leanh::lean_ctor_set(v___x_1643_, 0, v_a_1639_);
                    v___x_1646_ = v___x_1643_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1647_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1647_, 0, v_a_1639_);
                    v___x_1646_ = v_reuseFailAlloc_1647_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1646_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg___boxed(
    mut v_x_1650_: *mut crate::leanh::LeanObject,
    mut v___y_1651_: *mut crate::leanh::LeanObject,
    mut v___y_1652_: *mut crate::leanh::LeanObject,
    mut v___y_1653_: *mut crate::leanh::LeanObject,
    mut v___y_1654_: *mut crate::leanh::LeanObject,
    mut v___y_1655_: *mut crate::leanh::LeanObject,
    mut v___y_1656_: *mut crate::leanh::LeanObject,
    mut v___y_1657_: *mut crate::leanh::LeanObject,
    mut v___y_1658_: *mut crate::leanh::LeanObject,
    mut v___y_1659_: *mut crate::leanh::LeanObject,
    mut v___y_1660_: *mut crate::leanh::LeanObject,
    mut v___y_1661_: *mut crate::leanh::LeanObject,
    mut v___y_1662_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1663_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg(v_x_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_);
    crate::leanh::lean_dec(v___y_1661_);
    crate::leanh::lean_dec_ref(v___y_1660_);
    crate::leanh::lean_dec(v___y_1659_);
    crate::leanh::lean_dec_ref(v___y_1658_);
    crate::leanh::lean_dec(v___y_1657_);
    crate::leanh::lean_dec_ref(v___y_1656_);
    crate::leanh::lean_dec(v___y_1655_);
    crate::leanh::lean_dec_ref(v___y_1654_);
    crate::leanh::lean_dec(v___y_1653_);
    crate::leanh::lean_dec(v___y_1652_);
    crate::leanh::lean_dec_ref(v___y_1651_);
    return v_res_1663_;
}
pub unsafe fn l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0(
    mut v_00_u03b1_1664_: *mut crate::leanh::LeanObject,
    mut v_x_1665_: *mut crate::leanh::LeanObject,
    mut v___y_1666_: *mut crate::leanh::LeanObject,
    mut v___y_1667_: *mut crate::leanh::LeanObject,
    mut v___y_1668_: *mut crate::leanh::LeanObject,
    mut v___y_1669_: *mut crate::leanh::LeanObject,
    mut v___y_1670_: *mut crate::leanh::LeanObject,
    mut v___y_1671_: *mut crate::leanh::LeanObject,
    mut v___y_1672_: *mut crate::leanh::LeanObject,
    mut v___y_1673_: *mut crate::leanh::LeanObject,
    mut v___y_1674_: *mut crate::leanh::LeanObject,
    mut v___y_1675_: *mut crate::leanh::LeanObject,
    mut v___y_1676_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1678_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg(v_x_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_);
    return v___x_1678_;
}
pub unsafe fn l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___boxed(
    mut v_00_u03b1_1679_: *mut crate::leanh::LeanObject,
    mut v_x_1680_: *mut crate::leanh::LeanObject,
    mut v___y_1681_: *mut crate::leanh::LeanObject,
    mut v___y_1682_: *mut crate::leanh::LeanObject,
    mut v___y_1683_: *mut crate::leanh::LeanObject,
    mut v___y_1684_: *mut crate::leanh::LeanObject,
    mut v___y_1685_: *mut crate::leanh::LeanObject,
    mut v___y_1686_: *mut crate::leanh::LeanObject,
    mut v___y_1687_: *mut crate::leanh::LeanObject,
    mut v___y_1688_: *mut crate::leanh::LeanObject,
    mut v___y_1689_: *mut crate::leanh::LeanObject,
    mut v___y_1690_: *mut crate::leanh::LeanObject,
    mut v___y_1691_: *mut crate::leanh::LeanObject,
    mut v___y_1692_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1693_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0(v_00_u03b1_1679_, v_x_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_);
    crate::leanh::lean_dec(v___y_1691_);
    crate::leanh::lean_dec_ref(v___y_1690_);
    crate::leanh::lean_dec(v___y_1689_);
    crate::leanh::lean_dec_ref(v___y_1688_);
    crate::leanh::lean_dec(v___y_1687_);
    crate::leanh::lean_dec_ref(v___y_1686_);
    crate::leanh::lean_dec(v___y_1685_);
    crate::leanh::lean_dec_ref(v___y_1684_);
    crate::leanh::lean_dec(v___y_1683_);
    crate::leanh::lean_dec(v___y_1682_);
    crate::leanh::lean_dec_ref(v___y_1681_);
    return v_res_1693_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___lam__0(
    mut v_a_1694_: *mut crate::leanh::LeanObject,
    mut v___x_1695_: *mut crate::leanh::LeanObject,
    mut v_rule_1696_: *mut crate::leanh::LeanObject,
    mut v___x_1697_: u8,
    mut v_debug_1698_: u8,
    mut v___y_1699_: *mut crate::leanh::LeanObject,
    mut v___y_1700_: *mut crate::leanh::LeanObject,
    mut v___y_1701_: *mut crate::leanh::LeanObject,
    mut v___y_1702_: *mut crate::leanh::LeanObject,
    mut v___y_1703_: *mut crate::leanh::LeanObject,
    mut v___y_1704_: *mut crate::leanh::LeanObject,
    mut v___y_1705_: *mut crate::leanh::LeanObject,
    mut v___y_1706_: *mut crate::leanh::LeanObject,
    mut v___y_1707_: *mut crate::leanh::LeanObject,
    mut v___y_1708_: *mut crate::leanh::LeanObject,
    mut v___y_1709_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1718_: u8 = 0;
    let mut v___x_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1727_: u8 = 0;
    let mut v_a_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1731_: u8 = 0;
    let mut v___x_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1735_: u8 = 0;
    let mut v_a_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1739_: u8 = 0;
    let mut v___x_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1743_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1711_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                    v_a_1694_,
                    v___x_1695_,
                    v___y_1706_,
                    v___y_1707_,
                    v___y_1708_,
                    v___y_1709_,
                );
                if crate::leanh::lean_obj_tag(v___x_1711_) == 0 {
                    v_a_1712_ = crate::leanh::lean_ctor_get(v___x_1711_, 0);
                    crate::leanh::lean_inc(v_a_1712_);
                    crate::leanh::lean_dec_ref_known(v___x_1711_, 1);
                    v___x_1713_ = l_Lean_Expr_mvarId_x21(v_a_1712_);
                    crate::leanh::lean_dec(v_a_1712_);
                    v___x_1714_ = l_Lean_Meta_Sym_BackwardRule_apply(
                        v___x_1713_,
                        v_rule_1696_,
                        v___y_1704_,
                        v___y_1705_,
                        v___y_1706_,
                        v___y_1707_,
                        v___y_1708_,
                        v___y_1709_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1714_) == 0 {
                        v_a_1715_ = crate::leanh::lean_ctor_get(v___x_1714_, 0);
                        v_isSharedCheck_1727_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1714_)) as u8;
                        if v_isSharedCheck_1727_ == 0 {
                            v___x_1717_ = v___x_1714_;
                            v_isShared_1718_ = v_isSharedCheck_1727_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1715_);
                            crate::leanh::lean_dec(v___x_1714_);
                            v___x_1717_ = crate::leanh::lean_box(0);
                            v_isShared_1718_ = v_isSharedCheck_1727_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1728_ = crate::leanh::lean_ctor_get(v___x_1714_, 0);
                        v_isSharedCheck_1735_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1714_)) as u8;
                        if v_isSharedCheck_1735_ == 0 {
                            v___x_1730_ = v___x_1714_;
                            v_isShared_1731_ = v_isSharedCheck_1735_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1728_);
                            crate::leanh::lean_dec(v___x_1714_);
                            v___x_1730_ = crate::leanh::lean_box(0);
                            v_isShared_1731_ = v_isSharedCheck_1735_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_rule_1696_);
                    v_a_1736_ = crate::leanh::lean_ctor_get(v___x_1711_, 0);
                    v_isSharedCheck_1743_ = (!crate::leanh::lean_is_exclusive(v___x_1711_)) as u8;
                    if v_isSharedCheck_1743_ == 0 {
                        v___x_1738_ = v___x_1711_;
                        v_isShared_1739_ = v_isSharedCheck_1743_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1736_);
                        crate::leanh::lean_dec(v___x_1711_);
                        v___x_1738_ = crate::leanh::lean_box(0);
                        v_isShared_1739_ = v_isSharedCheck_1743_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_1715_) == 0 {
                    v___x_1719_ = crate::leanh::lean_box((v___x_1697_) as usize);
                    if v_isShared_1718_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1717_, 0, v___x_1719_);
                        v___x_1721_ = v___x_1717_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1722_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1722_, 0, v___x_1719_);
                        v___x_1721_ = v_reuseFailAlloc_1722_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v_a_1715_, 1);
                    v___x_1723_ = crate::leanh::lean_box((v_debug_1698_) as usize);
                    if v_isShared_1718_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1717_, 0, v___x_1723_);
                        v___x_1725_ = v___x_1717_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1726_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1726_, 0, v___x_1723_);
                        v___x_1725_ = v_reuseFailAlloc_1726_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1721_;
            }
            3 => {
                return v___x_1725_;
            }
            4 => {
                if v_isShared_1731_ == 0 {
                    v___x_1733_ = v___x_1730_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1734_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1734_, 0, v_a_1728_);
                    v___x_1733_ = v_reuseFailAlloc_1734_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1733_;
            }
            6 => {
                if v_isShared_1739_ == 0 {
                    v___x_1741_ = v___x_1738_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1742_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1742_, 0, v_a_1736_);
                    v___x_1741_ = v_reuseFailAlloc_1742_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1741_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___lam__0___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1744_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v___x_1745_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_rule_1746_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v___x_1747_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_debug_1748_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___y_1749_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___y_1750_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___y_1751_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___y_1752_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_1753_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_1754_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_1755_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_1756_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_1757_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_1758_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_1759_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_1760_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___x_43892__boxed_1761_: u8 = 0;
    let mut v_debug_boxed_1762_: u8 = 0;
    let mut v_res_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_43892__boxed_1761_ = (crate::leanh::lean_unbox(v___x_1747_) as u8);
    v_debug_boxed_1762_ = (crate::leanh::lean_unbox(v_debug_1748_) as u8);
    v_res_1763_ = l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___lam__0(
        v_a_1744_,
        v___x_1745_,
        v_rule_1746_,
        v___x_43892__boxed_1761_,
        v_debug_boxed_1762_,
        v___y_1749_,
        v___y_1750_,
        v___y_1751_,
        v___y_1752_,
        v___y_1753_,
        v___y_1754_,
        v___y_1755_,
        v___y_1756_,
        v___y_1757_,
        v___y_1758_,
        v___y_1759_,
    );
    crate::leanh::lean_dec(v___y_1759_);
    crate::leanh::lean_dec_ref(v___y_1758_);
    crate::leanh::lean_dec(v___y_1757_);
    crate::leanh::lean_dec_ref(v___y_1756_);
    crate::leanh::lean_dec(v___y_1755_);
    crate::leanh::lean_dec_ref(v___y_1754_);
    crate::leanh::lean_dec(v___y_1753_);
    crate::leanh::lean_dec_ref(v___y_1752_);
    crate::leanh::lean_dec(v___y_1751_);
    crate::leanh::lean_dec(v___y_1750_);
    crate::leanh::lean_dec_ref(v___y_1749_);
    return v_res_1763_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1_spec__1(
    mut v_msgData_1764_: *mut crate::leanh::LeanObject,
    mut v___y_1765_: *mut crate::leanh::LeanObject,
    mut v___y_1766_: *mut crate::leanh::LeanObject,
    mut v___y_1767_: *mut crate::leanh::LeanObject,
    mut v___y_1768_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1770_ = lean_st_ref_get(v___y_1768_);
    v_env_1771_ = crate::leanh::lean_ctor_get(v___x_1770_, 0);
    crate::leanh::lean_inc_ref(v_env_1771_);
    crate::leanh::lean_dec(v___x_1770_);
    v___x_1772_ = lean_st_ref_get(v___y_1766_);
    v_mctx_1773_ = crate::leanh::lean_ctor_get(v___x_1772_, 0);
    crate::leanh::lean_inc_ref(v_mctx_1773_);
    crate::leanh::lean_dec(v___x_1772_);
    v_lctx_1774_ = crate::leanh::lean_ctor_get(v___y_1765_, 2);
    v_options_1775_ = crate::leanh::lean_ctor_get(v___y_1767_, 2);
    crate::leanh::lean_inc_ref(v_options_1775_);
    crate::leanh::lean_inc_ref(v_lctx_1774_);
    v___x_1776_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1776_, 0, v_env_1771_);
    crate::leanh::lean_ctor_set(v___x_1776_, 1, v_mctx_1773_);
    crate::leanh::lean_ctor_set(v___x_1776_, 2, v_lctx_1774_);
    crate::leanh::lean_ctor_set(v___x_1776_, 3, v_options_1775_);
    v___x_1777_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1777_, 0, v___x_1776_);
    crate::leanh::lean_ctor_set(v___x_1777_, 1, v_msgData_1764_);
    v___x_1778_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1778_, 0, v___x_1777_);
    return v___x_1778_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1_spec__1___boxed(
    mut v_msgData_1779_: *mut crate::leanh::LeanObject,
    mut v___y_1780_: *mut crate::leanh::LeanObject,
    mut v___y_1781_: *mut crate::leanh::LeanObject,
    mut v___y_1782_: *mut crate::leanh::LeanObject,
    mut v___y_1783_: *mut crate::leanh::LeanObject,
    mut v___y_1784_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1785_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1_spec__1(v_msgData_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_);
    crate::leanh::lean_dec(v___y_1783_);
    crate::leanh::lean_dec_ref(v___y_1782_);
    crate::leanh::lean_dec(v___y_1781_);
    crate::leanh::lean_dec_ref(v___y_1780_);
    return v_res_1785_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg(
    mut v_msg_1786_: *mut crate::leanh::LeanObject,
    mut v___y_1787_: *mut crate::leanh::LeanObject,
    mut v___y_1788_: *mut crate::leanh::LeanObject,
    mut v___y_1789_: *mut crate::leanh::LeanObject,
    mut v___y_1790_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1797_: u8 = 0;
    let mut v___x_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1802_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1792_ = crate::leanh::lean_ctor_get(v___y_1789_, 5);
                v___x_1793_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1_spec__1(v_msg_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_);
                v_a_1794_ = crate::leanh::lean_ctor_get(v___x_1793_, 0);
                v_isSharedCheck_1802_ = (!crate::leanh::lean_is_exclusive(v___x_1793_)) as u8;
                if v_isSharedCheck_1802_ == 0 {
                    v___x_1796_ = v___x_1793_;
                    v_isShared_1797_ = v_isSharedCheck_1802_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1794_);
                    crate::leanh::lean_dec(v___x_1793_);
                    v___x_1796_ = crate::leanh::lean_box(0);
                    v_isShared_1797_ = v_isSharedCheck_1802_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_1792_);
                v___x_1798_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1798_, 0, v_ref_1792_);
                crate::leanh::lean_ctor_set(v___x_1798_, 1, v_a_1794_);
                if v_isShared_1797_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1796_, 1);
                    crate::leanh::lean_ctor_set(v___x_1796_, 0, v___x_1798_);
                    v___x_1800_ = v___x_1796_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1801_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1801_, 0, v___x_1798_);
                    v___x_1800_ = v_reuseFailAlloc_1801_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1800_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg___boxed(
    mut v_msg_1803_: *mut crate::leanh::LeanObject,
    mut v___y_1804_: *mut crate::leanh::LeanObject,
    mut v___y_1805_: *mut crate::leanh::LeanObject,
    mut v___y_1806_: *mut crate::leanh::LeanObject,
    mut v___y_1807_: *mut crate::leanh::LeanObject,
    mut v___y_1808_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1809_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg(v_msg_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_);
    crate::leanh::lean_dec(v___y_1807_);
    crate::leanh::lean_dec_ref(v___y_1806_);
    crate::leanh::lean_dec(v___y_1805_);
    crate::leanh::lean_dec_ref(v___y_1804_);
    return v_res_1809_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1811_ =
        l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__0;
    v___x_1812_ = l_Lean_stringToMessageData(v___x_1811_);
    return v___x_1812_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1814_ =
        l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__2;
    v___x_1815_ = l_Lean_stringToMessageData(v___x_1814_);
    return v___x_1815_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1817_ =
        l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__4;
    v___x_1818_ = l_Lean_stringToMessageData(v___x_1817_);
    return v___x_1818_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1820_ =
        l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__6;
    v___x_1821_ = l_Lean_stringToMessageData(v___x_1820_);
    return v___x_1821_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1823_ =
        l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__8;
    v___x_1824_ = l_Lean_stringToMessageData(v___x_1823_);
    return v___x_1824_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1826_ =
        l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__10;
    v___x_1827_ = l_Lean_stringToMessageData(v___x_1826_);
    return v___x_1827_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(
    mut v_rule_1828_: *mut crate::leanh::LeanObject,
    mut v_goal_1829_: *mut crate::leanh::LeanObject,
    mut v_ruleDesc_x3f_1830_: *mut crate::leanh::LeanObject,
    mut v_a_1831_: *mut crate::leanh::LeanObject,
    mut v_a_1832_: *mut crate::leanh::LeanObject,
    mut v_a_1833_: *mut crate::leanh::LeanObject,
    mut v_a_1834_: *mut crate::leanh::LeanObject,
    mut v_a_1835_: *mut crate::leanh::LeanObject,
    mut v_a_1836_: *mut crate::leanh::LeanObject,
    mut v_a_1837_: *mut crate::leanh::LeanObject,
    mut v_a_1838_: *mut crate::leanh::LeanObject,
    mut v_a_1839_: *mut crate::leanh::LeanObject,
    mut v_a_1840_: *mut crate::leanh::LeanObject,
    mut v_a_1841_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_1845_: u8 = 0;
    let mut v___x_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1852_: u8 = 0;
    let mut v___x_1853_: u8 = 0;
    let mut v___x_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1862_: u8 = 0;
    let mut v___y_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1881_: u8 = 0;
    let mut v___x_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1885_: u8 = 0;
    let mut v___x_1886_: u8 = 0;
    let mut v___x_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1899_: u8 = 0;
    let mut v_a_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1903_: u8 = 0;
    let mut v___x_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1907_: u8 = 0;
    let mut v___x_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1911_: u8 = 0;
    let mut v_a_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1915_: u8 = 0;
    let mut v___x_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1919_: u8 = 0;
    let mut v_a_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1923_: u8 = 0;
    let mut v___x_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1927_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_rule_1828_);
                crate::leanh::lean_inc(v_goal_1829_);
                v___x_1843_ = l_Lean_Meta_Sym_BackwardRule_apply(
                    v_goal_1829_,
                    v_rule_1828_,
                    v_a_1836_,
                    v_a_1837_,
                    v_a_1838_,
                    v_a_1839_,
                    v_a_1840_,
                    v_a_1841_,
                );
                if crate::leanh::lean_obj_tag(v___x_1843_) == 0 {
                    v_a_1844_ = crate::leanh::lean_ctor_get(v___x_1843_, 0);
                    crate::leanh::lean_inc(v_a_1844_);
                    if crate::leanh::lean_obj_tag(v_a_1844_) == 0 {
                        v_debug_1845_ = crate::leanh::lean_ctor_get_uint8(
                            v_a_1831_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 19 + 3) as u32,
                        );
                        if v_debug_1845_ == 0 {
                            crate::leanh::lean_dec(v_ruleDesc_x3f_1830_);
                            crate::leanh::lean_dec(v_goal_1829_);
                            crate::leanh::lean_dec_ref(v_rule_1828_);
                            return v___x_1843_;
                        } else {
                            crate::leanh::lean_dec_ref_known(v___x_1843_, 1);
                            v___x_1846_ = l_Lean_MVarId_getType(
                                v_goal_1829_,
                                v_a_1838_,
                                v_a_1839_,
                                v_a_1840_,
                                v_a_1841_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_1846_) == 0 {
                                v_a_1847_ = crate::leanh::lean_ctor_get(v___x_1846_, 0);
                                crate::leanh::lean_inc_n(v_a_1847_, 2);
                                crate::leanh::lean_dec_ref_known(v___x_1846_, 1);
                                v___x_1848_ = l_Lean_Meta_Sym_unfoldReducible(
                                    v_a_1847_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_1848_) == 0 {
                                    v_a_1849_ = crate::leanh::lean_ctor_get(v___x_1848_, 0);
                                    v_isSharedCheck_1911_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1848_)) as u8;
                                    if v_isSharedCheck_1911_ == 0 {
                                        v___x_1851_ = v___x_1848_;
                                        v_isShared_1852_ = v_isSharedCheck_1911_;
                                        state = 1;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_1849_);
                                        crate::leanh::lean_dec(v___x_1848_);
                                        v___x_1851_ = crate::leanh::lean_box(0);
                                        v_isShared_1852_ = v_isSharedCheck_1911_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_1847_);
                                    crate::leanh::lean_dec(v_ruleDesc_x3f_1830_);
                                    crate::leanh::lean_dec_ref(v_rule_1828_);
                                    v_a_1912_ = crate::leanh::lean_ctor_get(v___x_1848_, 0);
                                    v_isSharedCheck_1919_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1848_)) as u8;
                                    if v_isSharedCheck_1919_ == 0 {
                                        v___x_1914_ = v___x_1848_;
                                        v_isShared_1915_ = v_isSharedCheck_1919_;
                                        state = 10;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_1912_);
                                        crate::leanh::lean_dec(v___x_1848_);
                                        v___x_1914_ = crate::leanh::lean_box(0);
                                        v_isShared_1915_ = v_isSharedCheck_1919_;
                                        state = 10;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_ruleDesc_x3f_1830_);
                                crate::leanh::lean_dec_ref(v_rule_1828_);
                                v_a_1920_ = crate::leanh::lean_ctor_get(v___x_1846_, 0);
                                v_isSharedCheck_1927_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1846_)) as u8;
                                if v_isSharedCheck_1927_ == 0 {
                                    v___x_1922_ = v___x_1846_;
                                    v_isShared_1923_ = v_isSharedCheck_1927_;
                                    state = 12;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1920_);
                                    crate::leanh::lean_dec(v___x_1846_);
                                    v___x_1922_ = crate::leanh::lean_box(0);
                                    v_isShared_1923_ = v_isSharedCheck_1927_;
                                    state = 12;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_a_1844_, 1);
                        crate::leanh::lean_dec(v_ruleDesc_x3f_1830_);
                        crate::leanh::lean_dec(v_goal_1829_);
                        crate::leanh::lean_dec_ref(v_rule_1828_);
                        return v___x_1843_;
                    }
                } else {
                    crate::leanh::lean_dec(v_ruleDesc_x3f_1830_);
                    crate::leanh::lean_dec(v_goal_1829_);
                    crate::leanh::lean_dec_ref(v_rule_1828_);
                    return v___x_1843_;
                }
            }
            1 => {
                v___x_1853_ = lean_expr_eqv(v_a_1849_, v_a_1847_);
                if v___x_1853_ == 0 {
                    crate::leanh::lean_del_object(v___x_1851_);
                    v___x_1854_ = crate::leanh::lean_box(0);
                    v___x_1855_ = crate::leanh::lean_box((v___x_1853_) as usize);
                    v___x_1856_ = crate::leanh::lean_box((v_debug_1845_) as usize);
                    crate::leanh::lean_inc_ref(v_rule_1828_);
                    crate::leanh::lean_inc(v_a_1849_);
                    v___f_1857_ = crate::leanh::lean_alloc_closure(l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___lam__0___boxed as *mut core::ffi::c_void, 17, 5);
                    crate::leanh::lean_closure_set(v___f_1857_, 0, v_a_1849_);
                    crate::leanh::lean_closure_set(v___f_1857_, 1, v___x_1854_);
                    crate::leanh::lean_closure_set(v___f_1857_, 2, v_rule_1828_);
                    crate::leanh::lean_closure_set(v___f_1857_, 3, v___x_1855_);
                    crate::leanh::lean_closure_set(v___f_1857_, 4, v___x_1856_);
                    v___x_1858_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg(v___f_1857_, v_a_1831_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_);
                    if crate::leanh::lean_obj_tag(v___x_1858_) == 0 {
                        v_a_1859_ = crate::leanh::lean_ctor_get(v___x_1858_, 0);
                        v_isSharedCheck_1899_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1858_)) as u8;
                        if v_isSharedCheck_1899_ == 0 {
                            v___x_1861_ = v___x_1858_;
                            v_isShared_1862_ = v_isSharedCheck_1899_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1859_);
                            crate::leanh::lean_dec(v___x_1858_);
                            v___x_1861_ = crate::leanh::lean_box(0);
                            v_isShared_1862_ = v_isSharedCheck_1899_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_1849_);
                        crate::leanh::lean_dec(v_a_1847_);
                        crate::leanh::lean_dec(v_ruleDesc_x3f_1830_);
                        crate::leanh::lean_dec_ref(v_rule_1828_);
                        v_a_1900_ = crate::leanh::lean_ctor_get(v___x_1858_, 0);
                        v_isSharedCheck_1907_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1858_)) as u8;
                        if v_isSharedCheck_1907_ == 0 {
                            v___x_1902_ = v___x_1858_;
                            v_isShared_1903_ = v_isSharedCheck_1907_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1900_);
                            crate::leanh::lean_dec(v___x_1858_);
                            v___x_1902_ = crate::leanh::lean_box(0);
                            v_isShared_1903_ = v_isSharedCheck_1907_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1849_);
                    crate::leanh::lean_dec(v_a_1847_);
                    crate::leanh::lean_dec(v_ruleDesc_x3f_1830_);
                    crate::leanh::lean_dec_ref(v_rule_1828_);
                    if v_isShared_1852_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1851_, 0, v_a_1844_);
                        v___x_1909_ = v___x_1851_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_1910_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1910_, 0, v_a_1844_);
                        v___x_1909_ = v_reuseFailAlloc_1910_;
                        state = 9;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1886_ = (crate::leanh::lean_unbox(v_a_1859_) as u8);
                crate::leanh::lean_dec(v_a_1859_);
                if v___x_1886_ == 0 {
                    crate::leanh::lean_dec(v_a_1849_);
                    crate::leanh::lean_dec(v_a_1847_);
                    crate::leanh::lean_dec(v_ruleDesc_x3f_1830_);
                    crate::leanh::lean_dec_ref(v_rule_1828_);
                    if v_isShared_1862_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1861_, 0, v_a_1844_);
                        v___x_1888_ = v___x_1861_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1889_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1889_, 0, v_a_1844_);
                        v___x_1888_ = v_reuseFailAlloc_1889_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1861_);
                    if crate::leanh::lean_obj_tag(v_ruleDesc_x3f_1830_) == 0 {
                        v_expr_1890_ = crate::leanh::lean_ctor_get(v_rule_1828_, 0);
                        crate::leanh::lean_inc_ref(v_expr_1890_);
                        crate::leanh::lean_dec_ref(v_rule_1828_);
                        v___x_1891_ = l_Lean_Expr_getAppFn(v_expr_1890_);
                        crate::leanh::lean_dec_ref(v_expr_1890_);
                        if crate::leanh::lean_obj_tag(v___x_1891_) == 4 {
                            v_declName_1892_ = crate::leanh::lean_ctor_get(v___x_1891_, 0);
                            crate::leanh::lean_inc(v_declName_1892_);
                            crate::leanh::lean_dec_ref_known(v___x_1891_, 2);
                            v___x_1893_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__9), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__9_once), _init_l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__9);
                            v___x_1894_ =
                                l_Lean_MessageData_ofConstName(v_declName_1892_, v___x_1853_);
                            v___x_1895_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1895_, 0, v___x_1893_);
                            crate::leanh::lean_ctor_set(v___x_1895_, 1, v___x_1894_);
                            v___x_1896_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1896_, 0, v___x_1895_);
                            crate::leanh::lean_ctor_set(v___x_1896_, 1, v___x_1893_);
                            v___y_1864_ = v___x_1896_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v___x_1891_);
                            v___x_1897_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__11), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__11_once), _init_l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__11);
                            v___y_1864_ = v___x_1897_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_rule_1828_);
                        v_val_1898_ = crate::leanh::lean_ctor_get(v_ruleDesc_x3f_1830_, 0);
                        crate::leanh::lean_inc(v_val_1898_);
                        crate::leanh::lean_dec_ref_known(v_ruleDesc_x3f_1830_, 1);
                        v___y_1864_ = v_val_1898_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1865_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__1_once), _init_l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__1);
                v___x_1866_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1866_, 0, v___x_1865_);
                crate::leanh::lean_ctor_set(v___x_1866_, 1, v___y_1864_);
                v___x_1867_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__3), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__3_once), _init_l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__3);
                v___x_1868_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1868_, 0, v___x_1866_);
                crate::leanh::lean_ctor_set(v___x_1868_, 1, v___x_1867_);
                v___x_1869_ = l_Lean_indentExpr(v_a_1847_);
                v___x_1870_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1870_, 0, v___x_1868_);
                crate::leanh::lean_ctor_set(v___x_1870_, 1, v___x_1869_);
                v___x_1871_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__5), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__5_once), _init_l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__5);
                v___x_1872_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1872_, 0, v___x_1870_);
                crate::leanh::lean_ctor_set(v___x_1872_, 1, v___x_1871_);
                v___x_1873_ = l_Lean_indentExpr(v_a_1849_);
                v___x_1874_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1874_, 0, v___x_1872_);
                crate::leanh::lean_ctor_set(v___x_1874_, 1, v___x_1873_);
                v___x_1875_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__7), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__7_once), _init_l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__7);
                v___x_1876_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1876_, 0, v___x_1874_);
                crate::leanh::lean_ctor_set(v___x_1876_, 1, v___x_1875_);
                v___x_1877_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg(v___x_1876_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_);
                v_a_1878_ = crate::leanh::lean_ctor_get(v___x_1877_, 0);
                v_isSharedCheck_1885_ = (!crate::leanh::lean_is_exclusive(v___x_1877_)) as u8;
                if v_isSharedCheck_1885_ == 0 {
                    v___x_1880_ = v___x_1877_;
                    v_isShared_1881_ = v_isSharedCheck_1885_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1878_);
                    crate::leanh::lean_dec(v___x_1877_);
                    v___x_1880_ = crate::leanh::lean_box(0);
                    v_isShared_1881_ = v_isSharedCheck_1885_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1881_ == 0 {
                    v___x_1883_ = v___x_1880_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1884_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1884_, 0, v_a_1878_);
                    v___x_1883_ = v_reuseFailAlloc_1884_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1883_;
            }
            6 => {
                return v___x_1888_;
            }
            7 => {
                if v_isShared_1903_ == 0 {
                    v___x_1905_ = v___x_1902_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1906_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1906_, 0, v_a_1900_);
                    v___x_1905_ = v_reuseFailAlloc_1906_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1905_;
            }
            9 => {
                return v___x_1909_;
            }
            10 => {
                if v_isShared_1915_ == 0 {
                    v___x_1917_ = v___x_1914_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1918_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1918_, 0, v_a_1912_);
                    v___x_1917_ = v_reuseFailAlloc_1918_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1917_;
            }
            12 => {
                if v_isShared_1923_ == 0 {
                    v___x_1925_ = v___x_1922_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1926_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1926_, 0, v_a_1920_);
                    v___x_1925_ = v_reuseFailAlloc_1926_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_1925_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___boxed(
    mut v_rule_1928_: *mut crate::leanh::LeanObject,
    mut v_goal_1929_: *mut crate::leanh::LeanObject,
    mut v_ruleDesc_x3f_1930_: *mut crate::leanh::LeanObject,
    mut v_a_1931_: *mut crate::leanh::LeanObject,
    mut v_a_1932_: *mut crate::leanh::LeanObject,
    mut v_a_1933_: *mut crate::leanh::LeanObject,
    mut v_a_1934_: *mut crate::leanh::LeanObject,
    mut v_a_1935_: *mut crate::leanh::LeanObject,
    mut v_a_1936_: *mut crate::leanh::LeanObject,
    mut v_a_1937_: *mut crate::leanh::LeanObject,
    mut v_a_1938_: *mut crate::leanh::LeanObject,
    mut v_a_1939_: *mut crate::leanh::LeanObject,
    mut v_a_1940_: *mut crate::leanh::LeanObject,
    mut v_a_1941_: *mut crate::leanh::LeanObject,
    mut v_a_1942_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1943_ = l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(
        v_rule_1928_,
        v_goal_1929_,
        v_ruleDesc_x3f_1930_,
        v_a_1931_,
        v_a_1932_,
        v_a_1933_,
        v_a_1934_,
        v_a_1935_,
        v_a_1936_,
        v_a_1937_,
        v_a_1938_,
        v_a_1939_,
        v_a_1940_,
        v_a_1941_,
    );
    crate::leanh::lean_dec(v_a_1941_);
    crate::leanh::lean_dec_ref(v_a_1940_);
    crate::leanh::lean_dec(v_a_1939_);
    crate::leanh::lean_dec_ref(v_a_1938_);
    crate::leanh::lean_dec(v_a_1937_);
    crate::leanh::lean_dec_ref(v_a_1936_);
    crate::leanh::lean_dec(v_a_1935_);
    crate::leanh::lean_dec_ref(v_a_1934_);
    crate::leanh::lean_dec(v_a_1933_);
    crate::leanh::lean_dec(v_a_1932_);
    crate::leanh::lean_dec_ref(v_a_1931_);
    return v_res_1943_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1(
    mut v_00_u03b1_1944_: *mut crate::leanh::LeanObject,
    mut v_msg_1945_: *mut crate::leanh::LeanObject,
    mut v___y_1946_: *mut crate::leanh::LeanObject,
    mut v___y_1947_: *mut crate::leanh::LeanObject,
    mut v___y_1948_: *mut crate::leanh::LeanObject,
    mut v___y_1949_: *mut crate::leanh::LeanObject,
    mut v___y_1950_: *mut crate::leanh::LeanObject,
    mut v___y_1951_: *mut crate::leanh::LeanObject,
    mut v___y_1952_: *mut crate::leanh::LeanObject,
    mut v___y_1953_: *mut crate::leanh::LeanObject,
    mut v___y_1954_: *mut crate::leanh::LeanObject,
    mut v___y_1955_: *mut crate::leanh::LeanObject,
    mut v___y_1956_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1958_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg(v_msg_1945_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_);
    return v___x_1958_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___boxed(
    mut v_00_u03b1_1959_: *mut crate::leanh::LeanObject,
    mut v_msg_1960_: *mut crate::leanh::LeanObject,
    mut v___y_1961_: *mut crate::leanh::LeanObject,
    mut v___y_1962_: *mut crate::leanh::LeanObject,
    mut v___y_1963_: *mut crate::leanh::LeanObject,
    mut v___y_1964_: *mut crate::leanh::LeanObject,
    mut v___y_1965_: *mut crate::leanh::LeanObject,
    mut v___y_1966_: *mut crate::leanh::LeanObject,
    mut v___y_1967_: *mut crate::leanh::LeanObject,
    mut v___y_1968_: *mut crate::leanh::LeanObject,
    mut v___y_1969_: *mut crate::leanh::LeanObject,
    mut v___y_1970_: *mut crate::leanh::LeanObject,
    mut v___y_1971_: *mut crate::leanh::LeanObject,
    mut v___y_1972_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1973_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1(v_00_u03b1_1959_, v_msg_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_);
    crate::leanh::lean_dec(v___y_1971_);
    crate::leanh::lean_dec_ref(v___y_1970_);
    crate::leanh::lean_dec(v___y_1969_);
    crate::leanh::lean_dec_ref(v___y_1968_);
    crate::leanh::lean_dec(v___y_1967_);
    crate::leanh::lean_dec_ref(v___y_1966_);
    crate::leanh::lean_dec(v___y_1965_);
    crate::leanh::lean_dec_ref(v___y_1964_);
    crate::leanh::lean_dec(v___y_1963_);
    crate::leanh::lean_dec(v___y_1962_);
    crate::leanh::lean_dec_ref(v___y_1961_);
    return v_res_1973_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_simpTargetTelescope___redArg(
    mut v_mvarId_1978_: *mut crate::leanh::LeanObject,
    mut v_a_1979_: *mut crate::leanh::LeanObject,
    mut v_a_1980_: *mut crate::leanh::LeanObject,
    mut v_a_1981_: *mut crate::leanh::LeanObject,
    mut v_a_1982_: *mut crate::leanh::LeanObject,
    mut v_a_1983_: *mut crate::leanh::LeanObject,
    mut v_a_1984_: *mut crate::leanh::LeanObject,
    mut v_a_1985_: *mut crate::leanh::LeanObject,
    mut v_a_1986_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_hypSimpMethods_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_simpState_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_post_1994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2003_: u8 = 0;
    let mut v_fst_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2008_: u8 = 0;
    let mut v___x_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_specBackwardRuleCache_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_splitBackwardRuleCache_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invariants_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vcs_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fuel_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inlineHandledInvariants_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_preTacFailed_2016_: u8 = 0;
    let mut v___x_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2019_: u8 = 0;
    let mut v___x_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: u8 = 0;
    let mut v___x_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x27_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_2032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2037_: u8 = 0;
    let mut v___x_2038_: u8 = 0;
    let mut v___x_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2046_: u8 = 0;
    let mut v_a_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2050_: u8 = 0;
    let mut v___x_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2054_: u8 = 0;
    let mut v_reuseFailAlloc_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2056_: u8 = 0;
    let mut v_unused_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2058_: u8 = 0;
    let mut v_isSharedCheck_2059_: u8 = 0;
    let mut v_a_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2063_: u8 = 0;
    let mut v___x_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2067_: u8 = 0;
    let mut v_a_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2071_: u8 = 0;
    let mut v___x_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2075_: u8 = 0;
    let mut v___x_2076_: u8 = 0;
    let mut v___x_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_hypSimpMethods_1988_ = crate::leanh::lean_ctor_get(v_a_1979_, 16);
                if crate::leanh::lean_obj_tag(v_hypSimpMethods_1988_) == 1 {
                    v_val_1989_ = crate::leanh::lean_ctor_get(v_hypSimpMethods_1988_, 0);
                    crate::leanh::lean_inc(v_mvarId_1978_);
                    v___x_1990_ = l_Lean_MVarId_getType(
                        v_mvarId_1978_,
                        v_a_1983_,
                        v_a_1984_,
                        v_a_1985_,
                        v_a_1986_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1990_) == 0 {
                        v_a_1991_ = crate::leanh::lean_ctor_get(v___x_1990_, 0);
                        crate::leanh::lean_inc(v_a_1991_);
                        crate::leanh::lean_dec_ref_known(v___x_1990_, 1);
                        v___x_1992_ = lean_st_ref_get(v_a_1980_);
                        v_simpState_1993_ = crate::leanh::lean_ctor_get(v___x_1992_, 4);
                        crate::leanh::lean_inc_ref(v_simpState_1993_);
                        crate::leanh::lean_dec(v___x_1992_);
                        v_post_1994_ = crate::leanh::lean_ctor_get(v_val_1989_, 1);
                        v___x_1995_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_simpTargetTelescope___redArg___closed__0;
                        crate::leanh::lean_inc_ref(v_post_1994_);
                        v___x_1996_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1996_, 0, v___x_1995_);
                        crate::leanh::lean_ctor_set(v___x_1996_, 1, v_post_1994_);
                        v___x_1997_ = crate::leanh::lean_alloc_closure(
                            l_Lean_Meta_Sym_Simp_simp___boxed as *mut core::ffi::c_void,
                            11,
                            1,
                        );
                        crate::leanh::lean_closure_set(v___x_1997_, 0, v_a_1991_);
                        v___x_1998_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_simpTargetTelescope___redArg___closed__1;
                        v___x_1999_ = l_Lean_Meta_Sym_Simp_SimpM_run___redArg(
                            v___x_1997_,
                            v___x_1996_,
                            v___x_1998_,
                            v_simpState_1993_,
                            v_a_1981_,
                            v_a_1982_,
                            v_a_1983_,
                            v_a_1984_,
                            v_a_1985_,
                            v_a_1986_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1999_) == 0 {
                            v_a_2000_ = crate::leanh::lean_ctor_get(v___x_1999_, 0);
                            v_isSharedCheck_2059_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1999_)) as u8;
                            if v_isSharedCheck_2059_ == 0 {
                                v___x_2002_ = v___x_1999_;
                                v_isShared_2003_ = v_isSharedCheck_2059_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2000_);
                                crate::leanh::lean_dec(v___x_1999_);
                                v___x_2002_ = crate::leanh::lean_box(0);
                                v_isShared_2003_ = v_isSharedCheck_2059_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_mvarId_1978_);
                            v_a_2060_ = crate::leanh::lean_ctor_get(v___x_1999_, 0);
                            v_isSharedCheck_2067_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1999_)) as u8;
                            if v_isSharedCheck_2067_ == 0 {
                                v___x_2062_ = v___x_1999_;
                                v_isShared_2063_ = v_isSharedCheck_2067_;
                                state = 12;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2060_);
                                crate::leanh::lean_dec(v___x_1999_);
                                v___x_2062_ = crate::leanh::lean_box(0);
                                v_isShared_2063_ = v_isSharedCheck_2067_;
                                state = 12;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_mvarId_1978_);
                        v_a_2068_ = crate::leanh::lean_ctor_get(v___x_1990_, 0);
                        v_isSharedCheck_2075_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1990_)) as u8;
                        if v_isSharedCheck_2075_ == 0 {
                            v___x_2070_ = v___x_1990_;
                            v_isShared_2071_ = v_isSharedCheck_2075_;
                            state = 14;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2068_);
                            crate::leanh::lean_dec(v___x_1990_);
                            v___x_2070_ = crate::leanh::lean_box(0);
                            v_isShared_2071_ = v_isSharedCheck_2075_;
                            state = 14;
                            continue;
                        }
                    }
                } else {
                    v___x_2076_ = 0;
                    v___x_2077_ = crate::leanh::lean_box((v___x_2076_) as usize);
                    v___x_2078_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2078_, 0, v_mvarId_1978_);
                    crate::leanh::lean_ctor_set(v___x_2078_, 1, v___x_2077_);
                    v___x_2079_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2079_, 0, v___x_2078_);
                    return v___x_2079_;
                }
            }
            1 => {
                v_fst_2004_ = crate::leanh::lean_ctor_get(v_a_2000_, 0);
                v_snd_2005_ = crate::leanh::lean_ctor_get(v_a_2000_, 1);
                v_isSharedCheck_2058_ = (!crate::leanh::lean_is_exclusive(v_a_2000_)) as u8;
                if v_isSharedCheck_2058_ == 0 {
                    v___x_2007_ = v_a_2000_;
                    v_isShared_2008_ = v_isSharedCheck_2058_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2005_);
                    crate::leanh::lean_inc(v_fst_2004_);
                    crate::leanh::lean_dec(v_a_2000_);
                    v___x_2007_ = crate::leanh::lean_box(0);
                    v_isShared_2008_ = v_isSharedCheck_2058_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2009_ = lean_st_ref_take(v_a_1980_);
                v_specBackwardRuleCache_2010_ = crate::leanh::lean_ctor_get(v___x_2009_, 0);
                v_splitBackwardRuleCache_2011_ = crate::leanh::lean_ctor_get(v___x_2009_, 1);
                v_invariants_2012_ = crate::leanh::lean_ctor_get(v___x_2009_, 2);
                v_vcs_2013_ = crate::leanh::lean_ctor_get(v___x_2009_, 3);
                v_fuel_2014_ = crate::leanh::lean_ctor_get(v___x_2009_, 5);
                v_inlineHandledInvariants_2015_ = crate::leanh::lean_ctor_get(v___x_2009_, 6);
                v_preTacFailed_2016_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_2009_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_isSharedCheck_2056_ = (!crate::leanh::lean_is_exclusive(v___x_2009_)) as u8;
                if v_isSharedCheck_2056_ == 0 {
                    v_unused_2057_ = crate::leanh::lean_ctor_get(v___x_2009_, 4);
                    crate::leanh::lean_dec(v_unused_2057_);
                    v___x_2018_ = v___x_2009_;
                    v_isShared_2019_ = v_isSharedCheck_2056_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_inlineHandledInvariants_2015_);
                    crate::leanh::lean_inc(v_fuel_2014_);
                    crate::leanh::lean_inc(v_vcs_2013_);
                    crate::leanh::lean_inc(v_invariants_2012_);
                    crate::leanh::lean_inc(v_splitBackwardRuleCache_2011_);
                    crate::leanh::lean_inc(v_specBackwardRuleCache_2010_);
                    crate::leanh::lean_dec(v___x_2009_);
                    v___x_2018_ = crate::leanh::lean_box(0);
                    v_isShared_2019_ = v_isSharedCheck_2056_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2019_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2018_, 4, v_snd_2005_);
                    v___x_2021_ = v___x_2018_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2055_ = crate::leanh::lean_alloc_ctor(0, 7, (1) as u32);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2055_,
                        0,
                        v_specBackwardRuleCache_2010_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2055_,
                        1,
                        v_splitBackwardRuleCache_2011_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2055_, 2, v_invariants_2012_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2055_, 3, v_vcs_2013_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2055_, 4, v_snd_2005_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2055_, 5, v_fuel_2014_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2055_,
                        6,
                        v_inlineHandledInvariants_2015_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2055_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                        v_preTacFailed_2016_,
                    );
                    v___x_2021_ = v_reuseFailAlloc_2055_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2022_ = lean_st_ref_set(v_a_1980_, v___x_2021_);
                if crate::leanh::lean_obj_tag(v_fst_2004_) == 0 {
                    crate::leanh::lean_dec_ref_known(v_fst_2004_, 0);
                    v___x_2023_ = 0;
                    v___x_2024_ = crate::leanh::lean_box((v___x_2023_) as usize);
                    if v_isShared_2008_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2007_, 1, v___x_2024_);
                        crate::leanh::lean_ctor_set(v___x_2007_, 0, v_mvarId_1978_);
                        v___x_2026_ = v___x_2007_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2030_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2030_, 0, v_mvarId_1978_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2030_, 1, v___x_2024_);
                        v___x_2026_ = v_reuseFailAlloc_2030_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2002_);
                    v_e_x27_2031_ = crate::leanh::lean_ctor_get(v_fst_2004_, 0);
                    crate::leanh::lean_inc_ref(v_e_x27_2031_);
                    v_proof_2032_ = crate::leanh::lean_ctor_get(v_fst_2004_, 1);
                    crate::leanh::lean_inc_ref(v_proof_2032_);
                    crate::leanh::lean_dec_ref_known(v_fst_2004_, 2);
                    v___x_2033_ = l_Lean_MVarId_replaceTargetEq(
                        v_mvarId_1978_,
                        v_e_x27_2031_,
                        v_proof_2032_,
                        v_a_1983_,
                        v_a_1984_,
                        v_a_1985_,
                        v_a_1986_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2033_) == 0 {
                        v_a_2034_ = crate::leanh::lean_ctor_get(v___x_2033_, 0);
                        v_isSharedCheck_2046_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2033_)) as u8;
                        if v_isSharedCheck_2046_ == 0 {
                            v___x_2036_ = v___x_2033_;
                            v_isShared_2037_ = v_isSharedCheck_2046_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2034_);
                            crate::leanh::lean_dec(v___x_2033_);
                            v___x_2036_ = crate::leanh::lean_box(0);
                            v_isShared_2037_ = v_isSharedCheck_2046_;
                            state = 7;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_2007_);
                        v_a_2047_ = crate::leanh::lean_ctor_get(v___x_2033_, 0);
                        v_isSharedCheck_2054_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2033_)) as u8;
                        if v_isSharedCheck_2054_ == 0 {
                            v___x_2049_ = v___x_2033_;
                            v_isShared_2050_ = v_isSharedCheck_2054_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2047_);
                            crate::leanh::lean_dec(v___x_2033_);
                            v___x_2049_ = crate::leanh::lean_box(0);
                            v_isShared_2050_ = v_isSharedCheck_2054_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            5 => {
                if v_isShared_2003_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2002_, 0, v___x_2026_);
                    v___x_2028_ = v___x_2002_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2029_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2029_, 0, v___x_2026_);
                    v___x_2028_ = v_reuseFailAlloc_2029_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2028_;
            }
            7 => {
                v___x_2038_ = 1;
                v___x_2039_ = crate::leanh::lean_box((v___x_2038_) as usize);
                if v_isShared_2008_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2007_, 1, v___x_2039_);
                    crate::leanh::lean_ctor_set(v___x_2007_, 0, v_a_2034_);
                    v___x_2041_ = v___x_2007_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2045_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2045_, 0, v_a_2034_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2045_, 1, v___x_2039_);
                    v___x_2041_ = v_reuseFailAlloc_2045_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_2037_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2036_, 0, v___x_2041_);
                    v___x_2043_ = v___x_2036_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2044_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2044_, 0, v___x_2041_);
                    v___x_2043_ = v_reuseFailAlloc_2044_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2043_;
            }
            10 => {
                if v_isShared_2050_ == 0 {
                    v___x_2052_ = v___x_2049_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2053_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2053_, 0, v_a_2047_);
                    v___x_2052_ = v_reuseFailAlloc_2053_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2052_;
            }
            12 => {
                if v_isShared_2063_ == 0 {
                    v___x_2065_ = v___x_2062_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2066_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2066_, 0, v_a_2060_);
                    v___x_2065_ = v_reuseFailAlloc_2066_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_2065_;
            }
            14 => {
                if v_isShared_2071_ == 0 {
                    v___x_2073_ = v___x_2070_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2074_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2074_, 0, v_a_2068_);
                    v___x_2073_ = v_reuseFailAlloc_2074_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_2073_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_simpTargetTelescope___redArg___boxed(
    mut v_mvarId_2080_: *mut crate::leanh::LeanObject,
    mut v_a_2081_: *mut crate::leanh::LeanObject,
    mut v_a_2082_: *mut crate::leanh::LeanObject,
    mut v_a_2083_: *mut crate::leanh::LeanObject,
    mut v_a_2084_: *mut crate::leanh::LeanObject,
    mut v_a_2085_: *mut crate::leanh::LeanObject,
    mut v_a_2086_: *mut crate::leanh::LeanObject,
    mut v_a_2087_: *mut crate::leanh::LeanObject,
    mut v_a_2088_: *mut crate::leanh::LeanObject,
    mut v_a_2089_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2090_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_simpTargetTelescope___redArg(
        v_mvarId_2080_,
        v_a_2081_,
        v_a_2082_,
        v_a_2083_,
        v_a_2084_,
        v_a_2085_,
        v_a_2086_,
        v_a_2087_,
        v_a_2088_,
    );
    crate::leanh::lean_dec(v_a_2088_);
    crate::leanh::lean_dec_ref(v_a_2087_);
    crate::leanh::lean_dec(v_a_2086_);
    crate::leanh::lean_dec_ref(v_a_2085_);
    crate::leanh::lean_dec(v_a_2084_);
    crate::leanh::lean_dec_ref(v_a_2083_);
    crate::leanh::lean_dec(v_a_2082_);
    crate::leanh::lean_dec_ref(v_a_2081_);
    return v_res_2090_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_simpTargetTelescope(
    mut v_mvarId_2091_: *mut crate::leanh::LeanObject,
    mut v_a_2092_: *mut crate::leanh::LeanObject,
    mut v_a_2093_: *mut crate::leanh::LeanObject,
    mut v_a_2094_: *mut crate::leanh::LeanObject,
    mut v_a_2095_: *mut crate::leanh::LeanObject,
    mut v_a_2096_: *mut crate::leanh::LeanObject,
    mut v_a_2097_: *mut crate::leanh::LeanObject,
    mut v_a_2098_: *mut crate::leanh::LeanObject,
    mut v_a_2099_: *mut crate::leanh::LeanObject,
    mut v_a_2100_: *mut crate::leanh::LeanObject,
    mut v_a_2101_: *mut crate::leanh::LeanObject,
    mut v_a_2102_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2104_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_simpTargetTelescope___redArg(
        v_mvarId_2091_,
        v_a_2092_,
        v_a_2093_,
        v_a_2097_,
        v_a_2098_,
        v_a_2099_,
        v_a_2100_,
        v_a_2101_,
        v_a_2102_,
    );
    return v___x_2104_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_simpTargetTelescope___boxed(
    mut v_mvarId_2105_: *mut crate::leanh::LeanObject,
    mut v_a_2106_: *mut crate::leanh::LeanObject,
    mut v_a_2107_: *mut crate::leanh::LeanObject,
    mut v_a_2108_: *mut crate::leanh::LeanObject,
    mut v_a_2109_: *mut crate::leanh::LeanObject,
    mut v_a_2110_: *mut crate::leanh::LeanObject,
    mut v_a_2111_: *mut crate::leanh::LeanObject,
    mut v_a_2112_: *mut crate::leanh::LeanObject,
    mut v_a_2113_: *mut crate::leanh::LeanObject,
    mut v_a_2114_: *mut crate::leanh::LeanObject,
    mut v_a_2115_: *mut crate::leanh::LeanObject,
    mut v_a_2116_: *mut crate::leanh::LeanObject,
    mut v_a_2117_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2118_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_simpTargetTelescope(
        v_mvarId_2105_,
        v_a_2106_,
        v_a_2107_,
        v_a_2108_,
        v_a_2109_,
        v_a_2110_,
        v_a_2111_,
        v_a_2112_,
        v_a_2113_,
        v_a_2114_,
        v_a_2115_,
        v_a_2116_,
    );
    crate::leanh::lean_dec(v_a_2116_);
    crate::leanh::lean_dec_ref(v_a_2115_);
    crate::leanh::lean_dec(v_a_2114_);
    crate::leanh::lean_dec_ref(v_a_2113_);
    crate::leanh::lean_dec(v_a_2112_);
    crate::leanh::lean_dec_ref(v_a_2111_);
    crate::leanh::lean_dec(v_a_2110_);
    crate::leanh::lean_dec_ref(v_a_2109_);
    crate::leanh::lean_dec(v_a_2108_);
    crate::leanh::lean_dec(v_a_2107_);
    crate::leanh::lean_dec_ref(v_a_2106_);
    return v_res_2118_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2122_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__1;
    v___x_2123_ = l_Lean_stringToMessageData(v___x_2122_);
    return v___x_2123_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2125_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__3;
    v___x_2126_ = l_Lean_stringToMessageData(v___x_2125_);
    return v___x_2126_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2128_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__5;
    v___x_2129_ = l_Lean_stringToMessageData(v___x_2128_);
    return v___x_2129_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg(
    mut v_mvarId_2130_: *mut crate::leanh::LeanObject,
    mut v_errorMsg_2131_: *mut crate::leanh::LeanObject,
    mut v_a_2132_: *mut crate::leanh::LeanObject,
    mut v_a_2133_: *mut crate::leanh::LeanObject,
    mut v_a_2134_: *mut crate::leanh::LeanObject,
    mut v_a_2135_: *mut crate::leanh::LeanObject,
    mut v_a_2136_: *mut crate::leanh::LeanObject,
    mut v_a_2137_: *mut crate::leanh::LeanObject,
    mut v_a_2138_: *mut crate::leanh::LeanObject,
    mut v_a_2139_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2147_: u8 = 0;
    let mut v___x_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2153_: u8 = 0;
    let mut v___x_2154_: u8 = 0;
    let mut v___x_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2173_: u8 = 0;
    let mut v_a_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2177_: u8 = 0;
    let mut v___x_2179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2181_: u8 = 0;
    let mut v_isSharedCheck_2182_: u8 = 0;
    let mut v_a_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2186_: u8 = 0;
    let mut v___x_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2190_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2141_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_simpTargetTelescope___redArg(
                    v_mvarId_2130_,
                    v_a_2132_,
                    v_a_2133_,
                    v_a_2134_,
                    v_a_2135_,
                    v_a_2136_,
                    v_a_2137_,
                    v_a_2138_,
                    v_a_2139_,
                );
                if crate::leanh::lean_obj_tag(v___x_2141_) == 0 {
                    v_a_2142_ = crate::leanh::lean_ctor_get(v___x_2141_, 0);
                    crate::leanh::lean_inc(v_a_2142_);
                    crate::leanh::lean_dec_ref_known(v___x_2141_, 1);
                    v_fst_2143_ = crate::leanh::lean_ctor_get(v_a_2142_, 0);
                    v_snd_2144_ = crate::leanh::lean_ctor_get(v_a_2142_, 1);
                    v_isSharedCheck_2182_ = (!crate::leanh::lean_is_exclusive(v_a_2142_)) as u8;
                    if v_isSharedCheck_2182_ == 0 {
                        v___x_2146_ = v_a_2142_;
                        v_isShared_2147_ = v_isSharedCheck_2182_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2144_);
                        crate::leanh::lean_inc(v_fst_2143_);
                        crate::leanh::lean_dec(v_a_2142_);
                        v___x_2146_ = crate::leanh::lean_box(0);
                        v_isShared_2147_ = v_isSharedCheck_2182_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_errorMsg_2131_);
                    v_a_2183_ = crate::leanh::lean_ctor_get(v___x_2141_, 0);
                    v_isSharedCheck_2190_ = (!crate::leanh::lean_is_exclusive(v___x_2141_)) as u8;
                    if v_isSharedCheck_2190_ == 0 {
                        v___x_2185_ = v___x_2141_;
                        v_isShared_2186_ = v_isSharedCheck_2190_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2183_);
                        crate::leanh::lean_dec(v___x_2141_);
                        v___x_2185_ = crate::leanh::lean_box(0);
                        v_isShared_2186_ = v_isSharedCheck_2190_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2148_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__0;
                crate::leanh::lean_inc(v_fst_2143_);
                v___x_2149_ = l_Lean_Meta_Sym_intros(
                    v_fst_2143_,
                    v___x_2148_,
                    v_a_2134_,
                    v_a_2135_,
                    v_a_2136_,
                    v_a_2137_,
                    v_a_2138_,
                    v_a_2139_,
                );
                if crate::leanh::lean_obj_tag(v___x_2149_) == 0 {
                    v_a_2150_ = crate::leanh::lean_ctor_get(v___x_2149_, 0);
                    v_isSharedCheck_2173_ = (!crate::leanh::lean_is_exclusive(v___x_2149_)) as u8;
                    if v_isSharedCheck_2173_ == 0 {
                        v___x_2152_ = v___x_2149_;
                        v_isShared_2153_ = v_isSharedCheck_2173_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2150_);
                        crate::leanh::lean_dec(v___x_2149_);
                        v___x_2152_ = crate::leanh::lean_box(0);
                        v_isShared_2153_ = v_isSharedCheck_2173_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2146_);
                    crate::leanh::lean_dec(v_snd_2144_);
                    crate::leanh::lean_dec(v_fst_2143_);
                    crate::leanh::lean_dec_ref(v_errorMsg_2131_);
                    v_a_2174_ = crate::leanh::lean_ctor_get(v___x_2149_, 0);
                    v_isSharedCheck_2181_ = (!crate::leanh::lean_is_exclusive(v___x_2149_)) as u8;
                    if v_isSharedCheck_2181_ == 0 {
                        v___x_2176_ = v___x_2149_;
                        v_isShared_2177_ = v_isSharedCheck_2181_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2174_);
                        crate::leanh::lean_dec(v___x_2149_);
                        v___x_2176_ = crate::leanh::lean_box(0);
                        v_isShared_2177_ = v_isSharedCheck_2181_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_2150_) == 0 {
                    v___x_2154_ = (crate::leanh::lean_unbox(v_snd_2144_) as u8);
                    crate::leanh::lean_dec(v_snd_2144_);
                    if v___x_2154_ == 0 {
                        crate::leanh::lean_del_object(v___x_2152_);
                        v___x_2155_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__2_once), _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__2);
                        v___x_2156_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2156_, 0, v_fst_2143_);
                        if v_isShared_2147_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_2146_, 7);
                            crate::leanh::lean_ctor_set(v___x_2146_, 1, v___x_2156_);
                            crate::leanh::lean_ctor_set(v___x_2146_, 0, v___x_2155_);
                            v___x_2158_ = v___x_2146_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2165_ =
                                crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2165_, 0, v___x_2155_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2165_, 1, v___x_2156_);
                            v___x_2158_ = v_reuseFailAlloc_2165_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_2146_);
                        crate::leanh::lean_dec_ref(v_errorMsg_2131_);
                        if v_isShared_2153_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2152_, 0, v_fst_2143_);
                            v___x_2167_ = v___x_2152_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2168_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2168_, 0, v_fst_2143_);
                            v___x_2167_ = v_reuseFailAlloc_2168_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2146_);
                    crate::leanh::lean_dec(v_snd_2144_);
                    crate::leanh::lean_dec(v_fst_2143_);
                    crate::leanh::lean_dec_ref(v_errorMsg_2131_);
                    v_mvarId_2169_ = crate::leanh::lean_ctor_get(v_a_2150_, 1);
                    crate::leanh::lean_inc(v_mvarId_2169_);
                    crate::leanh::lean_dec_ref_known(v_a_2150_, 2);
                    if v_isShared_2153_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2152_, 0, v_mvarId_2169_);
                        v___x_2171_ = v___x_2152_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2172_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2172_, 0, v_mvarId_2169_);
                        v___x_2171_ = v_reuseFailAlloc_2172_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                v___x_2159_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__4
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__4_once
                    ),
                    _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__4,
                );
                v___x_2160_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2160_, 0, v___x_2158_);
                crate::leanh::lean_ctor_set(v___x_2160_, 1, v___x_2159_);
                v___x_2161_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2161_, 0, v___x_2160_);
                crate::leanh::lean_ctor_set(v___x_2161_, 1, v_errorMsg_2131_);
                v___x_2162_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__6
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__6_once
                    ),
                    _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__6,
                );
                v___x_2163_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2163_, 0, v___x_2161_);
                crate::leanh::lean_ctor_set(v___x_2163_, 1, v___x_2162_);
                v___x_2164_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg(v___x_2163_, v_a_2136_, v_a_2137_, v_a_2138_, v_a_2139_);
                return v___x_2164_;
            }
            4 => {
                return v___x_2167_;
            }
            5 => {
                return v___x_2171_;
            }
            6 => {
                if v_isShared_2177_ == 0 {
                    v___x_2179_ = v___x_2176_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2180_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2180_, 0, v_a_2174_);
                    v___x_2179_ = v_reuseFailAlloc_2180_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2179_;
            }
            8 => {
                if v_isShared_2186_ == 0 {
                    v___x_2188_ = v___x_2185_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2189_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2189_, 0, v_a_2183_);
                    v___x_2188_ = v_reuseFailAlloc_2189_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2188_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___boxed(
    mut v_mvarId_2191_: *mut crate::leanh::LeanObject,
    mut v_errorMsg_2192_: *mut crate::leanh::LeanObject,
    mut v_a_2193_: *mut crate::leanh::LeanObject,
    mut v_a_2194_: *mut crate::leanh::LeanObject,
    mut v_a_2195_: *mut crate::leanh::LeanObject,
    mut v_a_2196_: *mut crate::leanh::LeanObject,
    mut v_a_2197_: *mut crate::leanh::LeanObject,
    mut v_a_2198_: *mut crate::leanh::LeanObject,
    mut v_a_2199_: *mut crate::leanh::LeanObject,
    mut v_a_2200_: *mut crate::leanh::LeanObject,
    mut v_a_2201_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2202_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg(
        v_mvarId_2191_,
        v_errorMsg_2192_,
        v_a_2193_,
        v_a_2194_,
        v_a_2195_,
        v_a_2196_,
        v_a_2197_,
        v_a_2198_,
        v_a_2199_,
        v_a_2200_,
    );
    crate::leanh::lean_dec(v_a_2200_);
    crate::leanh::lean_dec_ref(v_a_2199_);
    crate::leanh::lean_dec(v_a_2198_);
    crate::leanh::lean_dec_ref(v_a_2197_);
    crate::leanh::lean_dec(v_a_2196_);
    crate::leanh::lean_dec_ref(v_a_2195_);
    crate::leanh::lean_dec(v_a_2194_);
    crate::leanh::lean_dec_ref(v_a_2193_);
    return v_res_2202_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp(
    mut v_mvarId_2203_: *mut crate::leanh::LeanObject,
    mut v_errorMsg_2204_: *mut crate::leanh::LeanObject,
    mut v_a_2205_: *mut crate::leanh::LeanObject,
    mut v_a_2206_: *mut crate::leanh::LeanObject,
    mut v_a_2207_: *mut crate::leanh::LeanObject,
    mut v_a_2208_: *mut crate::leanh::LeanObject,
    mut v_a_2209_: *mut crate::leanh::LeanObject,
    mut v_a_2210_: *mut crate::leanh::LeanObject,
    mut v_a_2211_: *mut crate::leanh::LeanObject,
    mut v_a_2212_: *mut crate::leanh::LeanObject,
    mut v_a_2213_: *mut crate::leanh::LeanObject,
    mut v_a_2214_: *mut crate::leanh::LeanObject,
    mut v_a_2215_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2217_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg(
        v_mvarId_2203_,
        v_errorMsg_2204_,
        v_a_2205_,
        v_a_2206_,
        v_a_2210_,
        v_a_2211_,
        v_a_2212_,
        v_a_2213_,
        v_a_2214_,
        v_a_2215_,
    );
    return v___x_2217_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___boxed(
    mut v_mvarId_2218_: *mut crate::leanh::LeanObject,
    mut v_errorMsg_2219_: *mut crate::leanh::LeanObject,
    mut v_a_2220_: *mut crate::leanh::LeanObject,
    mut v_a_2221_: *mut crate::leanh::LeanObject,
    mut v_a_2222_: *mut crate::leanh::LeanObject,
    mut v_a_2223_: *mut crate::leanh::LeanObject,
    mut v_a_2224_: *mut crate::leanh::LeanObject,
    mut v_a_2225_: *mut crate::leanh::LeanObject,
    mut v_a_2226_: *mut crate::leanh::LeanObject,
    mut v_a_2227_: *mut crate::leanh::LeanObject,
    mut v_a_2228_: *mut crate::leanh::LeanObject,
    mut v_a_2229_: *mut crate::leanh::LeanObject,
    mut v_a_2230_: *mut crate::leanh::LeanObject,
    mut v_a_2231_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2232_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp(
        v_mvarId_2218_,
        v_errorMsg_2219_,
        v_a_2220_,
        v_a_2221_,
        v_a_2222_,
        v_a_2223_,
        v_a_2224_,
        v_a_2225_,
        v_a_2226_,
        v_a_2227_,
        v_a_2228_,
        v_a_2229_,
        v_a_2230_,
    );
    crate::leanh::lean_dec(v_a_2230_);
    crate::leanh::lean_dec_ref(v_a_2229_);
    crate::leanh::lean_dec(v_a_2228_);
    crate::leanh::lean_dec_ref(v_a_2227_);
    crate::leanh::lean_dec(v_a_2226_);
    crate::leanh::lean_dec_ref(v_a_2225_);
    crate::leanh::lean_dec(v_a_2224_);
    crate::leanh::lean_dec_ref(v_a_2223_);
    crate::leanh::lean_dec(v_a_2222_);
    crate::leanh::lean_dec(v_a_2221_);
    crate::leanh::lean_dec_ref(v_a_2220_);
    return v_res_2232_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_processHypotheses___redArg(
    mut v_preTac_2233_: *mut crate::leanh::LeanObject,
    mut v_goal_2234_: *mut crate::leanh::LeanObject,
    mut v_a_2235_: *mut crate::leanh::LeanObject,
    mut v_a_2236_: *mut crate::leanh::LeanObject,
    mut v_a_2237_: *mut crate::leanh::LeanObject,
    mut v_a_2238_: *mut crate::leanh::LeanObject,
    mut v_a_2239_: *mut crate::leanh::LeanObject,
    mut v_a_2240_: *mut crate::leanh::LeanObject,
    mut v_a_2241_: *mut crate::leanh::LeanObject,
    mut v_a_2242_: *mut crate::leanh::LeanObject,
    mut v_a_2243_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2245_: u8 = 0;
    v___x_2245_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_isGrind(v_preTac_2233_);
    if v___x_2245_ == 0 {
        let mut v___x_2246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2246_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2246_, 0, v_goal_2234_);
        return v___x_2246_;
    } else {
        let mut v___x_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2247_ = crate::leanh::lean_box(0);
        v___x_2248_ = l_Lean_Meta_Grind_processHypotheses(
            v_goal_2234_,
            v___x_2247_,
            v_a_2235_,
            v_a_2236_,
            v_a_2237_,
            v_a_2238_,
            v_a_2239_,
            v_a_2240_,
            v_a_2241_,
            v_a_2242_,
            v_a_2243_,
        );
        return v___x_2248_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_processHypotheses___redArg___boxed(
    mut v_preTac_2249_: *mut crate::leanh::LeanObject,
    mut v_goal_2250_: *mut crate::leanh::LeanObject,
    mut v_a_2251_: *mut crate::leanh::LeanObject,
    mut v_a_2252_: *mut crate::leanh::LeanObject,
    mut v_a_2253_: *mut crate::leanh::LeanObject,
    mut v_a_2254_: *mut crate::leanh::LeanObject,
    mut v_a_2255_: *mut crate::leanh::LeanObject,
    mut v_a_2256_: *mut crate::leanh::LeanObject,
    mut v_a_2257_: *mut crate::leanh::LeanObject,
    mut v_a_2258_: *mut crate::leanh::LeanObject,
    mut v_a_2259_: *mut crate::leanh::LeanObject,
    mut v_a_2260_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2261_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_processHypotheses___redArg(
        v_preTac_2249_,
        v_goal_2250_,
        v_a_2251_,
        v_a_2252_,
        v_a_2253_,
        v_a_2254_,
        v_a_2255_,
        v_a_2256_,
        v_a_2257_,
        v_a_2258_,
        v_a_2259_,
    );
    crate::leanh::lean_dec(v_a_2259_);
    crate::leanh::lean_dec_ref(v_a_2258_);
    crate::leanh::lean_dec(v_a_2257_);
    crate::leanh::lean_dec_ref(v_a_2256_);
    crate::leanh::lean_dec(v_a_2255_);
    crate::leanh::lean_dec_ref(v_a_2254_);
    crate::leanh::lean_dec(v_a_2253_);
    crate::leanh::lean_dec_ref(v_a_2252_);
    crate::leanh::lean_dec(v_a_2251_);
    crate::leanh::lean_dec(v_preTac_2249_);
    return v_res_2261_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_processHypotheses(
    mut v_preTac_2262_: *mut crate::leanh::LeanObject,
    mut v_goal_2263_: *mut crate::leanh::LeanObject,
    mut v_a_2264_: *mut crate::leanh::LeanObject,
    mut v_a_2265_: *mut crate::leanh::LeanObject,
    mut v_a_2266_: *mut crate::leanh::LeanObject,
    mut v_a_2267_: *mut crate::leanh::LeanObject,
    mut v_a_2268_: *mut crate::leanh::LeanObject,
    mut v_a_2269_: *mut crate::leanh::LeanObject,
    mut v_a_2270_: *mut crate::leanh::LeanObject,
    mut v_a_2271_: *mut crate::leanh::LeanObject,
    mut v_a_2272_: *mut crate::leanh::LeanObject,
    mut v_a_2273_: *mut crate::leanh::LeanObject,
    mut v_a_2274_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2276_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_processHypotheses___redArg(
        v_preTac_2262_,
        v_goal_2263_,
        v_a_2266_,
        v_a_2267_,
        v_a_2268_,
        v_a_2269_,
        v_a_2270_,
        v_a_2271_,
        v_a_2272_,
        v_a_2273_,
        v_a_2274_,
    );
    return v___x_2276_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_processHypotheses___boxed(
    mut v_preTac_2277_: *mut crate::leanh::LeanObject,
    mut v_goal_2278_: *mut crate::leanh::LeanObject,
    mut v_a_2279_: *mut crate::leanh::LeanObject,
    mut v_a_2280_: *mut crate::leanh::LeanObject,
    mut v_a_2281_: *mut crate::leanh::LeanObject,
    mut v_a_2282_: *mut crate::leanh::LeanObject,
    mut v_a_2283_: *mut crate::leanh::LeanObject,
    mut v_a_2284_: *mut crate::leanh::LeanObject,
    mut v_a_2285_: *mut crate::leanh::LeanObject,
    mut v_a_2286_: *mut crate::leanh::LeanObject,
    mut v_a_2287_: *mut crate::leanh::LeanObject,
    mut v_a_2288_: *mut crate::leanh::LeanObject,
    mut v_a_2289_: *mut crate::leanh::LeanObject,
    mut v_a_2290_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2291_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_processHypotheses(
        v_preTac_2277_,
        v_goal_2278_,
        v_a_2279_,
        v_a_2280_,
        v_a_2281_,
        v_a_2282_,
        v_a_2283_,
        v_a_2284_,
        v_a_2285_,
        v_a_2286_,
        v_a_2287_,
        v_a_2288_,
        v_a_2289_,
    );
    crate::leanh::lean_dec(v_a_2289_);
    crate::leanh::lean_dec_ref(v_a_2288_);
    crate::leanh::lean_dec(v_a_2287_);
    crate::leanh::lean_dec_ref(v_a_2286_);
    crate::leanh::lean_dec(v_a_2285_);
    crate::leanh::lean_dec_ref(v_a_2284_);
    crate::leanh::lean_dec(v_a_2283_);
    crate::leanh::lean_dec_ref(v_a_2282_);
    crate::leanh::lean_dec(v_a_2281_);
    crate::leanh::lean_dec(v_a_2280_);
    crate::leanh::lean_dec_ref(v_a_2279_);
    crate::leanh::lean_dec(v_preTac_2277_);
    return v_res_2291_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__0___redArg(
    mut v_e_2292_: *mut crate::leanh::LeanObject,
    mut v___y_2293_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2295_: u8 = 0;
    let mut v___x_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_2305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2309_: u8 = 0;
    let mut v___x_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2315_: u8 = 0;
    let mut v_unused_2316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2295_ = l_Lean_Expr_hasMVar(v_e_2292_);
                if v___x_2295_ == 0 {
                    v___x_2296_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2296_, 0, v_e_2292_);
                    return v___x_2296_;
                } else {
                    v___x_2297_ = lean_st_ref_get(v___y_2293_);
                    v_mctx_2298_ = crate::leanh::lean_ctor_get(v___x_2297_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_2298_);
                    crate::leanh::lean_dec(v___x_2297_);
                    v___x_2299_ = l_Lean_instantiateMVarsCore(v_mctx_2298_, v_e_2292_);
                    v_fst_2300_ = crate::leanh::lean_ctor_get(v___x_2299_, 0);
                    crate::leanh::lean_inc(v_fst_2300_);
                    v_snd_2301_ = crate::leanh::lean_ctor_get(v___x_2299_, 1);
                    crate::leanh::lean_inc(v_snd_2301_);
                    crate::leanh::lean_dec_ref(v___x_2299_);
                    v___x_2302_ = lean_st_ref_take(v___y_2293_);
                    v_cache_2303_ = crate::leanh::lean_ctor_get(v___x_2302_, 1);
                    v_zetaDeltaFVarIds_2304_ = crate::leanh::lean_ctor_get(v___x_2302_, 2);
                    v_postponed_2305_ = crate::leanh::lean_ctor_get(v___x_2302_, 3);
                    v_diag_2306_ = crate::leanh::lean_ctor_get(v___x_2302_, 4);
                    v_isSharedCheck_2315_ = (!crate::leanh::lean_is_exclusive(v___x_2302_)) as u8;
                    if v_isSharedCheck_2315_ == 0 {
                        v_unused_2316_ = crate::leanh::lean_ctor_get(v___x_2302_, 0);
                        crate::leanh::lean_dec(v_unused_2316_);
                        v___x_2308_ = v___x_2302_;
                        v_isShared_2309_ = v_isSharedCheck_2315_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_2306_);
                        crate::leanh::lean_inc(v_postponed_2305_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_2304_);
                        crate::leanh::lean_inc(v_cache_2303_);
                        crate::leanh::lean_dec(v___x_2302_);
                        v___x_2308_ = crate::leanh::lean_box(0);
                        v_isShared_2309_ = v_isSharedCheck_2315_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2309_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2308_, 0, v_snd_2301_);
                    v___x_2311_ = v___x_2308_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2314_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2314_, 0, v_snd_2301_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2314_, 1, v_cache_2303_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2314_,
                        2,
                        v_zetaDeltaFVarIds_2304_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2314_, 3, v_postponed_2305_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2314_, 4, v_diag_2306_);
                    v___x_2311_ = v_reuseFailAlloc_2314_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2312_ = lean_st_ref_set(v___y_2293_, v___x_2311_);
                v___x_2313_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2313_, 0, v_fst_2300_);
                return v___x_2313_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__0___redArg___boxed(
    mut v_e_2317_: *mut crate::leanh::LeanObject,
    mut v___y_2318_: *mut crate::leanh::LeanObject,
    mut v___y_2319_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2320_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__0___redArg(v_e_2317_, v___y_2318_);
    crate::leanh::lean_dec(v___y_2318_);
    return v_res_2320_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__0(
    mut v_e_2321_: *mut crate::leanh::LeanObject,
    mut v___y_2322_: *mut crate::leanh::LeanObject,
    mut v___y_2323_: *mut crate::leanh::LeanObject,
    mut v___y_2324_: *mut crate::leanh::LeanObject,
    mut v___y_2325_: *mut crate::leanh::LeanObject,
    mut v___y_2326_: *mut crate::leanh::LeanObject,
    mut v___y_2327_: *mut crate::leanh::LeanObject,
    mut v___y_2328_: *mut crate::leanh::LeanObject,
    mut v___y_2329_: *mut crate::leanh::LeanObject,
    mut v___y_2330_: *mut crate::leanh::LeanObject,
    mut v___y_2331_: *mut crate::leanh::LeanObject,
    mut v___y_2332_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2334_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__0___redArg(v_e_2321_, v___y_2330_);
    return v___x_2334_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__0___boxed(
    mut v_e_2335_: *mut crate::leanh::LeanObject,
    mut v___y_2336_: *mut crate::leanh::LeanObject,
    mut v___y_2337_: *mut crate::leanh::LeanObject,
    mut v___y_2338_: *mut crate::leanh::LeanObject,
    mut v___y_2339_: *mut crate::leanh::LeanObject,
    mut v___y_2340_: *mut crate::leanh::LeanObject,
    mut v___y_2341_: *mut crate::leanh::LeanObject,
    mut v___y_2342_: *mut crate::leanh::LeanObject,
    mut v___y_2343_: *mut crate::leanh::LeanObject,
    mut v___y_2344_: *mut crate::leanh::LeanObject,
    mut v___y_2345_: *mut crate::leanh::LeanObject,
    mut v___y_2346_: *mut crate::leanh::LeanObject,
    mut v___y_2347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2348_ =
        l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__0(
            v_e_2335_,
            v___y_2336_,
            v___y_2337_,
            v___y_2338_,
            v___y_2339_,
            v___y_2340_,
            v___y_2341_,
            v___y_2342_,
            v___y_2343_,
            v___y_2344_,
            v___y_2345_,
            v___y_2346_,
        );
    crate::leanh::lean_dec(v___y_2346_);
    crate::leanh::lean_dec_ref(v___y_2345_);
    crate::leanh::lean_dec(v___y_2344_);
    crate::leanh::lean_dec_ref(v___y_2343_);
    crate::leanh::lean_dec(v___y_2342_);
    crate::leanh::lean_dec_ref(v___y_2341_);
    crate::leanh::lean_dec(v___y_2340_);
    crate::leanh::lean_dec_ref(v___y_2339_);
    crate::leanh::lean_dec(v___y_2338_);
    crate::leanh::lean_dec(v___y_2337_);
    crate::leanh::lean_dec_ref(v___y_2336_);
    return v_res_2348_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__2___redArg___lam__0(
    mut v_x_2349_: *mut crate::leanh::LeanObject,
    mut v___y_2350_: *mut crate::leanh::LeanObject,
    mut v___y_2351_: *mut crate::leanh::LeanObject,
    mut v___y_2352_: *mut crate::leanh::LeanObject,
    mut v___y_2353_: *mut crate::leanh::LeanObject,
    mut v___y_2354_: *mut crate::leanh::LeanObject,
    mut v___y_2355_: *mut crate::leanh::LeanObject,
    mut v___y_2356_: *mut crate::leanh::LeanObject,
    mut v___y_2357_: *mut crate::leanh::LeanObject,
    mut v___y_2358_: *mut crate::leanh::LeanObject,
    mut v___y_2359_: *mut crate::leanh::LeanObject,
    mut v___y_2360_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_2356_);
    crate::leanh::lean_inc_ref(v___y_2355_);
    crate::leanh::lean_inc(v___y_2354_);
    crate::leanh::lean_inc_ref(v___y_2353_);
    crate::leanh::lean_inc(v___y_2352_);
    crate::leanh::lean_inc(v___y_2351_);
    crate::leanh::lean_inc_ref(v___y_2350_);
    v___x_2362_ = crate::leanh::lean_apply_12(
        v_x_2349_,
        v___y_2350_,
        v___y_2351_,
        v___y_2352_,
        v___y_2353_,
        v___y_2354_,
        v___y_2355_,
        v___y_2356_,
        v___y_2357_,
        v___y_2358_,
        v___y_2359_,
        v___y_2360_,
        crate::leanh::lean_box(0),
    );
    return v___x_2362_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__2___redArg___lam__0___boxed(
    mut v_x_2363_: *mut crate::leanh::LeanObject,
    mut v___y_2364_: *mut crate::leanh::LeanObject,
    mut v___y_2365_: *mut crate::leanh::LeanObject,
    mut v___y_2366_: *mut crate::leanh::LeanObject,
    mut v___y_2367_: *mut crate::leanh::LeanObject,
    mut v___y_2368_: *mut crate::leanh::LeanObject,
    mut v___y_2369_: *mut crate::leanh::LeanObject,
    mut v___y_2370_: *mut crate::leanh::LeanObject,
    mut v___y_2371_: *mut crate::leanh::LeanObject,
    mut v___y_2372_: *mut crate::leanh::LeanObject,
    mut v___y_2373_: *mut crate::leanh::LeanObject,
    mut v___y_2374_: *mut crate::leanh::LeanObject,
    mut v___y_2375_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2376_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__2___redArg___lam__0(v_x_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_);
    crate::leanh::lean_dec(v___y_2370_);
    crate::leanh::lean_dec_ref(v___y_2369_);
    crate::leanh::lean_dec(v___y_2368_);
    crate::leanh::lean_dec_ref(v___y_2367_);
    crate::leanh::lean_dec(v___y_2366_);
    crate::leanh::lean_dec(v___y_2365_);
    crate::leanh::lean_dec_ref(v___y_2364_);
    return v_res_2376_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__2___redArg(
    mut v_mvarId_2377_: *mut crate::leanh::LeanObject,
    mut v_x_2378_: *mut crate::leanh::LeanObject,
    mut v___y_2379_: *mut crate::leanh::LeanObject,
    mut v___y_2380_: *mut crate::leanh::LeanObject,
    mut v___y_2381_: *mut crate::leanh::LeanObject,
    mut v___y_2382_: *mut crate::leanh::LeanObject,
    mut v___y_2383_: *mut crate::leanh::LeanObject,
    mut v___y_2384_: *mut crate::leanh::LeanObject,
    mut v___y_2385_: *mut crate::leanh::LeanObject,
    mut v___y_2386_: *mut crate::leanh::LeanObject,
    mut v___y_2387_: *mut crate::leanh::LeanObject,
    mut v___y_2388_: *mut crate::leanh::LeanObject,
    mut v___y_2389_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2396_: u8 = 0;
    let mut v___x_2398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2400_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_2385_);
                crate::leanh::lean_inc_ref(v___y_2384_);
                crate::leanh::lean_inc(v___y_2383_);
                crate::leanh::lean_inc_ref(v___y_2382_);
                crate::leanh::lean_inc(v___y_2381_);
                crate::leanh::lean_inc(v___y_2380_);
                crate::leanh::lean_inc_ref(v___y_2379_);
                v___f_2391_ = crate::leanh::lean_alloc_closure(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__2___redArg___lam__0___boxed as *mut core::ffi::c_void, 13, 8);
                crate::leanh::lean_closure_set(v___f_2391_, 0, v_x_2378_);
                crate::leanh::lean_closure_set(v___f_2391_, 1, v___y_2379_);
                crate::leanh::lean_closure_set(v___f_2391_, 2, v___y_2380_);
                crate::leanh::lean_closure_set(v___f_2391_, 3, v___y_2381_);
                crate::leanh::lean_closure_set(v___f_2391_, 4, v___y_2382_);
                crate::leanh::lean_closure_set(v___f_2391_, 5, v___y_2383_);
                crate::leanh::lean_closure_set(v___f_2391_, 6, v___y_2384_);
                crate::leanh::lean_closure_set(v___f_2391_, 7, v___y_2385_);
                v___x_2392_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    crate::leanh::lean_box(0),
                    v_mvarId_2377_,
                    v___f_2391_,
                    v___y_2386_,
                    v___y_2387_,
                    v___y_2388_,
                    v___y_2389_,
                );
                if crate::leanh::lean_obj_tag(v___x_2392_) == 0 {
                    return v___x_2392_;
                } else {
                    v_a_2393_ = crate::leanh::lean_ctor_get(v___x_2392_, 0);
                    v_isSharedCheck_2400_ = (!crate::leanh::lean_is_exclusive(v___x_2392_)) as u8;
                    if v_isSharedCheck_2400_ == 0 {
                        v___x_2395_ = v___x_2392_;
                        v_isShared_2396_ = v_isSharedCheck_2400_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2393_);
                        crate::leanh::lean_dec(v___x_2392_);
                        v___x_2395_ = crate::leanh::lean_box(0);
                        v_isShared_2396_ = v_isSharedCheck_2400_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2396_ == 0 {
                    v___x_2398_ = v___x_2395_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2399_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2399_, 0, v_a_2393_);
                    v___x_2398_ = v_reuseFailAlloc_2399_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2398_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__2___redArg___boxed(
    mut v_mvarId_2401_: *mut crate::leanh::LeanObject,
    mut v_x_2402_: *mut crate::leanh::LeanObject,
    mut v___y_2403_: *mut crate::leanh::LeanObject,
    mut v___y_2404_: *mut crate::leanh::LeanObject,
    mut v___y_2405_: *mut crate::leanh::LeanObject,
    mut v___y_2406_: *mut crate::leanh::LeanObject,
    mut v___y_2407_: *mut crate::leanh::LeanObject,
    mut v___y_2408_: *mut crate::leanh::LeanObject,
    mut v___y_2409_: *mut crate::leanh::LeanObject,
    mut v___y_2410_: *mut crate::leanh::LeanObject,
    mut v___y_2411_: *mut crate::leanh::LeanObject,
    mut v___y_2412_: *mut crate::leanh::LeanObject,
    mut v___y_2413_: *mut crate::leanh::LeanObject,
    mut v___y_2414_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2415_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__2___redArg(v_mvarId_2401_, v_x_2402_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_);
    crate::leanh::lean_dec(v___y_2413_);
    crate::leanh::lean_dec_ref(v___y_2412_);
    crate::leanh::lean_dec(v___y_2411_);
    crate::leanh::lean_dec_ref(v___y_2410_);
    crate::leanh::lean_dec(v___y_2409_);
    crate::leanh::lean_dec_ref(v___y_2408_);
    crate::leanh::lean_dec(v___y_2407_);
    crate::leanh::lean_dec_ref(v___y_2406_);
    crate::leanh::lean_dec(v___y_2405_);
    crate::leanh::lean_dec(v___y_2404_);
    crate::leanh::lean_dec_ref(v___y_2403_);
    return v_res_2415_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__2(
    mut v_00_u03b1_2416_: *mut crate::leanh::LeanObject,
    mut v_mvarId_2417_: *mut crate::leanh::LeanObject,
    mut v_x_2418_: *mut crate::leanh::LeanObject,
    mut v___y_2419_: *mut crate::leanh::LeanObject,
    mut v___y_2420_: *mut crate::leanh::LeanObject,
    mut v___y_2421_: *mut crate::leanh::LeanObject,
    mut v___y_2422_: *mut crate::leanh::LeanObject,
    mut v___y_2423_: *mut crate::leanh::LeanObject,
    mut v___y_2424_: *mut crate::leanh::LeanObject,
    mut v___y_2425_: *mut crate::leanh::LeanObject,
    mut v___y_2426_: *mut crate::leanh::LeanObject,
    mut v___y_2427_: *mut crate::leanh::LeanObject,
    mut v___y_2428_: *mut crate::leanh::LeanObject,
    mut v___y_2429_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2431_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__2___redArg(v_mvarId_2417_, v_x_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_);
    return v___x_2431_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__2___boxed(
    mut v_00_u03b1_2432_: *mut crate::leanh::LeanObject,
    mut v_mvarId_2433_: *mut crate::leanh::LeanObject,
    mut v_x_2434_: *mut crate::leanh::LeanObject,
    mut v___y_2435_: *mut crate::leanh::LeanObject,
    mut v___y_2436_: *mut crate::leanh::LeanObject,
    mut v___y_2437_: *mut crate::leanh::LeanObject,
    mut v___y_2438_: *mut crate::leanh::LeanObject,
    mut v___y_2439_: *mut crate::leanh::LeanObject,
    mut v___y_2440_: *mut crate::leanh::LeanObject,
    mut v___y_2441_: *mut crate::leanh::LeanObject,
    mut v___y_2442_: *mut crate::leanh::LeanObject,
    mut v___y_2443_: *mut crate::leanh::LeanObject,
    mut v___y_2444_: *mut crate::leanh::LeanObject,
    mut v___y_2445_: *mut crate::leanh::LeanObject,
    mut v___y_2446_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2447_ =
        l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__2(
            v_00_u03b1_2432_,
            v_mvarId_2433_,
            v_x_2434_,
            v___y_2435_,
            v___y_2436_,
            v___y_2437_,
            v___y_2438_,
            v___y_2439_,
            v___y_2440_,
            v___y_2441_,
            v___y_2442_,
            v___y_2443_,
            v___y_2444_,
            v___y_2445_,
        );
    crate::leanh::lean_dec(v___y_2445_);
    crate::leanh::lean_dec_ref(v___y_2444_);
    crate::leanh::lean_dec(v___y_2443_);
    crate::leanh::lean_dec_ref(v___y_2442_);
    crate::leanh::lean_dec(v___y_2441_);
    crate::leanh::lean_dec_ref(v___y_2440_);
    crate::leanh::lean_dec(v___y_2439_);
    crate::leanh::lean_dec_ref(v___y_2438_);
    crate::leanh::lean_dec(v___y_2437_);
    crate::leanh::lean_dec(v___y_2436_);
    crate::leanh::lean_dec_ref(v___y_2435_);
    return v_res_2447_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3_spec__4_spec__5___redArg(
    mut v_x_2448_: *mut crate::leanh::LeanObject,
    mut v_x_2449_: *mut crate::leanh::LeanObject,
    mut v_x_2450_: *mut crate::leanh::LeanObject,
    mut v_x_2451_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_2452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2456_: u8 = 0;
    let mut v___x_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: u8 = 0;
    let mut v___x_2459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: u8 = 0;
    let mut v___x_2467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2477_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_2452_ = crate::leanh::lean_ctor_get(v_x_2448_, 0);
                v_vs_2453_ = crate::leanh::lean_ctor_get(v_x_2448_, 1);
                v_isSharedCheck_2477_ = (!crate::leanh::lean_is_exclusive(v_x_2448_)) as u8;
                if v_isSharedCheck_2477_ == 0 {
                    v___x_2455_ = v_x_2448_;
                    v_isShared_2456_ = v_isSharedCheck_2477_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_2453_);
                    crate::leanh::lean_inc(v_ks_2452_);
                    crate::leanh::lean_dec(v_x_2448_);
                    v___x_2455_ = crate::leanh::lean_box(0);
                    v_isShared_2456_ = v_isSharedCheck_2477_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2457_ = lean_array_get_size(v_ks_2452_);
                v___x_2458_ = lean_nat_dec_lt(v_x_2449_, v___x_2457_);
                if v___x_2458_ == 0 {
                    crate::leanh::lean_dec(v_x_2449_);
                    v___x_2459_ = lean_array_push(v_ks_2452_, v_x_2450_);
                    v___x_2460_ = lean_array_push(v_vs_2453_, v_x_2451_);
                    if v_isShared_2456_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2455_, 1, v___x_2460_);
                        crate::leanh::lean_ctor_set(v___x_2455_, 0, v___x_2459_);
                        v___x_2462_ = v___x_2455_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2463_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2463_, 0, v___x_2459_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2463_, 1, v___x_2460_);
                        v___x_2462_ = v_reuseFailAlloc_2463_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_2464_ = lean_array_fget_borrowed(v_ks_2452_, v_x_2449_);
                    v___x_2465_ = l_Lean_instBEqMVarId_beq(v_x_2450_, v_k_x27_2464_);
                    if v___x_2465_ == 0 {
                        if v_isShared_2456_ == 0 {
                            v___x_2467_ = v___x_2455_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2471_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2471_, 0, v_ks_2452_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2471_, 1, v_vs_2453_);
                            v___x_2467_ = v_reuseFailAlloc_2471_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_2472_ = lean_array_fset(v_ks_2452_, v_x_2449_, v_x_2450_);
                        v___x_2473_ = lean_array_fset(v_vs_2453_, v_x_2449_, v_x_2451_);
                        crate::leanh::lean_dec(v_x_2449_);
                        if v_isShared_2456_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2455_, 1, v___x_2473_);
                            crate::leanh::lean_ctor_set(v___x_2455_, 0, v___x_2472_);
                            v___x_2475_ = v___x_2455_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2476_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2476_, 0, v___x_2472_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2476_, 1, v___x_2473_);
                            v___x_2475_ = v_reuseFailAlloc_2476_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_2462_;
            }
            3 => {
                v___x_2468_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2469_ = lean_nat_add(v_x_2449_, v___x_2468_);
                crate::leanh::lean_dec(v_x_2449_);
                v_x_2448_ = v___x_2467_;
                v_x_2449_ = v___x_2469_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_2475_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3_spec__4___redArg(
    mut v_n_2478_: *mut crate::leanh::LeanObject,
    mut v_k_2479_: *mut crate::leanh::LeanObject,
    mut v_v_2480_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2481_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2482_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3_spec__4_spec__5___redArg(v_n_2478_, v___x_2481_, v_k_2479_, v_v_2480_);
    return v___x_2482_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg___closed__0()
-> usize {
    let mut v___x_2483_: usize = 0;
    let mut v___x_2484_: usize = 0;
    let mut v___x_2485_: usize = 0;
    v___x_2483_ = 5usize;
    v___x_2484_ = 1usize;
    v___x_2485_ = lean_usize_shift_left(v___x_2484_, v___x_2483_);
    return v___x_2485_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg___closed__1()
-> usize {
    let mut v___x_2486_: usize = 0;
    let mut v___x_2487_: usize = 0;
    let mut v___x_2488_: usize = 0;
    v___x_2486_ = 1usize;
    v___x_2487_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg___closed__0);
    v___x_2488_ = lean_usize_sub(v___x_2487_, v___x_2486_);
    return v___x_2488_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2489_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_2489_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg(
    mut v_x_2490_: *mut crate::leanh::LeanObject,
    mut v_x_2491_: usize,
    mut v_x_2492_: usize,
    mut v_x_2493_: *mut crate::leanh::LeanObject,
    mut v_x_2494_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2496_: usize = 0;
    let mut v___x_2497_: usize = 0;
    let mut v___x_2498_: usize = 0;
    let mut v___x_2499_: usize = 0;
    let mut v_j_2500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2502_: u8 = 0;
    let mut v___x_2504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2505_: u8 = 0;
    let mut v_v_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_2508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2519_: u8 = 0;
    let mut v___x_2520_: u8 = 0;
    let mut v___x_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2526_: u8 = 0;
    let mut v_node_2527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2530_: u8 = 0;
    let mut v___x_2531_: usize = 0;
    let mut v___x_2532_: usize = 0;
    let mut v___x_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2537_: u8 = 0;
    let mut v___x_2538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2539_: u8 = 0;
    let mut v_unused_2540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_2541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2545_: u8 = 0;
    let mut v___x_2547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_2548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2550_: u8 = 0;
    let mut v_ks_2551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: usize = 0;
    let mut v___x_2557_: u8 = 0;
    let mut v___x_2558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: u8 = 0;
    let mut v_reuseFailAlloc_2561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2562_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2490_) == 0 {
                    v_es_2495_ = crate::leanh::lean_ctor_get(v_x_2490_, 0);
                    v___x_2496_ = 5usize;
                    v___x_2497_ = 1usize;
                    v___x_2498_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg___closed__1);
                    v___x_2499_ = lean_usize_land(v_x_2491_, v___x_2498_);
                    v_j_2500_ = lean_usize_to_nat(v___x_2499_);
                    v___x_2501_ = lean_array_get_size(v_es_2495_);
                    v___x_2502_ = lean_nat_dec_lt(v_j_2500_, v___x_2501_);
                    if v___x_2502_ == 0 {
                        crate::leanh::lean_dec(v_j_2500_);
                        crate::leanh::lean_dec(v_x_2494_);
                        crate::leanh::lean_dec(v_x_2493_);
                        return v_x_2490_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_2495_);
                        v_isSharedCheck_2539_ = (!crate::leanh::lean_is_exclusive(v_x_2490_)) as u8;
                        if v_isSharedCheck_2539_ == 0 {
                            v_unused_2540_ = crate::leanh::lean_ctor_get(v_x_2490_, 0);
                            crate::leanh::lean_dec(v_unused_2540_);
                            v___x_2504_ = v_x_2490_;
                            v_isShared_2505_ = v_isSharedCheck_2539_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_2490_);
                            v___x_2504_ = crate::leanh::lean_box(0);
                            v_isShared_2505_ = v_isSharedCheck_2539_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_2541_ = crate::leanh::lean_ctor_get(v_x_2490_, 0);
                    v_vs_2542_ = crate::leanh::lean_ctor_get(v_x_2490_, 1);
                    v_isSharedCheck_2562_ = (!crate::leanh::lean_is_exclusive(v_x_2490_)) as u8;
                    if v_isSharedCheck_2562_ == 0 {
                        v___x_2544_ = v_x_2490_;
                        v_isShared_2545_ = v_isSharedCheck_2562_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_2542_);
                        crate::leanh::lean_inc(v_ks_2541_);
                        crate::leanh::lean_dec(v_x_2490_);
                        v___x_2544_ = crate::leanh::lean_box(0);
                        v_isShared_2545_ = v_isSharedCheck_2562_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_2506_ = lean_array_fget(v_es_2495_, v_j_2500_);
                v___x_2507_ = crate::leanh::lean_box(0);
                v_xs_x27_2508_ = lean_array_fset(v_es_2495_, v_j_2500_, v___x_2507_);
                match crate::leanh::lean_obj_tag(v_v_2506_) {
                    0 => {
                        v_key_2515_ = crate::leanh::lean_ctor_get(v_v_2506_, 0);
                        v_val_2516_ = crate::leanh::lean_ctor_get(v_v_2506_, 1);
                        v_isSharedCheck_2526_ = (!crate::leanh::lean_is_exclusive(v_v_2506_)) as u8;
                        if v_isSharedCheck_2526_ == 0 {
                            v___x_2518_ = v_v_2506_;
                            v_isShared_2519_ = v_isSharedCheck_2526_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_2516_);
                            crate::leanh::lean_inc(v_key_2515_);
                            crate::leanh::lean_dec(v_v_2506_);
                            v___x_2518_ = crate::leanh::lean_box(0);
                            v_isShared_2519_ = v_isSharedCheck_2526_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_2527_ = crate::leanh::lean_ctor_get(v_v_2506_, 0);
                        v_isSharedCheck_2537_ = (!crate::leanh::lean_is_exclusive(v_v_2506_)) as u8;
                        if v_isSharedCheck_2537_ == 0 {
                            v___x_2529_ = v_v_2506_;
                            v_isShared_2530_ = v_isSharedCheck_2537_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_2527_);
                            crate::leanh::lean_dec(v_v_2506_);
                            v___x_2529_ = crate::leanh::lean_box(0);
                            v_isShared_2530_ = v_isSharedCheck_2537_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_2538_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2538_, 0, v_x_2493_);
                        crate::leanh::lean_ctor_set(v___x_2538_, 1, v_x_2494_);
                        v___y_2510_ = v___x_2538_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2511_ = lean_array_fset(v_xs_x27_2508_, v_j_2500_, v___y_2510_);
                crate::leanh::lean_dec(v_j_2500_);
                if v_isShared_2505_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2504_, 0, v___x_2511_);
                    v___x_2513_ = v___x_2504_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2514_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2514_, 0, v___x_2511_);
                    v___x_2513_ = v_reuseFailAlloc_2514_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2513_;
            }
            4 => {
                v___x_2520_ = l_Lean_instBEqMVarId_beq(v_x_2493_, v_key_2515_);
                if v___x_2520_ == 0 {
                    crate::leanh::lean_del_object(v___x_2518_);
                    v___x_2521_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_2515_,
                        v_val_2516_,
                        v_x_2493_,
                        v_x_2494_,
                    );
                    v___x_2522_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2522_, 0, v___x_2521_);
                    v___y_2510_ = v___x_2522_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_2516_);
                    crate::leanh::lean_dec(v_key_2515_);
                    if v_isShared_2519_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2518_, 1, v_x_2494_);
                        crate::leanh::lean_ctor_set(v___x_2518_, 0, v_x_2493_);
                        v___x_2524_ = v___x_2518_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2525_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2525_, 0, v_x_2493_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2525_, 1, v_x_2494_);
                        v___x_2524_ = v_reuseFailAlloc_2525_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_2510_ = v___x_2524_;
                state = 2;
                continue;
            }
            6 => {
                v___x_2531_ = lean_usize_shift_right(v_x_2491_, v___x_2496_);
                v___x_2532_ = lean_usize_add(v_x_2492_, v___x_2497_);
                v___x_2533_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg(v_node_2527_, v___x_2531_, v___x_2532_, v_x_2493_, v_x_2494_);
                if v_isShared_2530_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2529_, 0, v___x_2533_);
                    v___x_2535_ = v___x_2529_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2536_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2536_, 0, v___x_2533_);
                    v___x_2535_ = v_reuseFailAlloc_2536_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_2510_ = v___x_2535_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_2545_ == 0 {
                    v___x_2547_ = v___x_2544_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2561_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2561_, 0, v_ks_2541_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2561_, 1, v_vs_2542_);
                    v___x_2547_ = v_reuseFailAlloc_2561_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_2548_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3_spec__4___redArg(v___x_2547_, v_x_2493_, v_x_2494_);
                v___x_2556_ = 7usize;
                v___x_2557_ = lean_usize_dec_le(v___x_2556_, v_x_2492_);
                if v___x_2557_ == 0 {
                    v___x_2558_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2548_);
                    v___x_2559_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_2560_ = lean_nat_dec_lt(v___x_2558_, v___x_2559_);
                    crate::leanh::lean_dec(v___x_2558_);
                    v___y_2550_ = v___x_2560_;
                    state = 10;
                    continue;
                } else {
                    v___y_2550_ = v___x_2557_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_2550_ == 0 {
                    v_ks_2551_ = crate::leanh::lean_ctor_get(v_newNode_2548_, 0);
                    crate::leanh::lean_inc_ref(v_ks_2551_);
                    v_vs_2552_ = crate::leanh::lean_ctor_get(v_newNode_2548_, 1);
                    crate::leanh::lean_inc_ref(v_vs_2552_);
                    crate::leanh::lean_dec_ref(v_newNode_2548_);
                    v___x_2553_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2554_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg___closed__2);
                    v___x_2555_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3_spec__5___redArg(v_x_2492_, v_ks_2551_, v_vs_2552_, v___x_2553_, v___x_2554_);
                    crate::leanh::lean_dec_ref(v_vs_2552_);
                    crate::leanh::lean_dec_ref(v_ks_2551_);
                    return v___x_2555_;
                } else {
                    return v_newNode_2548_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3_spec__5___redArg(
    mut v_depth_2563_: usize,
    mut v_keys_2564_: *mut crate::leanh::LeanObject,
    mut v_vals_2565_: *mut crate::leanh::LeanObject,
    mut v_i_2566_: *mut crate::leanh::LeanObject,
    mut v_entries_2567_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: u8 = 0;
    let mut v_k_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: u64 = 0;
    let mut v_h_2573_: usize = 0;
    let mut v___x_2574_: usize = 0;
    let mut v___x_2575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: usize = 0;
    let mut v___x_2577_: usize = 0;
    let mut v___x_2578_: usize = 0;
    let mut v_h_2579_: usize = 0;
    let mut v___x_2580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2568_ = lean_array_get_size(v_keys_2564_);
                v___x_2569_ = lean_nat_dec_lt(v_i_2566_, v___x_2568_);
                if v___x_2569_ == 0 {
                    crate::leanh::lean_dec(v_i_2566_);
                    return v_entries_2567_;
                } else {
                    v_k_2570_ = lean_array_fget_borrowed(v_keys_2564_, v_i_2566_);
                    v_v_2571_ = lean_array_fget_borrowed(v_vals_2565_, v_i_2566_);
                    v___x_2572_ = l_Lean_instHashableMVarId_hash(v_k_2570_);
                    v_h_2573_ = lean_uint64_to_usize(v___x_2572_);
                    v___x_2574_ = 5usize;
                    v___x_2575_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2576_ = 1usize;
                    v___x_2577_ = lean_usize_sub(v_depth_2563_, v___x_2576_);
                    v___x_2578_ = lean_usize_mul(v___x_2574_, v___x_2577_);
                    v_h_2579_ = lean_usize_shift_right(v_h_2573_, v___x_2578_);
                    v___x_2580_ = lean_nat_add(v_i_2566_, v___x_2575_);
                    crate::leanh::lean_dec(v_i_2566_);
                    crate::leanh::lean_inc(v_v_2571_);
                    crate::leanh::lean_inc(v_k_2570_);
                    v___x_2581_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg(v_entries_2567_, v_h_2579_, v_depth_2563_, v_k_2570_, v_v_2571_);
                    v_i_2566_ = v___x_2580_;
                    v_entries_2567_ = v___x_2581_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3_spec__5___redArg___boxed(
    mut v_depth_2583_: *mut crate::leanh::LeanObject,
    mut v_keys_2584_: *mut crate::leanh::LeanObject,
    mut v_vals_2585_: *mut crate::leanh::LeanObject,
    mut v_i_2586_: *mut crate::leanh::LeanObject,
    mut v_entries_2587_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_2588_: usize = 0;
    let mut v_res_2589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_2588_ = crate::leanh::lean_unbox_usize(v_depth_2583_);
    crate::leanh::lean_dec(v_depth_2583_);
    v_res_2589_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3_spec__5___redArg(v_depth_boxed_2588_, v_keys_2584_, v_vals_2585_, v_i_2586_, v_entries_2587_);
    crate::leanh::lean_dec_ref(v_vals_2585_);
    crate::leanh::lean_dec_ref(v_keys_2584_);
    return v_res_2589_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg___boxed(
    mut v_x_2590_: *mut crate::leanh::LeanObject,
    mut v_x_2591_: *mut crate::leanh::LeanObject,
    mut v_x_2592_: *mut crate::leanh::LeanObject,
    mut v_x_2593_: *mut crate::leanh::LeanObject,
    mut v_x_2594_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_74839__boxed_2595_: usize = 0;
    let mut v_x_74840__boxed_2596_: usize = 0;
    let mut v_res_2597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_74839__boxed_2595_ = crate::leanh::lean_unbox_usize(v_x_2591_);
    crate::leanh::lean_dec(v_x_2591_);
    v_x_74840__boxed_2596_ = crate::leanh::lean_unbox_usize(v_x_2592_);
    crate::leanh::lean_dec(v_x_2592_);
    v_res_2597_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg(v_x_2590_, v_x_74839__boxed_2595_, v_x_74840__boxed_2596_, v_x_2593_, v_x_2594_);
    return v_res_2597_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1___redArg(
    mut v_x_2598_: *mut crate::leanh::LeanObject,
    mut v_x_2599_: *mut crate::leanh::LeanObject,
    mut v_x_2600_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2601_: u64 = 0;
    let mut v___x_2602_: usize = 0;
    let mut v___x_2603_: usize = 0;
    let mut v___x_2604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2601_ = l_Lean_instHashableMVarId_hash(v_x_2599_);
    v___x_2602_ = lean_uint64_to_usize(v___x_2601_);
    v___x_2603_ = 1usize;
    v___x_2604_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg(v_x_2598_, v___x_2602_, v___x_2603_, v_x_2599_, v_x_2600_);
    return v___x_2604_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1___redArg(
    mut v_mvarId_2605_: *mut crate::leanh::LeanObject,
    mut v_val_2606_: *mut crate::leanh::LeanObject,
    mut v___y_2607_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_2613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2617_: u8 = 0;
    let mut v_depth_2618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_2619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_2620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_2621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lDecls_2622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_2623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userNames_2624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_2625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_2626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_2627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2630_: u8 = 0;
    let mut v___x_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2641_: u8 = 0;
    let mut v_isSharedCheck_2642_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2609_ = lean_st_ref_take(v___y_2607_);
                v_mctx_2610_ = crate::leanh::lean_ctor_get(v___x_2609_, 0);
                v_cache_2611_ = crate::leanh::lean_ctor_get(v___x_2609_, 1);
                v_zetaDeltaFVarIds_2612_ = crate::leanh::lean_ctor_get(v___x_2609_, 2);
                v_postponed_2613_ = crate::leanh::lean_ctor_get(v___x_2609_, 3);
                v_diag_2614_ = crate::leanh::lean_ctor_get(v___x_2609_, 4);
                v_isSharedCheck_2642_ = (!crate::leanh::lean_is_exclusive(v___x_2609_)) as u8;
                if v_isSharedCheck_2642_ == 0 {
                    v___x_2616_ = v___x_2609_;
                    v_isShared_2617_ = v_isSharedCheck_2642_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_2614_);
                    crate::leanh::lean_inc(v_postponed_2613_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_2612_);
                    crate::leanh::lean_inc(v_cache_2611_);
                    crate::leanh::lean_inc(v_mctx_2610_);
                    crate::leanh::lean_dec(v___x_2609_);
                    v___x_2616_ = crate::leanh::lean_box(0);
                    v_isShared_2617_ = v_isSharedCheck_2642_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_2618_ = crate::leanh::lean_ctor_get(v_mctx_2610_, 0);
                v_levelAssignDepth_2619_ = crate::leanh::lean_ctor_get(v_mctx_2610_, 1);
                v_lmvarCounter_2620_ = crate::leanh::lean_ctor_get(v_mctx_2610_, 2);
                v_mvarCounter_2621_ = crate::leanh::lean_ctor_get(v_mctx_2610_, 3);
                v_lDecls_2622_ = crate::leanh::lean_ctor_get(v_mctx_2610_, 4);
                v_decls_2623_ = crate::leanh::lean_ctor_get(v_mctx_2610_, 5);
                v_userNames_2624_ = crate::leanh::lean_ctor_get(v_mctx_2610_, 6);
                v_lAssignment_2625_ = crate::leanh::lean_ctor_get(v_mctx_2610_, 7);
                v_eAssignment_2626_ = crate::leanh::lean_ctor_get(v_mctx_2610_, 8);
                v_dAssignment_2627_ = crate::leanh::lean_ctor_get(v_mctx_2610_, 9);
                v_isSharedCheck_2641_ = (!crate::leanh::lean_is_exclusive(v_mctx_2610_)) as u8;
                if v_isSharedCheck_2641_ == 0 {
                    v___x_2629_ = v_mctx_2610_;
                    v_isShared_2630_ = v_isSharedCheck_2641_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_dAssignment_2627_);
                    crate::leanh::lean_inc(v_eAssignment_2626_);
                    crate::leanh::lean_inc(v_lAssignment_2625_);
                    crate::leanh::lean_inc(v_userNames_2624_);
                    crate::leanh::lean_inc(v_decls_2623_);
                    crate::leanh::lean_inc(v_lDecls_2622_);
                    crate::leanh::lean_inc(v_mvarCounter_2621_);
                    crate::leanh::lean_inc(v_lmvarCounter_2620_);
                    crate::leanh::lean_inc(v_levelAssignDepth_2619_);
                    crate::leanh::lean_inc(v_depth_2618_);
                    crate::leanh::lean_dec(v_mctx_2610_);
                    v___x_2629_ = crate::leanh::lean_box(0);
                    v_isShared_2630_ = v_isSharedCheck_2641_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2631_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1___redArg(v_eAssignment_2626_, v_mvarId_2605_, v_val_2606_);
                if v_isShared_2630_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2629_, 8, v___x_2631_);
                    v___x_2633_ = v___x_2629_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2640_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2640_, 0, v_depth_2618_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2640_,
                        1,
                        v_levelAssignDepth_2619_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2640_, 2, v_lmvarCounter_2620_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2640_, 3, v_mvarCounter_2621_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2640_, 4, v_lDecls_2622_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2640_, 5, v_decls_2623_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2640_, 6, v_userNames_2624_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2640_, 7, v_lAssignment_2625_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2640_, 8, v___x_2631_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2640_, 9, v_dAssignment_2627_);
                    v___x_2633_ = v_reuseFailAlloc_2640_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2617_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2616_, 0, v___x_2633_);
                    v___x_2635_ = v___x_2616_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2639_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2639_, 0, v___x_2633_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2639_, 1, v_cache_2611_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2639_,
                        2,
                        v_zetaDeltaFVarIds_2612_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2639_, 3, v_postponed_2613_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2639_, 4, v_diag_2614_);
                    v___x_2635_ = v_reuseFailAlloc_2639_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2636_ = lean_st_ref_set(v___y_2607_, v___x_2635_);
                v___x_2637_ = crate::leanh::lean_box(0);
                v___x_2638_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2638_, 0, v___x_2637_);
                return v___x_2638_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1___redArg___boxed(
    mut v_mvarId_2643_: *mut crate::leanh::LeanObject,
    mut v_val_2644_: *mut crate::leanh::LeanObject,
    mut v___y_2645_: *mut crate::leanh::LeanObject,
    mut v___y_2646_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2647_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1___redArg(v_mvarId_2643_, v_val_2644_, v___y_2645_);
    crate::leanh::lean_dec(v___y_2645_);
    return v_res_2647_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2662_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__8;
    v___x_2663_ = l_Lean_stringToMessageData(v___x_2662_);
    return v___x_2663_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2669_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__12;
    v___x_2670_ = l_Lean_stringToMessageData(v___x_2669_);
    return v___x_2670_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2671_ = crate::leanh::lean_box(0);
    v___x_2672_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__3;
    v___x_2673_ = l_Lean_mkConst(v___x_2672_, v___x_2671_);
    return v___x_2673_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2678_ = crate::leanh::lean_box(0);
    v___x_2679_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__16;
    v___x_2680_ = l_Lean_mkConst(v___x_2679_, v___x_2678_);
    return v___x_2680_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__20()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2685_ = crate::leanh::lean_box(0);
    v___x_2686_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__19;
    v___x_2687_ = l_Lean_mkConst(v___x_2686_, v___x_2685_);
    return v___x_2687_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__22()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2691_ = crate::leanh::lean_box(0);
    v___x_2692_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__21;
    v___x_2693_ = l_Lean_mkConst(v___x_2692_, v___x_2691_);
    return v___x_2693_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0(
    mut v_goal_2694_: *mut crate::leanh::LeanObject,
    mut v___y_2695_: *mut crate::leanh::LeanObject,
    mut v___y_2696_: *mut crate::leanh::LeanObject,
    mut v___y_2697_: *mut crate::leanh::LeanObject,
    mut v___y_2698_: *mut crate::leanh::LeanObject,
    mut v___y_2699_: *mut crate::leanh::LeanObject,
    mut v___y_2700_: *mut crate::leanh::LeanObject,
    mut v___y_2701_: *mut crate::leanh::LeanObject,
    mut v___y_2702_: *mut crate::leanh::LeanObject,
    mut v___y_2703_: *mut crate::leanh::LeanObject,
    mut v___y_2704_: *mut crate::leanh::LeanObject,
    mut v___y_2705_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2713_: u8 = 0;
    let mut v___x_2714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2715_: u8 = 0;
    let mut v___x_2716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: u8 = 0;
    let mut v___x_2718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2720_: u8 = 0;
    let mut v___x_2721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2744_: u8 = 0;
    let mut v_a_2746_: u8 = 0;
    let mut v___x_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2760_: u8 = 0;
    let mut v___x_2761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2765_: u8 = 0;
    let mut v_unused_2766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2770_: u8 = 0;
    let mut v___x_2772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2774_: u8 = 0;
    let mut v_a_2775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2778_: u8 = 0;
    let mut v___x_2780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2782_: u8 = 0;
    let mut v___x_2783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_foApprox_2784_: u8 = 0;
    let mut v_ctxApprox_2785_: u8 = 0;
    let mut v_quasiPatternApprox_2786_: u8 = 0;
    let mut v_constApprox_2787_: u8 = 0;
    let mut v_isDefEqStuckEx_2788_: u8 = 0;
    let mut v_unificationHints_2789_: u8 = 0;
    let mut v_proofIrrelevance_2790_: u8 = 0;
    let mut v_offsetCnstrs_2791_: u8 = 0;
    let mut v_transparency_2792_: u8 = 0;
    let mut v_etaStruct_2793_: u8 = 0;
    let mut v_univApprox_2794_: u8 = 0;
    let mut v_iota_2795_: u8 = 0;
    let mut v_beta_2796_: u8 = 0;
    let mut v_proj_2797_: u8 = 0;
    let mut v_zeta_2798_: u8 = 0;
    let mut v_zetaDelta_2799_: u8 = 0;
    let mut v_zetaUnused_2800_: u8 = 0;
    let mut v_zetaHave_2801_: u8 = 0;
    let mut v___x_2803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2804_: u8 = 0;
    let mut v_trackZetaDelta_2805_: u8 = 0;
    let mut v_zetaDeltaSet_2806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_2808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_2809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_2810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_2811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_2812_: u8 = 0;
    let mut v_inTypeClassResolution_2813_: u8 = 0;
    let mut v_cacheInferType_2814_: u8 = 0;
    let mut v___x_2816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: u64 = 0;
    let mut v___x_2818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: u8 = 0;
    let mut v_a_2824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2825_: u8 = 0;
    let mut v_a_2826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2829_: u8 = 0;
    let mut v___x_2831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2833_: u8 = 0;
    let mut v_reuseFailAlloc_2834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2835_: u8 = 0;
    let mut v_isSharedCheck_2836_: u8 = 0;
    let mut v_a_2837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2840_: u8 = 0;
    let mut v___x_2842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2844_: u8 = 0;
    let mut v_a_2845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2848_: u8 = 0;
    let mut v___x_2850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2852_: u8 = 0;
    let mut v_a_2853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2856_: u8 = 0;
    let mut v___x_2858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2860_: u8 = 0;
    let mut v_a_2861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2864_: u8 = 0;
    let mut v___x_2866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2868_: u8 = 0;
    let mut v_andIntroRule_2869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarIds_2887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2890_: u8 = 0;
    let mut v_tail_2891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2899_: u8 = 0;
    let mut v___x_2900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_g_2903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2916_: u8 = 0;
    let mut v___x_2917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2934_: u8 = 0;
    let mut v___x_2935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2942_: u8 = 0;
    let mut v_unused_2943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2947_: u8 = 0;
    let mut v___x_2949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2951_: u8 = 0;
    let mut v_a_2952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2955_: u8 = 0;
    let mut v___x_2957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2959_: u8 = 0;
    let mut v_a_2960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2963_: u8 = 0;
    let mut v___x_2965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2967_: u8 = 0;
    let mut v_a_2968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2971_: u8 = 0;
    let mut v___x_2973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2975_: u8 = 0;
    let mut v_a_2976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2979_: u8 = 0;
    let mut v___x_2981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2983_: u8 = 0;
    let mut v_isSharedCheck_2984_: u8 = 0;
    let mut v_isSharedCheck_2985_: u8 = 0;
    let mut v_isSharedCheck_2986_: u8 = 0;
    let mut v_a_2987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2990_: u8 = 0;
    let mut v___x_2992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2994_: u8 = 0;
    let mut v___x_2995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2999_: u8 = 0;
    let mut v___x_3000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3004_: u8 = 0;
    let mut v_unused_3005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3009_: u8 = 0;
    let mut v___x_3011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3013_: u8 = 0;
    let mut v_isSharedCheck_3014_: u8 = 0;
    let mut v_a_3015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3018_: u8 = 0;
    let mut v___x_3020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3022_: u8 = 0;
    let mut v_a_3023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3026_: u8 = 0;
    let mut v___x_3028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3030_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_goal_2694_);
                v___x_2707_ = l_Lean_MVarId_getType(
                    v_goal_2694_,
                    v___y_2702_,
                    v___y_2703_,
                    v___y_2704_,
                    v___y_2705_,
                );
                if crate::leanh::lean_obj_tag(v___x_2707_) == 0 {
                    v_a_2708_ = crate::leanh::lean_ctor_get(v___x_2707_, 0);
                    crate::leanh::lean_inc(v_a_2708_);
                    crate::leanh::lean_dec_ref_known(v___x_2707_, 1);
                    v___x_2709_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__0___redArg(v_a_2708_, v___y_2703_);
                    if crate::leanh::lean_obj_tag(v___x_2709_) == 0 {
                        v_a_2710_ = crate::leanh::lean_ctor_get(v___x_2709_, 0);
                        v_isSharedCheck_3014_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2709_)) as u8;
                        if v_isSharedCheck_3014_ == 0 {
                            v___x_2712_ = v___x_2709_;
                            v_isShared_2713_ = v_isSharedCheck_3014_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2710_);
                            crate::leanh::lean_dec(v___x_2709_);
                            v___x_2712_ = crate::leanh::lean_box(0);
                            v_isShared_2713_ = v_isSharedCheck_3014_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_goal_2694_);
                        v_a_3015_ = crate::leanh::lean_ctor_get(v___x_2709_, 0);
                        v_isSharedCheck_3022_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2709_)) as u8;
                        if v_isSharedCheck_3022_ == 0 {
                            v___x_3017_ = v___x_2709_;
                            v_isShared_3018_ = v_isSharedCheck_3022_;
                            state = 50;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3015_);
                            crate::leanh::lean_dec(v___x_2709_);
                            v___x_3017_ = crate::leanh::lean_box(0);
                            v_isShared_3018_ = v_isSharedCheck_3022_;
                            state = 50;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_goal_2694_);
                    v_a_3023_ = crate::leanh::lean_ctor_get(v___x_2707_, 0);
                    v_isSharedCheck_3030_ = (!crate::leanh::lean_is_exclusive(v___x_2707_)) as u8;
                    if v_isSharedCheck_3030_ == 0 {
                        v___x_3025_ = v___x_2707_;
                        v_isShared_3026_ = v_isSharedCheck_3030_;
                        state = 52;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3023_);
                        crate::leanh::lean_dec(v___x_2707_);
                        v___x_3025_ = crate::leanh::lean_box(0);
                        v_isShared_3026_ = v_isSharedCheck_3030_;
                        state = 52;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2714_ =
                    l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__1;
                v___x_2715_ = l_Lean_Expr_isAppOf(v_a_2710_, v___x_2714_);
                if v___x_2715_ == 0 {
                    v___x_2716_ =
                        l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__3;
                    v___x_2717_ = l_Lean_Expr_isAppOf(v_a_2710_, v___x_2716_);
                    if v___x_2717_ == 0 {
                        v___x_2718_ =
                            l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__5;
                        v___x_2719_ = crate::leanh::lean_unsigned_to_nat(3);
                        v___x_2720_ = l_Lean_Expr_isAppOfArity(v_a_2710_, v___x_2718_, v___x_2719_);
                        if v___x_2720_ == 0 {
                            crate::leanh::lean_dec(v_a_2710_);
                            v___x_2721_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2721_, 0, v_goal_2694_);
                            if v_isShared_2713_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_2712_, 0, v___x_2721_);
                                v___x_2723_ = v___x_2712_;
                                state = 2;
                                continue;
                            } else {
                                v_reuseFailAlloc_2724_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2724_, 0, v___x_2721_);
                                v___x_2723_ = v_reuseFailAlloc_2724_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_2712_);
                            v___x_2725_ = l_Lean_Expr_appFn_x21(v_a_2710_);
                            v___x_2726_ = l_Lean_Expr_appArg_x21(v___x_2725_);
                            v___x_2727_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead(
                                v___x_2726_,
                                v___y_2700_,
                                v___y_2701_,
                                v___y_2702_,
                                v___y_2703_,
                                v___y_2704_,
                                v___y_2705_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_2727_) == 0 {
                                v_a_2728_ = crate::leanh::lean_ctor_get(v___x_2727_, 0);
                                crate::leanh::lean_inc(v_a_2728_);
                                crate::leanh::lean_dec_ref_known(v___x_2727_, 1);
                                v___x_2729_ = l_Lean_Expr_appArg_x21(v_a_2710_);
                                crate::leanh::lean_dec(v_a_2710_);
                                v___x_2730_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead(
                                    v___x_2729_,
                                    v___y_2700_,
                                    v___y_2701_,
                                    v___y_2702_,
                                    v___y_2703_,
                                    v___y_2704_,
                                    v___y_2705_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_2730_) == 0 {
                                    v_a_2731_ = crate::leanh::lean_ctor_get(v___x_2730_, 0);
                                    crate::leanh::lean_inc(v_a_2731_);
                                    crate::leanh::lean_dec_ref_known(v___x_2730_, 1);
                                    v___x_2732_ = l_Lean_Expr_appFn_x21(v___x_2725_);
                                    crate::leanh::lean_dec_ref(v___x_2725_);
                                    v___x_2733_ = l_Lean_Expr_appArg_x21(v___x_2732_);
                                    crate::leanh::lean_dec_ref(v___x_2732_);
                                    crate::leanh::lean_inc_ref(v___x_2733_);
                                    v___x_2734_ = l_Lean_Meta_getLevel(
                                        v___x_2733_,
                                        v___y_2702_,
                                        v___y_2703_,
                                        v___y_2704_,
                                        v___y_2705_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_2734_) == 0 {
                                        v_a_2735_ = crate::leanh::lean_ctor_get(v___x_2734_, 0);
                                        crate::leanh::lean_inc(v_a_2735_);
                                        crate::leanh::lean_dec_ref_known(v___x_2734_, 1);
                                        v___x_2736_ = crate::leanh::lean_box(0);
                                        v___x_2737_ =
                                            crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_2737_, 0, v_a_2735_);
                                        crate::leanh::lean_ctor_set(v___x_2737_, 1, v___x_2736_);
                                        v___x_2738_ = l_Lean_mkConst(v___x_2718_, v___x_2737_);
                                        crate::leanh::lean_inc(v_a_2731_);
                                        crate::leanh::lean_inc(v_a_2728_);
                                        crate::leanh::lean_inc_ref(v___x_2733_);
                                        v___x_2739_ = l_Lean_mkApp3(
                                            v___x_2738_,
                                            v___x_2733_,
                                            v_a_2728_,
                                            v_a_2731_,
                                        );
                                        v___x_2740_ = l_Lean_MVarId_replaceTargetDefEq(
                                            v_goal_2694_,
                                            v___x_2739_,
                                            v___y_2702_,
                                            v___y_2703_,
                                            v___y_2704_,
                                            v___y_2705_,
                                        );
                                        if crate::leanh::lean_obj_tag(v___x_2740_) == 0 {
                                            v_a_2741_ = crate::leanh::lean_ctor_get(v___x_2740_, 0);
                                            v_isSharedCheck_2836_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_2740_))
                                                    as u8;
                                            if v_isSharedCheck_2836_ == 0 {
                                                v___x_2743_ = v___x_2740_;
                                                v_isShared_2744_ = v_isSharedCheck_2836_;
                                                state = 3;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_2741_);
                                                crate::leanh::lean_dec(v___x_2740_);
                                                v___x_2743_ = crate::leanh::lean_box(0);
                                                v_isShared_2744_ = v_isSharedCheck_2836_;
                                                state = 3;
                                                continue;
                                            }
                                        } else {
                                            crate::leanh::lean_dec_ref(v___x_2733_);
                                            crate::leanh::lean_dec(v_a_2731_);
                                            crate::leanh::lean_dec(v_a_2728_);
                                            v_a_2837_ = crate::leanh::lean_ctor_get(v___x_2740_, 0);
                                            v_isSharedCheck_2844_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_2740_))
                                                    as u8;
                                            if v_isSharedCheck_2844_ == 0 {
                                                v___x_2839_ = v___x_2740_;
                                                v_isShared_2840_ = v_isSharedCheck_2844_;
                                                state = 16;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_2837_);
                                                crate::leanh::lean_dec(v___x_2740_);
                                                v___x_2839_ = crate::leanh::lean_box(0);
                                                v_isShared_2840_ = v_isSharedCheck_2844_;
                                                state = 16;
                                                continue;
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref(v___x_2733_);
                                        crate::leanh::lean_dec(v_a_2731_);
                                        crate::leanh::lean_dec(v_a_2728_);
                                        crate::leanh::lean_dec(v_goal_2694_);
                                        v_a_2845_ = crate::leanh::lean_ctor_get(v___x_2734_, 0);
                                        v_isSharedCheck_2852_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_2734_)) as u8;
                                        if v_isSharedCheck_2852_ == 0 {
                                            v___x_2847_ = v___x_2734_;
                                            v_isShared_2848_ = v_isSharedCheck_2852_;
                                            state = 18;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_2845_);
                                            crate::leanh::lean_dec(v___x_2734_);
                                            v___x_2847_ = crate::leanh::lean_box(0);
                                            v_isShared_2848_ = v_isSharedCheck_2852_;
                                            state = 18;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_2728_);
                                    crate::leanh::lean_dec_ref(v___x_2725_);
                                    crate::leanh::lean_dec(v_goal_2694_);
                                    v_a_2853_ = crate::leanh::lean_ctor_get(v___x_2730_, 0);
                                    v_isSharedCheck_2860_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2730_)) as u8;
                                    if v_isSharedCheck_2860_ == 0 {
                                        v___x_2855_ = v___x_2730_;
                                        v_isShared_2856_ = v_isSharedCheck_2860_;
                                        state = 20;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_2853_);
                                        crate::leanh::lean_dec(v___x_2730_);
                                        v___x_2855_ = crate::leanh::lean_box(0);
                                        v_isShared_2856_ = v_isSharedCheck_2860_;
                                        state = 20;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v___x_2725_);
                                crate::leanh::lean_dec(v_a_2710_);
                                crate::leanh::lean_dec(v_goal_2694_);
                                v_a_2861_ = crate::leanh::lean_ctor_get(v___x_2727_, 0);
                                v_isSharedCheck_2868_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2727_)) as u8;
                                if v_isSharedCheck_2868_ == 0 {
                                    v___x_2863_ = v___x_2727_;
                                    v_isShared_2864_ = v_isSharedCheck_2868_;
                                    state = 22;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2861_);
                                    crate::leanh::lean_dec(v___x_2727_);
                                    v___x_2863_ = crate::leanh::lean_box(0);
                                    v_isShared_2864_ = v_isSharedCheck_2868_;
                                    state = 22;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_2712_);
                        v_andIntroRule_2869_ = crate::leanh::lean_ctor_get(v___y_2695_, 15);
                        v___x_2870_ = crate::leanh::lean_box(0);
                        crate::leanh::lean_inc_ref(v_andIntroRule_2869_);
                        v___x_2871_ =
                            l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(
                                v_andIntroRule_2869_,
                                v_goal_2694_,
                                v___x_2870_,
                                v___y_2695_,
                                v___y_2696_,
                                v___y_2697_,
                                v___y_2698_,
                                v___y_2699_,
                                v___y_2700_,
                                v___y_2701_,
                                v___y_2702_,
                                v___y_2703_,
                                v___y_2704_,
                                v___y_2705_,
                            );
                        if crate::leanh::lean_obj_tag(v___x_2871_) == 0 {
                            v_a_2872_ = crate::leanh::lean_ctor_get(v___x_2871_, 0);
                            crate::leanh::lean_inc(v_a_2872_);
                            crate::leanh::lean_dec_ref_known(v___x_2871_, 1);
                            if crate::leanh::lean_obj_tag(v_a_2872_) == 1 {
                                v_mvarIds_2887_ = crate::leanh::lean_ctor_get(v_a_2872_, 0);
                                v_isSharedCheck_2986_ =
                                    (!crate::leanh::lean_is_exclusive(v_a_2872_)) as u8;
                                if v_isSharedCheck_2986_ == 0 {
                                    v___x_2889_ = v_a_2872_;
                                    v_isShared_2890_ = v_isSharedCheck_2986_;
                                    state = 25;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_mvarIds_2887_);
                                    crate::leanh::lean_dec(v_a_2872_);
                                    v___x_2889_ = crate::leanh::lean_box(0);
                                    v_isShared_2890_ = v_isSharedCheck_2986_;
                                    state = 25;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_2872_);
                                v___y_2874_ = v___y_2702_;
                                v___y_2875_ = v___y_2703_;
                                v___y_2876_ = v___y_2704_;
                                v___y_2877_ = v___y_2705_;
                                state = 24;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_2710_);
                            v_a_2987_ = crate::leanh::lean_ctor_get(v___x_2871_, 0);
                            v_isSharedCheck_2994_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2871_)) as u8;
                            if v_isSharedCheck_2994_ == 0 {
                                v___x_2989_ = v___x_2871_;
                                v_isShared_2990_ = v_isSharedCheck_2994_;
                                state = 44;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2987_);
                                crate::leanh::lean_dec(v___x_2871_);
                                v___x_2989_ = crate::leanh::lean_box(0);
                                v_isShared_2990_ = v_isSharedCheck_2994_;
                                state = 44;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2712_);
                    crate::leanh::lean_dec(v_a_2710_);
                    v___x_2995_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__22), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__22_once), _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__22);
                    v___x_2996_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1___redArg(v_goal_2694_, v___x_2995_, v___y_2703_);
                    if crate::leanh::lean_obj_tag(v___x_2996_) == 0 {
                        v_isSharedCheck_3004_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2996_)) as u8;
                        if v_isSharedCheck_3004_ == 0 {
                            v_unused_3005_ = crate::leanh::lean_ctor_get(v___x_2996_, 0);
                            crate::leanh::lean_dec(v_unused_3005_);
                            v___x_2998_ = v___x_2996_;
                            v_isShared_2999_ = v_isSharedCheck_3004_;
                            state = 46;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_2996_);
                            v___x_2998_ = crate::leanh::lean_box(0);
                            v_isShared_2999_ = v_isSharedCheck_3004_;
                            state = 46;
                            continue;
                        }
                    } else {
                        v_a_3006_ = crate::leanh::lean_ctor_get(v___x_2996_, 0);
                        v_isSharedCheck_3013_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2996_)) as u8;
                        if v_isSharedCheck_3013_ == 0 {
                            v___x_3008_ = v___x_2996_;
                            v_isShared_3009_ = v_isSharedCheck_3013_;
                            state = 48;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3006_);
                            crate::leanh::lean_dec(v___x_2996_);
                            v___x_3008_ = crate::leanh::lean_box(0);
                            v_isShared_3009_ = v_isSharedCheck_3013_;
                            state = 48;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_2723_;
            }
            3 => {
                v___x_2783_ = l_Lean_Meta_Context_config(v___y_2702_);
                v_foApprox_2784_ = crate::leanh::lean_ctor_get_uint8(v___x_2783_, 0 as u32);
                v_ctxApprox_2785_ = crate::leanh::lean_ctor_get_uint8(v___x_2783_, 1 as u32);
                v_quasiPatternApprox_2786_ =
                    crate::leanh::lean_ctor_get_uint8(v___x_2783_, 2 as u32);
                v_constApprox_2787_ = crate::leanh::lean_ctor_get_uint8(v___x_2783_, 3 as u32);
                v_isDefEqStuckEx_2788_ = crate::leanh::lean_ctor_get_uint8(v___x_2783_, 4 as u32);
                v_unificationHints_2789_ = crate::leanh::lean_ctor_get_uint8(v___x_2783_, 5 as u32);
                v_proofIrrelevance_2790_ = crate::leanh::lean_ctor_get_uint8(v___x_2783_, 6 as u32);
                v_offsetCnstrs_2791_ = crate::leanh::lean_ctor_get_uint8(v___x_2783_, 8 as u32);
                v_transparency_2792_ = crate::leanh::lean_ctor_get_uint8(v___x_2783_, 9 as u32);
                v_etaStruct_2793_ = crate::leanh::lean_ctor_get_uint8(v___x_2783_, 10 as u32);
                v_univApprox_2794_ = crate::leanh::lean_ctor_get_uint8(v___x_2783_, 11 as u32);
                v_iota_2795_ = crate::leanh::lean_ctor_get_uint8(v___x_2783_, 12 as u32);
                v_beta_2796_ = crate::leanh::lean_ctor_get_uint8(v___x_2783_, 13 as u32);
                v_proj_2797_ = crate::leanh::lean_ctor_get_uint8(v___x_2783_, 14 as u32);
                v_zeta_2798_ = crate::leanh::lean_ctor_get_uint8(v___x_2783_, 15 as u32);
                v_zetaDelta_2799_ = crate::leanh::lean_ctor_get_uint8(v___x_2783_, 16 as u32);
                v_zetaUnused_2800_ = crate::leanh::lean_ctor_get_uint8(v___x_2783_, 17 as u32);
                v_zetaHave_2801_ = crate::leanh::lean_ctor_get_uint8(v___x_2783_, 18 as u32);
                v_isSharedCheck_2835_ = (!crate::leanh::lean_is_exclusive(v___x_2783_)) as u8;
                if v_isSharedCheck_2835_ == 0 {
                    v___x_2803_ = v___x_2783_;
                    v_isShared_2804_ = v_isSharedCheck_2835_;
                    state = 12;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_2783_);
                    v___x_2803_ = crate::leanh::lean_box(0);
                    v_isShared_2804_ = v_isSharedCheck_2835_;
                    state = 12;
                    continue;
                }
            }
            4 => {
                if v_a_2746_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_2733_);
                    crate::leanh::lean_dec(v_a_2728_);
                    v___x_2747_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2747_, 0, v_a_2741_);
                    if v_isShared_2744_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2743_, 0, v___x_2747_);
                        v___x_2749_ = v___x_2743_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2750_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2750_, 0, v___x_2747_);
                        v___x_2749_ = v_reuseFailAlloc_2750_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2743_);
                    crate::leanh::lean_inc_ref(v___x_2733_);
                    v___x_2751_ = l_Lean_Meta_getLevel(
                        v___x_2733_,
                        v___y_2702_,
                        v___y_2703_,
                        v___y_2704_,
                        v___y_2705_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2751_) == 0 {
                        v_a_2752_ = crate::leanh::lean_ctor_get(v___x_2751_, 0);
                        crate::leanh::lean_inc(v_a_2752_);
                        crate::leanh::lean_dec_ref_known(v___x_2751_, 1);
                        v___x_2753_ =
                            l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__7;
                        v___x_2754_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2754_, 0, v_a_2752_);
                        crate::leanh::lean_ctor_set(v___x_2754_, 1, v___x_2736_);
                        v___x_2755_ = l_Lean_mkConst(v___x_2753_, v___x_2754_);
                        v___x_2756_ = l_Lean_mkAppB(v___x_2755_, v___x_2733_, v_a_2728_);
                        v___x_2757_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1___redArg(v_a_2741_, v___x_2756_, v___y_2703_);
                        if crate::leanh::lean_obj_tag(v___x_2757_) == 0 {
                            v_isSharedCheck_2765_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2757_)) as u8;
                            if v_isSharedCheck_2765_ == 0 {
                                v_unused_2766_ = crate::leanh::lean_ctor_get(v___x_2757_, 0);
                                crate::leanh::lean_dec(v_unused_2766_);
                                v___x_2759_ = v___x_2757_;
                                v_isShared_2760_ = v_isSharedCheck_2765_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_2757_);
                                v___x_2759_ = crate::leanh::lean_box(0);
                                v_isShared_2760_ = v_isSharedCheck_2765_;
                                state = 6;
                                continue;
                            }
                        } else {
                            v_a_2767_ = crate::leanh::lean_ctor_get(v___x_2757_, 0);
                            v_isSharedCheck_2774_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2757_)) as u8;
                            if v_isSharedCheck_2774_ == 0 {
                                v___x_2769_ = v___x_2757_;
                                v_isShared_2770_ = v_isSharedCheck_2774_;
                                state = 8;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2767_);
                                crate::leanh::lean_dec(v___x_2757_);
                                v___x_2769_ = crate::leanh::lean_box(0);
                                v_isShared_2770_ = v_isSharedCheck_2774_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2741_);
                        crate::leanh::lean_dec_ref(v___x_2733_);
                        crate::leanh::lean_dec(v_a_2728_);
                        v_a_2775_ = crate::leanh::lean_ctor_get(v___x_2751_, 0);
                        v_isSharedCheck_2782_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2751_)) as u8;
                        if v_isSharedCheck_2782_ == 0 {
                            v___x_2777_ = v___x_2751_;
                            v_isShared_2778_ = v_isSharedCheck_2782_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2775_);
                            crate::leanh::lean_dec(v___x_2751_);
                            v___x_2777_ = crate::leanh::lean_box(0);
                            v_isShared_2778_ = v_isSharedCheck_2782_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            5 => {
                return v___x_2749_;
            }
            6 => {
                v___x_2761_ = crate::leanh::lean_box(0);
                if v_isShared_2760_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2759_, 0, v___x_2761_);
                    v___x_2763_ = v___x_2759_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2764_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2764_, 0, v___x_2761_);
                    v___x_2763_ = v_reuseFailAlloc_2764_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2763_;
            }
            8 => {
                if v_isShared_2770_ == 0 {
                    v___x_2772_ = v___x_2769_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2773_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2773_, 0, v_a_2767_);
                    v___x_2772_ = v_reuseFailAlloc_2773_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2772_;
            }
            10 => {
                if v_isShared_2778_ == 0 {
                    v___x_2780_ = v___x_2777_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2781_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2781_, 0, v_a_2775_);
                    v___x_2780_ = v_reuseFailAlloc_2781_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2780_;
            }
            12 => {
                v_trackZetaDelta_2805_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_2702_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_2806_ = crate::leanh::lean_ctor_get(v___y_2702_, 1);
                v_lctx_2807_ = crate::leanh::lean_ctor_get(v___y_2702_, 2);
                v_localInstances_2808_ = crate::leanh::lean_ctor_get(v___y_2702_, 3);
                v_defEqCtx_x3f_2809_ = crate::leanh::lean_ctor_get(v___y_2702_, 4);
                v_synthPendingDepth_2810_ = crate::leanh::lean_ctor_get(v___y_2702_, 5);
                v_canUnfold_x3f_2811_ = crate::leanh::lean_ctor_get(v___y_2702_, 6);
                v_univApprox_2812_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_2702_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_2813_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_2702_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_2814_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_2702_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                );
                if v_isShared_2804_ == 0 {
                    v___x_2816_ = v___x_2803_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2834_ = crate::leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2834_,
                        0 as u32,
                        v_foApprox_2784_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2834_,
                        1 as u32,
                        v_ctxApprox_2785_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2834_,
                        2 as u32,
                        v_quasiPatternApprox_2786_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2834_,
                        3 as u32,
                        v_constApprox_2787_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2834_,
                        4 as u32,
                        v_isDefEqStuckEx_2788_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2834_,
                        5 as u32,
                        v_unificationHints_2789_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2834_,
                        6 as u32,
                        v_proofIrrelevance_2790_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2834_,
                        8 as u32,
                        v_offsetCnstrs_2791_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2834_,
                        9 as u32,
                        v_transparency_2792_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2834_,
                        10 as u32,
                        v_etaStruct_2793_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2834_,
                        11 as u32,
                        v_univApprox_2794_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2834_,
                        12 as u32,
                        v_iota_2795_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2834_,
                        13 as u32,
                        v_beta_2796_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2834_,
                        14 as u32,
                        v_proj_2797_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2834_,
                        15 as u32,
                        v_zeta_2798_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2834_,
                        16 as u32,
                        v_zetaDelta_2799_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2834_,
                        17 as u32,
                        v_zetaUnused_2800_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2834_,
                        18 as u32,
                        v_zetaHave_2801_,
                    );
                    v___x_2816_ = v_reuseFailAlloc_2834_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                crate::leanh::lean_ctor_set_uint8(v___x_2816_, 7 as u32, v___x_2720_);
                v___x_2817_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2816_);
                v___x_2818_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__0;
                v___x_2819_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                crate::leanh::lean_ctor_set(v___x_2819_, 0, v___x_2816_);
                crate::leanh::lean_ctor_set_uint64(
                    v___x_2819_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2817_,
                );
                crate::leanh::lean_inc(v_canUnfold_x3f_2811_);
                crate::leanh::lean_inc(v_synthPendingDepth_2810_);
                crate::leanh::lean_inc(v_defEqCtx_x3f_2809_);
                crate::leanh::lean_inc_ref(v_localInstances_2808_);
                crate::leanh::lean_inc_ref(v_lctx_2807_);
                crate::leanh::lean_inc(v_zetaDeltaSet_2806_);
                v___x_2820_ = crate::leanh::lean_alloc_ctor(0, 7, (4) as u32);
                crate::leanh::lean_ctor_set(v___x_2820_, 0, v___x_2819_);
                crate::leanh::lean_ctor_set(v___x_2820_, 1, v_zetaDeltaSet_2806_);
                crate::leanh::lean_ctor_set(v___x_2820_, 2, v_lctx_2807_);
                crate::leanh::lean_ctor_set(v___x_2820_, 3, v_localInstances_2808_);
                crate::leanh::lean_ctor_set(v___x_2820_, 4, v_defEqCtx_x3f_2809_);
                crate::leanh::lean_ctor_set(v___x_2820_, 5, v_synthPendingDepth_2810_);
                crate::leanh::lean_ctor_set(v___x_2820_, 6, v_canUnfold_x3f_2811_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2820_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_2805_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2820_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_2812_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2820_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_2813_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2820_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_2814_,
                );
                crate::leanh::lean_inc(v_a_2728_);
                v___x_2821_ = l_Lean_Meta_Sym_isDefEqS(
                    v_a_2728_,
                    v_a_2731_,
                    v___x_2720_,
                    v___x_2720_,
                    v___x_2818_,
                    v___x_2818_,
                    v___y_2700_,
                    v___y_2701_,
                    v___x_2820_,
                    v___y_2703_,
                    v___y_2704_,
                    v___y_2705_,
                );
                crate::leanh::lean_dec_ref_known(v___x_2820_, 7);
                if crate::leanh::lean_obj_tag(v___x_2821_) == 0 {
                    v_a_2822_ = crate::leanh::lean_ctor_get(v___x_2821_, 0);
                    crate::leanh::lean_inc(v_a_2822_);
                    crate::leanh::lean_dec_ref_known(v___x_2821_, 1);
                    v___x_2823_ = (crate::leanh::lean_unbox(v_a_2822_) as u8);
                    crate::leanh::lean_dec(v_a_2822_);
                    v_a_2746_ = v___x_2823_;
                    state = 4;
                    continue;
                } else {
                    if crate::leanh::lean_obj_tag(v___x_2821_) == 0 {
                        v_a_2824_ = crate::leanh::lean_ctor_get(v___x_2821_, 0);
                        crate::leanh::lean_inc(v_a_2824_);
                        crate::leanh::lean_dec_ref_known(v___x_2821_, 1);
                        v___x_2825_ = (crate::leanh::lean_unbox(v_a_2824_) as u8);
                        crate::leanh::lean_dec(v_a_2824_);
                        v_a_2746_ = v___x_2825_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_del_object(v___x_2743_);
                        crate::leanh::lean_dec(v_a_2741_);
                        crate::leanh::lean_dec_ref(v___x_2733_);
                        crate::leanh::lean_dec(v_a_2728_);
                        v_a_2826_ = crate::leanh::lean_ctor_get(v___x_2821_, 0);
                        v_isSharedCheck_2833_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2821_)) as u8;
                        if v_isSharedCheck_2833_ == 0 {
                            v___x_2828_ = v___x_2821_;
                            v_isShared_2829_ = v_isSharedCheck_2833_;
                            state = 14;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2826_);
                            crate::leanh::lean_dec(v___x_2821_);
                            v___x_2828_ = crate::leanh::lean_box(0);
                            v_isShared_2829_ = v_isSharedCheck_2833_;
                            state = 14;
                            continue;
                        }
                    }
                }
            }
            14 => {
                if v_isShared_2829_ == 0 {
                    v___x_2831_ = v___x_2828_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2832_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2832_, 0, v_a_2826_);
                    v___x_2831_ = v_reuseFailAlloc_2832_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_2831_;
            }
            16 => {
                if v_isShared_2840_ == 0 {
                    v___x_2842_ = v___x_2839_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_2843_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2843_, 0, v_a_2837_);
                    v___x_2842_ = v_reuseFailAlloc_2843_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_2842_;
            }
            18 => {
                if v_isShared_2848_ == 0 {
                    v___x_2850_ = v___x_2847_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_2851_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2851_, 0, v_a_2845_);
                    v___x_2850_ = v_reuseFailAlloc_2851_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_2850_;
            }
            20 => {
                if v_isShared_2856_ == 0 {
                    v___x_2858_ = v___x_2855_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_2859_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2859_, 0, v_a_2853_);
                    v___x_2858_ = v_reuseFailAlloc_2859_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_2858_;
            }
            22 => {
                if v_isShared_2864_ == 0 {
                    v___x_2866_ = v___x_2863_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_2867_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2867_, 0, v_a_2861_);
                    v___x_2866_ = v_reuseFailAlloc_2867_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_2866_;
            }
            24 => {
                v___x_2878_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__9
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__9_once
                    ),
                    _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__9,
                );
                v___x_2879_ =
                    l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__11;
                v___x_2880_ = l_Lean_MessageData_ofConstName(v___x_2879_, v___x_2715_);
                v___x_2881_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2881_, 0, v___x_2878_);
                crate::leanh::lean_ctor_set(v___x_2881_, 1, v___x_2880_);
                v___x_2882_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__13), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__13_once), _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__13);
                v___x_2883_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2883_, 0, v___x_2881_);
                crate::leanh::lean_ctor_set(v___x_2883_, 1, v___x_2882_);
                v___x_2884_ = l_Lean_indentExpr(v_a_2710_);
                v___x_2885_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2885_, 0, v___x_2883_);
                crate::leanh::lean_ctor_set(v___x_2885_, 1, v___x_2884_);
                v___x_2886_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg(v___x_2885_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_);
                return v___x_2886_;
            }
            25 => {
                if crate::leanh::lean_obj_tag(v_mvarIds_2887_) == 1 {
                    v_tail_2891_ = crate::leanh::lean_ctor_get(v_mvarIds_2887_, 1);
                    crate::leanh::lean_inc(v_tail_2891_);
                    if crate::leanh::lean_obj_tag(v_tail_2891_) == 1 {
                        v_tail_2892_ = crate::leanh::lean_ctor_get(v_tail_2891_, 1);
                        if crate::leanh::lean_obj_tag(v_tail_2892_) == 0 {
                            crate::leanh::lean_dec(v_a_2710_);
                            v_head_2893_ = crate::leanh::lean_ctor_get(v_mvarIds_2887_, 0);
                            crate::leanh::lean_inc(v_head_2893_);
                            crate::leanh::lean_dec_ref_known(v_mvarIds_2887_, 2);
                            v_head_2894_ = crate::leanh::lean_ctor_get(v_tail_2891_, 0);
                            crate::leanh::lean_inc(v_head_2894_);
                            crate::leanh::lean_dec_ref_known(v_tail_2891_, 2);
                            v___x_2895_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl(
                                v_head_2893_,
                                v___y_2695_,
                                v___y_2696_,
                                v___y_2697_,
                                v___y_2698_,
                                v___y_2699_,
                                v___y_2700_,
                                v___y_2701_,
                                v___y_2702_,
                                v___y_2703_,
                                v___y_2704_,
                                v___y_2705_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_2895_) == 0 {
                                v_a_2896_ = crate::leanh::lean_ctor_get(v___x_2895_, 0);
                                v_isSharedCheck_2985_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2895_)) as u8;
                                if v_isSharedCheck_2985_ == 0 {
                                    v___x_2898_ = v___x_2895_;
                                    v_isShared_2899_ = v_isSharedCheck_2985_;
                                    state = 26;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2896_);
                                    crate::leanh::lean_dec(v___x_2895_);
                                    v___x_2898_ = crate::leanh::lean_box(0);
                                    v_isShared_2899_ = v_isSharedCheck_2985_;
                                    state = 26;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_head_2894_);
                                crate::leanh::lean_del_object(v___x_2889_);
                                return v___x_2895_;
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v_tail_2891_, 2);
                            crate::leanh::lean_dec_ref_known(v_mvarIds_2887_, 2);
                            crate::leanh::lean_del_object(v___x_2889_);
                            v___y_2874_ = v___y_2702_;
                            v___y_2875_ = v___y_2703_;
                            v___y_2876_ = v___y_2704_;
                            v___y_2877_ = v___y_2705_;
                            state = 24;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_tail_2891_);
                        crate::leanh::lean_dec_ref_known(v_mvarIds_2887_, 2);
                        crate::leanh::lean_del_object(v___x_2889_);
                        v___y_2874_ = v___y_2702_;
                        v___y_2875_ = v___y_2703_;
                        v___y_2876_ = v___y_2704_;
                        v___y_2877_ = v___y_2705_;
                        state = 24;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2889_);
                    crate::leanh::lean_dec(v_mvarIds_2887_);
                    v___y_2874_ = v___y_2702_;
                    v___y_2875_ = v___y_2703_;
                    v___y_2876_ = v___y_2704_;
                    v___y_2877_ = v___y_2705_;
                    state = 24;
                    continue;
                }
            }
            26 => {
                v___x_2900_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl(
                    v_head_2894_,
                    v___y_2695_,
                    v___y_2696_,
                    v___y_2697_,
                    v___y_2698_,
                    v___y_2699_,
                    v___y_2700_,
                    v___y_2701_,
                    v___y_2702_,
                    v___y_2703_,
                    v___y_2704_,
                    v___y_2705_,
                );
                if crate::leanh::lean_obj_tag(v___x_2900_) == 0 {
                    v_a_2901_ = crate::leanh::lean_ctor_get(v___x_2900_, 0);
                    crate::leanh::lean_inc(v_a_2901_);
                    if crate::leanh::lean_obj_tag(v_a_2896_) == 0 {
                        if crate::leanh::lean_obj_tag(v_a_2901_) == 0 {
                            crate::leanh::lean_del_object(v___x_2898_);
                            crate::leanh::lean_del_object(v___x_2889_);
                            return v___x_2900_;
                        } else {
                            crate::leanh::lean_dec_ref_known(v___x_2900_, 1);
                            v_val_2910_ = crate::leanh::lean_ctor_get(v_a_2901_, 0);
                            crate::leanh::lean_inc(v_val_2910_);
                            crate::leanh::lean_dec_ref_known(v_a_2901_, 1);
                            v_g_2903_ = v_val_2910_;
                            state = 27;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v___x_2900_, 1);
                        if crate::leanh::lean_obj_tag(v_a_2901_) == 0 {
                            v_val_2911_ = crate::leanh::lean_ctor_get(v_a_2896_, 0);
                            crate::leanh::lean_inc(v_val_2911_);
                            crate::leanh::lean_dec_ref_known(v_a_2896_, 1);
                            v_g_2903_ = v_val_2911_;
                            state = 27;
                            continue;
                        } else {
                            crate::leanh::lean_del_object(v___x_2898_);
                            crate::leanh::lean_del_object(v___x_2889_);
                            v_val_2912_ = crate::leanh::lean_ctor_get(v_a_2896_, 0);
                            crate::leanh::lean_inc(v_val_2912_);
                            crate::leanh::lean_dec_ref_known(v_a_2896_, 1);
                            v_val_2913_ = crate::leanh::lean_ctor_get(v_a_2901_, 0);
                            v_isSharedCheck_2984_ =
                                (!crate::leanh::lean_is_exclusive(v_a_2901_)) as u8;
                            if v_isSharedCheck_2984_ == 0 {
                                v___x_2915_ = v_a_2901_;
                                v_isShared_2916_ = v_isSharedCheck_2984_;
                                state = 30;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_val_2913_);
                                crate::leanh::lean_dec(v_a_2901_);
                                v___x_2915_ = crate::leanh::lean_box(0);
                                v_isShared_2916_ = v_isSharedCheck_2984_;
                                state = 30;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2898_);
                    crate::leanh::lean_dec(v_a_2896_);
                    crate::leanh::lean_del_object(v___x_2889_);
                    return v___x_2900_;
                }
            }
            27 => {
                if v_isShared_2890_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2889_, 0, v_g_2903_);
                    v___x_2905_ = v___x_2889_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_2909_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2909_, 0, v_g_2903_);
                    v___x_2905_ = v_reuseFailAlloc_2909_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                if v_isShared_2899_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2898_, 0, v___x_2905_);
                    v___x_2907_ = v___x_2898_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_2908_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2908_, 0, v___x_2905_);
                    v___x_2907_ = v_reuseFailAlloc_2908_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_2907_;
            }
            30 => {
                crate::leanh::lean_inc(v_val_2912_);
                v___x_2917_ = l_Lean_MVarId_getType(
                    v_val_2912_,
                    v___y_2702_,
                    v___y_2703_,
                    v___y_2704_,
                    v___y_2705_,
                );
                if crate::leanh::lean_obj_tag(v___x_2917_) == 0 {
                    v_a_2918_ = crate::leanh::lean_ctor_get(v___x_2917_, 0);
                    crate::leanh::lean_inc(v_a_2918_);
                    crate::leanh::lean_dec_ref_known(v___x_2917_, 1);
                    crate::leanh::lean_inc(v_val_2913_);
                    v___x_2919_ = l_Lean_MVarId_getType(
                        v_val_2913_,
                        v___y_2702_,
                        v___y_2703_,
                        v___y_2704_,
                        v___y_2705_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2919_) == 0 {
                        v_a_2920_ = crate::leanh::lean_ctor_get(v___x_2919_, 0);
                        crate::leanh::lean_inc_n(v_a_2920_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_2919_, 1);
                        v___x_2921_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__14), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__14_once), _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__14);
                        crate::leanh::lean_inc(v_a_2918_);
                        v___x_2922_ = l_Lean_mkAppB(v___x_2921_, v_a_2918_, v_a_2920_);
                        v___x_2923_ = crate::leanh::lean_box(0);
                        v___x_2924_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                            v___x_2922_,
                            v___x_2923_,
                            v___y_2702_,
                            v___y_2703_,
                            v___y_2704_,
                            v___y_2705_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_2924_) == 0 {
                            v_a_2925_ = crate::leanh::lean_ctor_get(v___x_2924_, 0);
                            crate::leanh::lean_inc_n(v_a_2925_, 2);
                            crate::leanh::lean_dec_ref_known(v___x_2924_, 1);
                            v___x_2926_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__17), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__17_once), _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__17);
                            crate::leanh::lean_inc(v_a_2920_);
                            crate::leanh::lean_inc(v_a_2918_);
                            v___x_2927_ =
                                l_Lean_mkApp3(v___x_2926_, v_a_2918_, v_a_2920_, v_a_2925_);
                            v___x_2928_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1___redArg(v_val_2912_, v___x_2927_, v___y_2703_);
                            if crate::leanh::lean_obj_tag(v___x_2928_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_2928_, 1);
                                v___x_2929_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__20), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__20_once), _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__20);
                                crate::leanh::lean_inc(v_a_2925_);
                                v___x_2930_ =
                                    l_Lean_mkApp3(v___x_2929_, v_a_2918_, v_a_2920_, v_a_2925_);
                                v___x_2931_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1___redArg(v_val_2913_, v___x_2930_, v___y_2703_);
                                if crate::leanh::lean_obj_tag(v___x_2931_) == 0 {
                                    v_isSharedCheck_2942_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2931_)) as u8;
                                    if v_isSharedCheck_2942_ == 0 {
                                        v_unused_2943_ =
                                            crate::leanh::lean_ctor_get(v___x_2931_, 0);
                                        crate::leanh::lean_dec(v_unused_2943_);
                                        v___x_2933_ = v___x_2931_;
                                        v_isShared_2934_ = v_isSharedCheck_2942_;
                                        state = 31;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v___x_2931_);
                                        v___x_2933_ = crate::leanh::lean_box(0);
                                        v_isShared_2934_ = v_isSharedCheck_2942_;
                                        state = 31;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_2925_);
                                    crate::leanh::lean_del_object(v___x_2915_);
                                    v_a_2944_ = crate::leanh::lean_ctor_get(v___x_2931_, 0);
                                    v_isSharedCheck_2951_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2931_)) as u8;
                                    if v_isSharedCheck_2951_ == 0 {
                                        v___x_2946_ = v___x_2931_;
                                        v_isShared_2947_ = v_isSharedCheck_2951_;
                                        state = 34;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_2944_);
                                        crate::leanh::lean_dec(v___x_2931_);
                                        v___x_2946_ = crate::leanh::lean_box(0);
                                        v_isShared_2947_ = v_isSharedCheck_2951_;
                                        state = 34;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_2925_);
                                crate::leanh::lean_dec(v_a_2920_);
                                crate::leanh::lean_dec(v_a_2918_);
                                crate::leanh::lean_del_object(v___x_2915_);
                                crate::leanh::lean_dec(v_val_2913_);
                                v_a_2952_ = crate::leanh::lean_ctor_get(v___x_2928_, 0);
                                v_isSharedCheck_2959_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2928_)) as u8;
                                if v_isSharedCheck_2959_ == 0 {
                                    v___x_2954_ = v___x_2928_;
                                    v_isShared_2955_ = v_isSharedCheck_2959_;
                                    state = 36;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2952_);
                                    crate::leanh::lean_dec(v___x_2928_);
                                    v___x_2954_ = crate::leanh::lean_box(0);
                                    v_isShared_2955_ = v_isSharedCheck_2959_;
                                    state = 36;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_2920_);
                            crate::leanh::lean_dec(v_a_2918_);
                            crate::leanh::lean_del_object(v___x_2915_);
                            crate::leanh::lean_dec(v_val_2913_);
                            crate::leanh::lean_dec(v_val_2912_);
                            v_a_2960_ = crate::leanh::lean_ctor_get(v___x_2924_, 0);
                            v_isSharedCheck_2967_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2924_)) as u8;
                            if v_isSharedCheck_2967_ == 0 {
                                v___x_2962_ = v___x_2924_;
                                v_isShared_2963_ = v_isSharedCheck_2967_;
                                state = 38;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2960_);
                                crate::leanh::lean_dec(v___x_2924_);
                                v___x_2962_ = crate::leanh::lean_box(0);
                                v_isShared_2963_ = v_isSharedCheck_2967_;
                                state = 38;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2918_);
                        crate::leanh::lean_del_object(v___x_2915_);
                        crate::leanh::lean_dec(v_val_2913_);
                        crate::leanh::lean_dec(v_val_2912_);
                        v_a_2968_ = crate::leanh::lean_ctor_get(v___x_2919_, 0);
                        v_isSharedCheck_2975_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2919_)) as u8;
                        if v_isSharedCheck_2975_ == 0 {
                            v___x_2970_ = v___x_2919_;
                            v_isShared_2971_ = v_isSharedCheck_2975_;
                            state = 40;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2968_);
                            crate::leanh::lean_dec(v___x_2919_);
                            v___x_2970_ = crate::leanh::lean_box(0);
                            v_isShared_2971_ = v_isSharedCheck_2975_;
                            state = 40;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2915_);
                    crate::leanh::lean_dec(v_val_2913_);
                    crate::leanh::lean_dec(v_val_2912_);
                    v_a_2976_ = crate::leanh::lean_ctor_get(v___x_2917_, 0);
                    v_isSharedCheck_2983_ = (!crate::leanh::lean_is_exclusive(v___x_2917_)) as u8;
                    if v_isSharedCheck_2983_ == 0 {
                        v___x_2978_ = v___x_2917_;
                        v_isShared_2979_ = v_isSharedCheck_2983_;
                        state = 42;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2976_);
                        crate::leanh::lean_dec(v___x_2917_);
                        v___x_2978_ = crate::leanh::lean_box(0);
                        v_isShared_2979_ = v_isSharedCheck_2983_;
                        state = 42;
                        continue;
                    }
                }
            }
            31 => {
                v___x_2935_ = l_Lean_Expr_mvarId_x21(v_a_2925_);
                crate::leanh::lean_dec(v_a_2925_);
                if v_isShared_2916_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2915_, 0, v___x_2935_);
                    v___x_2937_ = v___x_2915_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_2941_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2941_, 0, v___x_2935_);
                    v___x_2937_ = v_reuseFailAlloc_2941_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_2934_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2933_, 0, v___x_2937_);
                    v___x_2939_ = v___x_2933_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_2940_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2940_, 0, v___x_2937_);
                    v___x_2939_ = v_reuseFailAlloc_2940_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_2939_;
            }
            34 => {
                if v_isShared_2947_ == 0 {
                    v___x_2949_ = v___x_2946_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_2950_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2950_, 0, v_a_2944_);
                    v___x_2949_ = v_reuseFailAlloc_2950_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                return v___x_2949_;
            }
            36 => {
                if v_isShared_2955_ == 0 {
                    v___x_2957_ = v___x_2954_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_2958_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2958_, 0, v_a_2952_);
                    v___x_2957_ = v_reuseFailAlloc_2958_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_2957_;
            }
            38 => {
                if v_isShared_2963_ == 0 {
                    v___x_2965_ = v___x_2962_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_2966_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2966_, 0, v_a_2960_);
                    v___x_2965_ = v_reuseFailAlloc_2966_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                return v___x_2965_;
            }
            40 => {
                if v_isShared_2971_ == 0 {
                    v___x_2973_ = v___x_2970_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_2974_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2974_, 0, v_a_2968_);
                    v___x_2973_ = v_reuseFailAlloc_2974_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_2973_;
            }
            42 => {
                if v_isShared_2979_ == 0 {
                    v___x_2981_ = v___x_2978_;
                    state = 43;
                    continue;
                } else {
                    v_reuseFailAlloc_2982_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2982_, 0, v_a_2976_);
                    v___x_2981_ = v_reuseFailAlloc_2982_;
                    state = 43;
                    continue;
                }
            }
            43 => {
                return v___x_2981_;
            }
            44 => {
                if v_isShared_2990_ == 0 {
                    v___x_2992_ = v___x_2989_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_2993_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2993_, 0, v_a_2987_);
                    v___x_2992_ = v_reuseFailAlloc_2993_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                return v___x_2992_;
            }
            46 => {
                v___x_3000_ = crate::leanh::lean_box(0);
                if v_isShared_2999_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2998_, 0, v___x_3000_);
                    v___x_3002_ = v___x_2998_;
                    state = 47;
                    continue;
                } else {
                    v_reuseFailAlloc_3003_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3003_, 0, v___x_3000_);
                    v___x_3002_ = v_reuseFailAlloc_3003_;
                    state = 47;
                    continue;
                }
            }
            47 => {
                return v___x_3002_;
            }
            48 => {
                if v_isShared_3009_ == 0 {
                    v___x_3011_ = v___x_3008_;
                    state = 49;
                    continue;
                } else {
                    v_reuseFailAlloc_3012_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3012_, 0, v_a_3006_);
                    v___x_3011_ = v_reuseFailAlloc_3012_;
                    state = 49;
                    continue;
                }
            }
            49 => {
                return v___x_3011_;
            }
            50 => {
                if v_isShared_3018_ == 0 {
                    v___x_3020_ = v___x_3017_;
                    state = 51;
                    continue;
                } else {
                    v_reuseFailAlloc_3021_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3021_, 0, v_a_3015_);
                    v___x_3020_ = v_reuseFailAlloc_3021_;
                    state = 51;
                    continue;
                }
            }
            51 => {
                return v___x_3020_;
            }
            52 => {
                if v_isShared_3026_ == 0 {
                    v___x_3028_ = v___x_3025_;
                    state = 53;
                    continue;
                } else {
                    v_reuseFailAlloc_3029_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3029_, 0, v_a_3023_);
                    v___x_3028_ = v_reuseFailAlloc_3029_;
                    state = 53;
                    continue;
                }
            }
            53 => {
                return v___x_3028_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___boxed(
    mut v_goal_3031_: *mut crate::leanh::LeanObject,
    mut v___y_3032_: *mut crate::leanh::LeanObject,
    mut v___y_3033_: *mut crate::leanh::LeanObject,
    mut v___y_3034_: *mut crate::leanh::LeanObject,
    mut v___y_3035_: *mut crate::leanh::LeanObject,
    mut v___y_3036_: *mut crate::leanh::LeanObject,
    mut v___y_3037_: *mut crate::leanh::LeanObject,
    mut v___y_3038_: *mut crate::leanh::LeanObject,
    mut v___y_3039_: *mut crate::leanh::LeanObject,
    mut v___y_3040_: *mut crate::leanh::LeanObject,
    mut v___y_3041_: *mut crate::leanh::LeanObject,
    mut v___y_3042_: *mut crate::leanh::LeanObject,
    mut v___y_3043_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3044_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0(
        v_goal_3031_,
        v___y_3032_,
        v___y_3033_,
        v___y_3034_,
        v___y_3035_,
        v___y_3036_,
        v___y_3037_,
        v___y_3038_,
        v___y_3039_,
        v___y_3040_,
        v___y_3041_,
        v___y_3042_,
    );
    crate::leanh::lean_dec(v___y_3042_);
    crate::leanh::lean_dec_ref(v___y_3041_);
    crate::leanh::lean_dec(v___y_3040_);
    crate::leanh::lean_dec_ref(v___y_3039_);
    crate::leanh::lean_dec(v___y_3038_);
    crate::leanh::lean_dec_ref(v___y_3037_);
    crate::leanh::lean_dec(v___y_3036_);
    crate::leanh::lean_dec_ref(v___y_3035_);
    crate::leanh::lean_dec(v___y_3034_);
    crate::leanh::lean_dec(v___y_3033_);
    crate::leanh::lean_dec_ref(v___y_3032_);
    return v_res_3044_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl(
    mut v_goal_3045_: *mut crate::leanh::LeanObject,
    mut v_a_3046_: *mut crate::leanh::LeanObject,
    mut v_a_3047_: *mut crate::leanh::LeanObject,
    mut v_a_3048_: *mut crate::leanh::LeanObject,
    mut v_a_3049_: *mut crate::leanh::LeanObject,
    mut v_a_3050_: *mut crate::leanh::LeanObject,
    mut v_a_3051_: *mut crate::leanh::LeanObject,
    mut v_a_3052_: *mut crate::leanh::LeanObject,
    mut v_a_3053_: *mut crate::leanh::LeanObject,
    mut v_a_3054_: *mut crate::leanh::LeanObject,
    mut v_a_3055_: *mut crate::leanh::LeanObject,
    mut v_a_3056_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_goal_3045_);
    v___f_3058_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___boxed
            as *mut core::ffi::c_void,
        13,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3058_, 0, v_goal_3045_);
    v___x_3059_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__2___redArg(v_goal_3045_, v___f_3058_, v_a_3046_, v_a_3047_, v_a_3048_, v_a_3049_, v_a_3050_, v_a_3051_, v_a_3052_, v_a_3053_, v_a_3054_, v_a_3055_, v_a_3056_);
    return v___x_3059_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___boxed(
    mut v_goal_3060_: *mut crate::leanh::LeanObject,
    mut v_a_3061_: *mut crate::leanh::LeanObject,
    mut v_a_3062_: *mut crate::leanh::LeanObject,
    mut v_a_3063_: *mut crate::leanh::LeanObject,
    mut v_a_3064_: *mut crate::leanh::LeanObject,
    mut v_a_3065_: *mut crate::leanh::LeanObject,
    mut v_a_3066_: *mut crate::leanh::LeanObject,
    mut v_a_3067_: *mut crate::leanh::LeanObject,
    mut v_a_3068_: *mut crate::leanh::LeanObject,
    mut v_a_3069_: *mut crate::leanh::LeanObject,
    mut v_a_3070_: *mut crate::leanh::LeanObject,
    mut v_a_3071_: *mut crate::leanh::LeanObject,
    mut v_a_3072_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3073_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl(
        v_goal_3060_,
        v_a_3061_,
        v_a_3062_,
        v_a_3063_,
        v_a_3064_,
        v_a_3065_,
        v_a_3066_,
        v_a_3067_,
        v_a_3068_,
        v_a_3069_,
        v_a_3070_,
        v_a_3071_,
    );
    crate::leanh::lean_dec(v_a_3071_);
    crate::leanh::lean_dec_ref(v_a_3070_);
    crate::leanh::lean_dec(v_a_3069_);
    crate::leanh::lean_dec_ref(v_a_3068_);
    crate::leanh::lean_dec(v_a_3067_);
    crate::leanh::lean_dec_ref(v_a_3066_);
    crate::leanh::lean_dec(v_a_3065_);
    crate::leanh::lean_dec_ref(v_a_3064_);
    crate::leanh::lean_dec(v_a_3063_);
    crate::leanh::lean_dec(v_a_3062_);
    crate::leanh::lean_dec_ref(v_a_3061_);
    return v_res_3073_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1(
    mut v_mvarId_3074_: *mut crate::leanh::LeanObject,
    mut v_val_3075_: *mut crate::leanh::LeanObject,
    mut v___y_3076_: *mut crate::leanh::LeanObject,
    mut v___y_3077_: *mut crate::leanh::LeanObject,
    mut v___y_3078_: *mut crate::leanh::LeanObject,
    mut v___y_3079_: *mut crate::leanh::LeanObject,
    mut v___y_3080_: *mut crate::leanh::LeanObject,
    mut v___y_3081_: *mut crate::leanh::LeanObject,
    mut v___y_3082_: *mut crate::leanh::LeanObject,
    mut v___y_3083_: *mut crate::leanh::LeanObject,
    mut v___y_3084_: *mut crate::leanh::LeanObject,
    mut v___y_3085_: *mut crate::leanh::LeanObject,
    mut v___y_3086_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3088_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1___redArg(v_mvarId_3074_, v_val_3075_, v___y_3084_);
    return v___x_3088_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1___boxed(
    mut v_mvarId_3089_: *mut crate::leanh::LeanObject,
    mut v_val_3090_: *mut crate::leanh::LeanObject,
    mut v___y_3091_: *mut crate::leanh::LeanObject,
    mut v___y_3092_: *mut crate::leanh::LeanObject,
    mut v___y_3093_: *mut crate::leanh::LeanObject,
    mut v___y_3094_: *mut crate::leanh::LeanObject,
    mut v___y_3095_: *mut crate::leanh::LeanObject,
    mut v___y_3096_: *mut crate::leanh::LeanObject,
    mut v___y_3097_: *mut crate::leanh::LeanObject,
    mut v___y_3098_: *mut crate::leanh::LeanObject,
    mut v___y_3099_: *mut crate::leanh::LeanObject,
    mut v___y_3100_: *mut crate::leanh::LeanObject,
    mut v___y_3101_: *mut crate::leanh::LeanObject,
    mut v___y_3102_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3103_ =
        l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1(
            v_mvarId_3089_,
            v_val_3090_,
            v___y_3091_,
            v___y_3092_,
            v___y_3093_,
            v___y_3094_,
            v___y_3095_,
            v___y_3096_,
            v___y_3097_,
            v___y_3098_,
            v___y_3099_,
            v___y_3100_,
            v___y_3101_,
        );
    crate::leanh::lean_dec(v___y_3101_);
    crate::leanh::lean_dec_ref(v___y_3100_);
    crate::leanh::lean_dec(v___y_3099_);
    crate::leanh::lean_dec_ref(v___y_3098_);
    crate::leanh::lean_dec(v___y_3097_);
    crate::leanh::lean_dec_ref(v___y_3096_);
    crate::leanh::lean_dec(v___y_3095_);
    crate::leanh::lean_dec_ref(v___y_3094_);
    crate::leanh::lean_dec(v___y_3093_);
    crate::leanh::lean_dec(v___y_3092_);
    crate::leanh::lean_dec_ref(v___y_3091_);
    return v_res_3103_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1(
    mut v_00_u03b2_3104_: *mut crate::leanh::LeanObject,
    mut v_x_3105_: *mut crate::leanh::LeanObject,
    mut v_x_3106_: *mut crate::leanh::LeanObject,
    mut v_x_3107_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3108_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1___redArg(v_x_3105_, v_x_3106_, v_x_3107_);
    return v___x_3108_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3(
    mut v_00_u03b2_3109_: *mut crate::leanh::LeanObject,
    mut v_x_3110_: *mut crate::leanh::LeanObject,
    mut v_x_3111_: usize,
    mut v_x_3112_: usize,
    mut v_x_3113_: *mut crate::leanh::LeanObject,
    mut v_x_3114_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3115_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg(v_x_3110_, v_x_3111_, v_x_3112_, v_x_3113_, v_x_3114_);
    return v___x_3115_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___boxed(
    mut v_00_u03b2_3116_: *mut crate::leanh::LeanObject,
    mut v_x_3117_: *mut crate::leanh::LeanObject,
    mut v_x_3118_: *mut crate::leanh::LeanObject,
    mut v_x_3119_: *mut crate::leanh::LeanObject,
    mut v_x_3120_: *mut crate::leanh::LeanObject,
    mut v_x_3121_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_75883__boxed_3122_: usize = 0;
    let mut v_x_75884__boxed_3123_: usize = 0;
    let mut v_res_3124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_75883__boxed_3122_ = crate::leanh::lean_unbox_usize(v_x_3118_);
    crate::leanh::lean_dec(v_x_3118_);
    v_x_75884__boxed_3123_ = crate::leanh::lean_unbox_usize(v_x_3119_);
    crate::leanh::lean_dec(v_x_3119_);
    v_res_3124_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3(v_00_u03b2_3116_, v_x_3117_, v_x_75883__boxed_3122_, v_x_75884__boxed_3123_, v_x_3120_, v_x_3121_);
    return v_res_3124_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3_spec__4(
    mut v_00_u03b2_3125_: *mut crate::leanh::LeanObject,
    mut v_n_3126_: *mut crate::leanh::LeanObject,
    mut v_k_3127_: *mut crate::leanh::LeanObject,
    mut v_v_3128_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3129_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3_spec__4___redArg(v_n_3126_, v_k_3127_, v_v_3128_);
    return v___x_3129_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3_spec__5(
    mut v_00_u03b2_3130_: *mut crate::leanh::LeanObject,
    mut v_depth_3131_: usize,
    mut v_keys_3132_: *mut crate::leanh::LeanObject,
    mut v_vals_3133_: *mut crate::leanh::LeanObject,
    mut v_heq_3134_: *mut crate::leanh::LeanObject,
    mut v_i_3135_: *mut crate::leanh::LeanObject,
    mut v_entries_3136_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3137_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3_spec__5___redArg(v_depth_3131_, v_keys_3132_, v_vals_3133_, v_i_3135_, v_entries_3136_);
    return v___x_3137_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3_spec__5___boxed(
    mut v_00_u03b2_3138_: *mut crate::leanh::LeanObject,
    mut v_depth_3139_: *mut crate::leanh::LeanObject,
    mut v_keys_3140_: *mut crate::leanh::LeanObject,
    mut v_vals_3141_: *mut crate::leanh::LeanObject,
    mut v_heq_3142_: *mut crate::leanh::LeanObject,
    mut v_i_3143_: *mut crate::leanh::LeanObject,
    mut v_entries_3144_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_3145_: usize = 0;
    let mut v_res_3146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_3145_ = crate::leanh::lean_unbox_usize(v_depth_3139_);
    crate::leanh::lean_dec(v_depth_3139_);
    v_res_3146_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3_spec__5(v_00_u03b2_3138_, v_depth_boxed_3145_, v_keys_3140_, v_vals_3141_, v_heq_3142_, v_i_3143_, v_entries_3144_);
    crate::leanh::lean_dec_ref(v_vals_3141_);
    crate::leanh::lean_dec_ref(v_keys_3140_);
    return v_res_3146_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3_spec__4_spec__5(
    mut v_00_u03b2_3147_: *mut crate::leanh::LeanObject,
    mut v_x_3148_: *mut crate::leanh::LeanObject,
    mut v_x_3149_: *mut crate::leanh::LeanObject,
    mut v_x_3150_: *mut crate::leanh::LeanObject,
    mut v_x_3151_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3152_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3_spec__4_spec__5___redArg(v_x_3148_, v_x_3149_, v_x_3150_, v_x_3151_);
    return v___x_3152_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Util(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Main(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Intro(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_Telescope(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Util(
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
pub unsafe fn initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Util(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Main(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Intro(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Simp_Telescope(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Util(builtin);
}
