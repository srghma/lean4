// Lean compiler output
// Module: Lean.Meta.Tactic.Induction
// Imports: Lean.Meta.RecursorInfo Lean.Meta.SynthInstance Lean.Meta.Tactic.Revert Lean.Meta.Tactic.Intro Lean.Meta.Tactic.FVarSubst Lean.Meta.WHNF Init.Omega
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr3,
    l_Lean_Name_num___override, l_Lean_Name_str___override, l_List_lengthTR___redArg,
    lean_erase_macro_scopes,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::CoreM::l_Lean_Exception_isRuntime;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Exception::l_Lean_Exception_isInterrupt;
use crate::r#gen::Lean::Expr::{
    l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux, l_Lean_BinderInfo_isInstImplicit,
    l_Lean_Expr_app___override, l_Lean_Expr_fvarId_x21, l_Lean_Expr_getAppNumArgs,
    l_Lean_Expr_hasFVar, l_Lean_Expr_hasMVar, l_Lean_Expr_headBeta, l_Lean_Expr_isFVar,
    l_Lean_Expr_isForall, l_Lean_Expr_isHeadBetaTarget, l_Lean_Expr_mvarId_x21,
    l_Lean_Expr_sort___override, l_Lean_instBEqFVarId_beq, l_Lean_instBEqMVarId_beq,
    l_Lean_instHashableMVarId_hash, l_Lean_mkConst, l_Lean_mkFVar, l_Lean_mkLambda,
};
use crate::r#gen::Lean::Level::l_Lean_Level_isZero;
use crate::r#gen::Lean::LocalContext::l_Lean_LocalDecl_type;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofName,
    l_Lean_MessageData_tagWithErrorName, l_Lean_indentExpr, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp, l_Lean_Expr_abstractM,
    l_Lean_FVarId_getDecl___redArg, l_Lean_Meta_instInhabitedMetaM___lam__0___boxed,
    l_Lean_Meta_mkLambdaFVars, l_Lean_Meta_normalizeLevel, l_Lean_Meta_whnfForall,
};
use crate::r#gen::Lean::Meta::InferType::l_Lean_Meta_getLevel;
use crate::r#gen::Lean::Meta::RecursorInfo::{
    initialize_Lean_Meta_RecursorInfo, l_Lean_Meta_RecursorInfo_firstIndexPos,
    l_Lean_Meta_mkRecursorInfo, runtime_initialize_Lean_Meta_RecursorInfo,
};
use crate::r#gen::Lean::Meta::SynthInstance::{
    initialize_Lean_Meta_SynthInstance, l_Lean_Meta_synthInstance, l_Lean_Meta_synthInstance_x3f,
    runtime_initialize_Lean_Meta_SynthInstance,
};
use crate::r#gen::Lean::Meta::Tactic::Clear::l_Lean_MVarId_tryClear;
use crate::r#gen::Lean::Meta::Tactic::FVarSubst::{
    initialize_Lean_Meta_Tactic_FVarSubst, l_Lean_Meta_FVarSubst_insert,
    runtime_initialize_Lean_Meta_Tactic_FVarSubst,
};
use crate::r#gen::Lean::Meta::Tactic::Intro::{
    initialize_Lean_Meta_Tactic_Intro, l_Lean_Meta_intro1Core, l_Lean_Meta_introNCore,
    runtime_initialize_Lean_Meta_Tactic_Intro,
};
use crate::r#gen::Lean::Meta::Tactic::Revert::{
    initialize_Lean_Meta_Tactic_Revert, l_Lean_MVarId_revert,
    runtime_initialize_Lean_Meta_Tactic_Revert,
};
use crate::r#gen::Lean::Meta::Tactic::Util::{
    l_Lean_MVarId_checkNotAssigned, l_Lean_MVarId_getTag, l_Lean_MVarId_getType,
    l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar, l_Lean_Meta_mkTacticExMsg,
    l_Lean_Meta_throwTacticEx___redArg,
};
use crate::r#gen::Lean::Meta::WHNF::{
    initialize_Lean_Meta_WHNF, l_Lean_Meta_whnfUntil, runtime_initialize_Lean_Meta_WHNF,
};
use crate::r#gen::Lean::MetavarContext::l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit;
use crate::r#gen::Lean::Util::Trace::{
    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go, l_Lean_registerTraceClass,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::{lean_array_fset, lean_array_set};
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_to_usize, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_le, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
    lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size,
    lean_array_mk, lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub,
    lean_panic_fn_borrowed, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Expr::{lean_expr_eqv, lean_expr_instantiate1};
use crate::lean_imports_rs::Lean::Meta::Basic::lean_infer_type;
pub static l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__0_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [105, 110, 100, 117, 99, 116, 105, 111, 110, 0],
};
static mut l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1_value:
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
            l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        9134229551085355598 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__2_value:
    crate::leanh::LeanStringObject<49> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 49,
    m_capacity: 49,
    m_length: 48,
    m_data: [
        102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 103, 101, 110, 101, 114, 97, 116, 101, 32,
        116, 121, 112, 101, 32, 99, 108, 97, 115, 115, 32, 105, 110, 115, 116, 97, 110, 99, 101,
        32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 0,
    ],
};
static mut l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__3_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__2_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__3_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__6_value:
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
        105, 108, 108, 45, 102, 111, 114, 109, 101, 100, 32, 114, 101, 99, 117, 114, 115, 111, 114,
        0,
    ],
};
static mut l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__6_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__7_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__6_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__7_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__8_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_instInhabitedInductionSubgoal_default___closed__0_value:
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
static mut l_Lean_Meta_instInhabitedInductionSubgoal_default___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instInhabitedInductionSubgoal_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instInhabitedInductionSubgoal_default___closed__1_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_instInhabitedInductionSubgoal_default___closed__0_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_instInhabitedInductionSubgoal_default___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instInhabitedInductionSubgoal_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_instInhabitedInductionSubgoal_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instInhabitedInductionSubgoal_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_instInhabitedInductionSubgoal: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instInhabitedInductionSubgoal_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instInhabitedAltVarNames_default___closed__0_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        0 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_instInhabitedAltVarNames_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instInhabitedAltVarNames_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_instInhabitedAltVarNames_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instInhabitedAltVarNames_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_instInhabitedAltVarNames: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instInhabitedAltVarNames_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__4___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instInhabitedMetaM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__4___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__4___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__1_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__2_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__0_value:
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
    m_data: [77, 101, 116, 97, 0],
};
static mut l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__1_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [84, 97, 99, 116, 105, 99, 0],
};
static mut l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__1_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2_value_aux_0:
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
            l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        142734480563613395 as *mut crate::leanh::LeanObject,
    ],
};
static l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__1_value) as *mut crate::leanh::LeanObject,15847151208953044930 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__0_value) as *mut crate::leanh::LeanObject,13036350349914159643 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__3_value:
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
    m_data: [116, 114, 97, 99, 101, 0],
};
static mut l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__4_value:
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
            l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__3_value
        ) as *mut crate::leanh::LeanObject,
        14231257465488249300 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__4_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__6_value:
    crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        102, 105, 110, 97, 108, 105, 122, 101, 32, 108, 111, 111, 112, 32, 105, 115, 32, 100, 111,
        110, 101, 44, 32, 0,
    ],
};
static mut l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__6_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__8_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [32, 115, 117, 98, 103, 111, 97, 108, 115, 0],
};
static mut l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__8_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__9_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__10_value:
    crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        110, 97, 109, 101, 32, 111, 102, 32, 109, 97, 106, 111, 114, 32, 112, 114, 101, 109, 105,
        115, 101, 58, 32, 0,
    ],
};
static mut l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__10_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__11_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__12_value:
    crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 73, 110, 100,
        117, 99, 116, 105, 111, 110, 0,
    ],
};
static mut l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__12_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__13_value:
    crate::leanh::LeanStringObject<62> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 62,
    m_capacity: 62,
    m_length: 61,
    m_data: [
        95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84,
        97, 99, 116, 105, 99, 46, 73, 110, 100, 117, 99, 116, 105, 111, 110, 46, 48, 46, 76, 101,
        97, 110, 46, 77, 101, 116, 97, 46, 102, 105, 110, 97, 108, 105, 122, 101, 46, 108, 111,
        111, 112, 0,
    ],
};
static mut l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__13_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__14_value:
    crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 34,
    m_capacity: 34,
    m_length: 33,
    m_data: [
        117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115,
        32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0,
    ],
};
static mut l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__14:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__14_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__15_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize___closed__0_value:
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
static mut l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__0_value: crate::leanh::LeanStringObject<30> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 30, m_capacity: 30, m_length: 29, m_data: [117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 109, 97, 106, 111, 114, 32, 112, 114, 101, 109, 105, 115, 101, 32, 116, 121, 112, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__1___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [39, 0]};
static mut l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__2_value: crate::leanh::LeanStringObject<80> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 80, m_capacity: 80, m_length: 79, m_data: [39, 32, 105, 115, 32, 97, 110, 32, 105, 110, 100, 101, 120, 32, 105, 110, 32, 109, 97, 106, 111, 114, 32, 112, 114, 101, 109, 105, 115, 101, 44, 32, 98, 117, 116, 32, 105, 116, 32, 100, 101, 112, 101, 110, 100, 115, 32, 111, 110, 32, 105, 110, 100, 101, 120, 32, 111, 99, 99, 117, 114, 114, 105, 110, 103, 32, 97, 116, 32, 112, 111, 115, 105, 116, 105, 111, 110, 32, 35, 0]};
static mut l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__4_value: crate::leanh::LeanStringObject<68> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [39, 32, 105, 115, 32, 97, 110, 32, 105, 110, 100, 101, 120, 32, 105, 110, 32, 109, 97, 106, 111, 114, 32, 112, 114, 101, 109, 105, 115, 101, 44, 32, 98, 117, 116, 32, 105, 116, 32, 111, 99, 99, 117, 114, 115, 32, 105, 110, 32, 112, 114, 101, 118, 105, 111, 117, 115, 32, 97, 114, 103, 117, 109, 101, 110, 116, 115, 0]};
static mut l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__6_value: crate::leanh::LeanStringObject<61> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 61, m_capacity: 61, m_length: 60, m_data: [39, 32, 105, 115, 32, 97, 110, 32, 105, 110, 100, 101, 120, 32, 105, 110, 32, 109, 97, 106, 111, 114, 32, 112, 114, 101, 109, 105, 115, 101, 44, 32, 98, 117, 116, 32, 105, 116, 32, 111, 99, 99, 117, 114, 115, 32, 109, 111, 114, 101, 32, 116, 104, 97, 110, 32, 111, 110, 99, 101, 0]};
static mut l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__0_value: crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [109, 97, 106, 111, 114, 32, 112, 114, 101, 109, 105, 115, 101, 32, 116, 121, 112, 101, 32, 105, 110, 100, 101, 120, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__2_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 118, 97, 114, 105, 97, 98, 108, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__4_value: crate::leanh::LeanStringObject<33> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [109, 97, 106, 111, 114, 32, 112, 114, 101, 109, 105, 115, 101, 32, 116, 121, 112, 101, 32, 105, 115, 32, 105, 108, 108, 45, 102, 111, 114, 109, 101, 100, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_getMajorTypeIndices___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_getMajorTypeIndices___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__0_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__2_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [120, 0]};
static mut l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__2_value) as *mut crate::leanh::LeanObject,13655884332201764339 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__4_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 101, 97, 110, 0]};
static mut l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__5_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [112, 114, 111, 112, 82, 101, 99, 76, 97, 114, 103, 101, 69, 108, 105, 109, 0]};
static mut l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__5_value) as *mut crate::leanh::LeanObject;
static l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__4_value) as *mut crate::leanh::LeanObject,9199928461212983083 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__6_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__5_value) as *mut crate::leanh::LeanObject,4458248471318271735 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__7_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [114, 101, 99, 117, 114, 115, 111, 114, 32, 96, 0]};
static mut l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__7_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__9_value: crate::leanh::LeanStringObject<33> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [96, 32, 99, 97, 110, 32, 111, 110, 108, 121, 32, 101, 108, 105, 109, 105, 110, 97, 116, 101, 32, 105, 110, 116, 111, 32, 96, 80, 114, 111, 112, 96, 0]};
static mut l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__9_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__11_value: crate::leanh::LeanStringObject<41> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 41, m_capacity: 41, m_length: 40, m_data: [109, 97, 106, 111, 114, 32, 112, 114, 101, 109, 105, 115, 101, 32, 105, 115, 32, 110, 111, 116, 32, 111, 102, 32, 116, 104, 101, 32, 102, 111, 114, 109, 32, 40, 67, 32, 46, 46, 46, 41, 0]};
static mut l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__12_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__11_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__12_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__13_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__13: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__0_value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [97, 102, 116, 101, 114, 32, 114, 101, 118, 101, 114, 116, 38, 105, 110, 116, 114, 111, 10, 0]};
static mut l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__2_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [114, 101, 99, 117, 114, 115, 111, 114, 32, 39, 0]};
static mut l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__4_value: crate::leanh::LeanStringObject<82> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 82, m_capacity: 82, m_length: 81, m_data: [39, 32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 115, 117, 112, 112, 111, 114, 116, 32, 100, 101, 112, 101, 110, 100, 101, 110, 116, 32, 101, 108, 105, 109, 105, 110, 97, 116, 105, 111, 110, 44, 32, 98, 117, 116, 32, 99, 111, 110, 99, 108, 117, 115, 105, 111, 110, 32, 100, 101, 112, 101, 110, 100, 115, 32, 111, 110, 32, 109, 97, 106, 111, 114, 32, 112, 114, 101, 109, 105, 115, 101, 0]};
static mut l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_MVarId_induction___lam__0___closed__0_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [105, 110, 105, 116, 105, 97, 108, 10, 0],
    };
static mut l_Lean_MVarId_induction___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_induction___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_MVarId_induction___lam__0___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_induction___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11079354408986465895 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,10352885018404983386 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__0_value) as *mut crate::leanh::LeanObject,13556645696814629918 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__1_value) as *mut crate::leanh::LeanObject,18261494228143523011 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [73, 110, 100, 117, 99, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,18126249269145477576 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,16958555676422685473 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,12830006613079322948 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__0_value) as *mut crate::leanh::LeanObject,18002518749944319896 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,10144738984557955669 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,5617762443433636072 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8317722334821517377 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__0_value) as *mut crate::leanh::LeanObject,17926710105567873 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__1_value) as *mut crate::leanh::LeanObject,829465440862518408 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8911271021728440095 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTargetArity(
    mut v_x_2980_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_expr_2981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_2983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2987_: u8 = 0;
    let mut v___x_2988_: u8 = 0;
    let mut v___x_2989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_2980_) {
                10 => {
                    v_expr_2981_ = crate::leanh::lean_ctor_get(v_x_2980_, 1);
                    crate::leanh::lean_inc_ref(v_expr_2981_);
                    crate::leanh::lean_dec_ref_known(v_x_2980_, 2);
                    v_x_2980_ = v_expr_2981_;
                    state = 0;
                    continue;
                }
                7 => {
                    v_body_2983_ = crate::leanh::lean_ctor_get(v_x_2980_, 2);
                    crate::leanh::lean_inc_ref(v_body_2983_);
                    crate::leanh::lean_dec_ref_known(v_x_2980_, 3);
                    v___x_2984_ =
                        l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTargetArity(
                            v_body_2983_,
                        );
                    v___x_2985_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2986_ = lean_nat_add(v___x_2984_, v___x_2985_);
                    crate::leanh::lean_dec(v___x_2984_);
                    return v___x_2986_;
                }
                _ => {
                    v___x_2987_ = 0;
                    v___x_2988_ = l_Lean_Expr_isHeadBetaTarget(v_x_2980_, v___x_2987_);
                    if v___x_2988_ == 0 {
                        crate::leanh::lean_dec_ref(v_x_2980_);
                        v___x_2989_ = crate::leanh::lean_unsigned_to_nat(0);
                        return v___x_2989_;
                    } else {
                        v___x_2990_ = l_Lean_Expr_headBeta(v_x_2980_);
                        v_x_2980_ = v___x_2990_;
                        state = 0;
                        continue;
                    }
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2998_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__3;
    v___x_2999_ = l_Lean_MessageData_ofFormat(v___x_2998_);
    return v___x_2999_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3000_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__4
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__4_once
        ),
        _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__4,
    );
    v___x_3001_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3001_, 0, v___x_3000_);
    return v___x_3001_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3005_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__7;
    v___x_3006_ = l_Lean_MessageData_ofFormat(v___x_3005_);
    return v___x_3006_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3007_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__8
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__8_once
        ),
        _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__8,
    );
    v___x_3008_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3008_, 0, v___x_3007_);
    return v___x_3008_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams(
    mut v_mvarId_3009_: *mut crate::leanh::LeanObject,
    mut v_majorTypeArgs_3010_: *mut crate::leanh::LeanObject,
    mut v_x_3011_: *mut crate::leanh::LeanObject,
    mut v_x_3012_: *mut crate::leanh::LeanObject,
    mut v_a_3013_: *mut crate::leanh::LeanObject,
    mut v_a_3014_: *mut crate::leanh::LeanObject,
    mut v_a_3015_: *mut crate::leanh::LeanObject,
    mut v_a_3016_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_3030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3034_: u8 = 0;
    let mut v___x_3035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: u8 = 0;
    let mut v___x_3039_: u8 = 0;
    let mut v___x_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3045_: u8 = 0;
    let mut v___x_3046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3011_) == 0 {
                    crate::leanh::lean_dec(v_mvarId_3009_);
                    v___x_3018_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3018_, 0, v_x_3012_);
                    return v___x_3018_;
                } else {
                    v_head_3019_ = crate::leanh::lean_ctor_get(v_x_3011_, 0);
                    crate::leanh::lean_inc(v_head_3019_);
                    v_tail_3020_ = crate::leanh::lean_ctor_get(v_x_3011_, 1);
                    crate::leanh::lean_inc(v_tail_3020_);
                    crate::leanh::lean_dec_ref_known(v_x_3011_, 2);
                    if crate::leanh::lean_obj_tag(v_head_3019_) == 0 {
                        crate::leanh::lean_inc(v_a_3016_);
                        crate::leanh::lean_inc_ref(v_a_3015_);
                        crate::leanh::lean_inc(v_a_3014_);
                        crate::leanh::lean_inc_ref(v_a_3013_);
                        crate::leanh::lean_inc_ref(v_x_3012_);
                        v___x_3026_ =
                            lean_infer_type(v_x_3012_, v_a_3013_, v_a_3014_, v_a_3015_, v_a_3016_);
                        if crate::leanh::lean_obj_tag(v___x_3026_) == 0 {
                            v_a_3027_ = crate::leanh::lean_ctor_get(v___x_3026_, 0);
                            crate::leanh::lean_inc(v_a_3027_);
                            crate::leanh::lean_dec_ref_known(v___x_3026_, 1);
                            v___x_3028_ = l_Lean_Meta_whnfForall(
                                v_a_3027_, v_a_3013_, v_a_3014_, v_a_3015_, v_a_3016_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_3028_) == 0 {
                                v_a_3029_ = crate::leanh::lean_ctor_get(v___x_3028_, 0);
                                crate::leanh::lean_inc(v_a_3029_);
                                crate::leanh::lean_dec_ref_known(v___x_3028_, 1);
                                if crate::leanh::lean_obj_tag(v_a_3029_) == 7 {
                                    v_binderType_3030_ = crate::leanh::lean_ctor_get(v_a_3029_, 1);
                                    crate::leanh::lean_inc_ref(v_binderType_3030_);
                                    crate::leanh::lean_dec_ref_known(v_a_3029_, 3);
                                    v___x_3031_ = l_Lean_Meta_synthInstance(
                                        v_binderType_3030_,
                                        v_head_3019_,
                                        v_a_3013_,
                                        v_a_3014_,
                                        v_a_3015_,
                                        v_a_3016_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_3031_) == 0 {
                                        v___y_3022_ = v___x_3031_;
                                        state = 1;
                                        continue;
                                    } else {
                                        v_a_3032_ = crate::leanh::lean_ctor_get(v___x_3031_, 0);
                                        crate::leanh::lean_inc(v_a_3032_);
                                        v___x_3038_ = l_Lean_Exception_isInterrupt(v_a_3032_);
                                        if v___x_3038_ == 0 {
                                            v___x_3039_ = l_Lean_Exception_isRuntime(v_a_3032_);
                                            v___y_3034_ = v___x_3039_;
                                            state = 2;
                                            continue;
                                        } else {
                                            crate::leanh::lean_dec(v_a_3032_);
                                            v___y_3034_ = v___x_3038_;
                                            state = 2;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_3029_);
                                    crate::leanh::lean_dec(v_tail_3020_);
                                    crate::leanh::lean_dec_ref(v_x_3012_);
                                    v___x_3040_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1;
                                    v___x_3041_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once), _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
                                    v___x_3042_ = l_Lean_Meta_throwTacticEx___redArg(
                                        v___x_3040_,
                                        v_mvarId_3009_,
                                        v___x_3041_,
                                        v_a_3013_,
                                        v_a_3014_,
                                        v_a_3015_,
                                        v_a_3016_,
                                    );
                                    return v___x_3042_;
                                }
                            } else {
                                crate::leanh::lean_dec(v_tail_3020_);
                                crate::leanh::lean_dec_ref(v_x_3012_);
                                crate::leanh::lean_dec(v_mvarId_3009_);
                                return v___x_3028_;
                            }
                        } else {
                            crate::leanh::lean_dec(v_tail_3020_);
                            crate::leanh::lean_dec_ref(v_x_3012_);
                            crate::leanh::lean_dec(v_mvarId_3009_);
                            return v___x_3026_;
                        }
                    } else {
                        v_val_3043_ = crate::leanh::lean_ctor_get(v_head_3019_, 0);
                        crate::leanh::lean_inc(v_val_3043_);
                        crate::leanh::lean_dec_ref_known(v_head_3019_, 1);
                        v___x_3044_ = lean_array_get_size(v_majorTypeArgs_3010_);
                        v___x_3045_ = lean_nat_dec_lt(v_val_3043_, v___x_3044_);
                        if v___x_3045_ == 0 {
                            crate::leanh::lean_dec(v_val_3043_);
                            crate::leanh::lean_dec(v_tail_3020_);
                            crate::leanh::lean_dec_ref(v_x_3012_);
                            v___x_3046_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1;
                            v___x_3047_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once), _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
                            v___x_3048_ = l_Lean_Meta_throwTacticEx___redArg(
                                v___x_3046_,
                                v_mvarId_3009_,
                                v___x_3047_,
                                v_a_3013_,
                                v_a_3014_,
                                v_a_3015_,
                                v_a_3016_,
                            );
                            return v___x_3048_;
                        } else {
                            v___x_3049_ =
                                lean_array_fget_borrowed(v_majorTypeArgs_3010_, v_val_3043_);
                            crate::leanh::lean_dec(v_val_3043_);
                            crate::leanh::lean_inc(v___x_3049_);
                            v___x_3050_ = l_Lean_Expr_app___override(v_x_3012_, v___x_3049_);
                            v_x_3011_ = v_tail_3020_;
                            v_x_3012_ = v___x_3050_;
                            state = 0;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v___y_3022_) == 0 {
                    v_a_3023_ = crate::leanh::lean_ctor_get(v___y_3022_, 0);
                    crate::leanh::lean_inc(v_a_3023_);
                    crate::leanh::lean_dec_ref_known(v___y_3022_, 1);
                    v___x_3024_ = l_Lean_Expr_app___override(v_x_3012_, v_a_3023_);
                    v_x_3011_ = v_tail_3020_;
                    v_x_3012_ = v___x_3024_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_tail_3020_);
                    crate::leanh::lean_dec_ref(v_x_3012_);
                    crate::leanh::lean_dec(v_mvarId_3009_);
                    return v___y_3022_;
                }
            }
            2 => {
                if v___y_3034_ == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_3031_, 1);
                    v___x_3035_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1;
                    v___x_3036_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__5_once), _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__5);
                    crate::leanh::lean_inc(v_mvarId_3009_);
                    v___x_3037_ = l_Lean_Meta_throwTacticEx___redArg(
                        v___x_3035_,
                        v_mvarId_3009_,
                        v___x_3036_,
                        v_a_3013_,
                        v_a_3014_,
                        v_a_3015_,
                        v_a_3016_,
                    );
                    v___y_3022_ = v___x_3037_;
                    state = 1;
                    continue;
                } else {
                    v___y_3022_ = v___x_3031_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___boxed(
    mut v_mvarId_3052_: *mut crate::leanh::LeanObject,
    mut v_majorTypeArgs_3053_: *mut crate::leanh::LeanObject,
    mut v_x_3054_: *mut crate::leanh::LeanObject,
    mut v_x_3055_: *mut crate::leanh::LeanObject,
    mut v_a_3056_: *mut crate::leanh::LeanObject,
    mut v_a_3057_: *mut crate::leanh::LeanObject,
    mut v_a_3058_: *mut crate::leanh::LeanObject,
    mut v_a_3059_: *mut crate::leanh::LeanObject,
    mut v_a_3060_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3061_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams(
        v_mvarId_3052_,
        v_majorTypeArgs_3053_,
        v_x_3054_,
        v_x_3055_,
        v_a_3056_,
        v_a_3057_,
        v_a_3058_,
        v_a_3059_,
    );
    crate::leanh::lean_dec(v_a_3059_);
    crate::leanh::lean_dec_ref(v_a_3058_);
    crate::leanh::lean_dec(v_a_3057_);
    crate::leanh::lean_dec_ref(v_a_3056_);
    crate::leanh::lean_dec_ref(v_majorTypeArgs_3053_);
    return v_res_3061_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(
    mut v_mvarId_3070_: *mut crate::leanh::LeanObject,
    mut v_type_3071_: *mut crate::leanh::LeanObject,
    mut v_x_3072_: *mut crate::leanh::LeanObject,
    mut v_a_3073_: *mut crate::leanh::LeanObject,
    mut v_a_3074_: *mut crate::leanh::LeanObject,
    mut v_a_3075_: *mut crate::leanh::LeanObject,
    mut v_a_3076_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3082_: u8 = 0;
    let mut v_body_3083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3091_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3078_ = l_Lean_Meta_whnfForall(
                    v_type_3071_,
                    v_a_3073_,
                    v_a_3074_,
                    v_a_3075_,
                    v_a_3076_,
                );
                if crate::leanh::lean_obj_tag(v___x_3078_) == 0 {
                    v_a_3079_ = crate::leanh::lean_ctor_get(v___x_3078_, 0);
                    v_isSharedCheck_3091_ = (!crate::leanh::lean_is_exclusive(v___x_3078_)) as u8;
                    if v_isSharedCheck_3091_ == 0 {
                        v___x_3081_ = v___x_3078_;
                        v_isShared_3082_ = v_isSharedCheck_3091_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3079_);
                        crate::leanh::lean_dec(v___x_3078_);
                        v___x_3081_ = crate::leanh::lean_box(0);
                        v_isShared_3082_ = v_isSharedCheck_3091_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_mvarId_3070_);
                    return v___x_3078_;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_3079_) == 7 {
                    crate::leanh::lean_dec(v_mvarId_3070_);
                    v_body_3083_ = crate::leanh::lean_ctor_get(v_a_3079_, 2);
                    crate::leanh::lean_inc_ref(v_body_3083_);
                    crate::leanh::lean_dec_ref_known(v_a_3079_, 3);
                    v___x_3084_ = lean_expr_instantiate1(v_body_3083_, v_x_3072_);
                    crate::leanh::lean_dec_ref(v_body_3083_);
                    if v_isShared_3082_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3081_, 0, v___x_3084_);
                        v___x_3086_ = v___x_3081_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3087_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3087_, 0, v___x_3084_);
                        v___x_3086_ = v_reuseFailAlloc_3087_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3081_);
                    crate::leanh::lean_dec(v_a_3079_);
                    v___x_3088_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1;
                    v___x_3089_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once), _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
                    v___x_3090_ = l_Lean_Meta_throwTacticEx___redArg(
                        v___x_3088_,
                        v_mvarId_3070_,
                        v___x_3089_,
                        v_a_3073_,
                        v_a_3074_,
                        v_a_3075_,
                        v_a_3076_,
                    );
                    return v___x_3090_;
                }
            }
            2 => {
                return v___x_3086_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody___boxed(
    mut v_mvarId_3092_: *mut crate::leanh::LeanObject,
    mut v_type_3093_: *mut crate::leanh::LeanObject,
    mut v_x_3094_: *mut crate::leanh::LeanObject,
    mut v_a_3095_: *mut crate::leanh::LeanObject,
    mut v_a_3096_: *mut crate::leanh::LeanObject,
    mut v_a_3097_: *mut crate::leanh::LeanObject,
    mut v_a_3098_: *mut crate::leanh::LeanObject,
    mut v_a_3099_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3100_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(
        v_mvarId_3092_,
        v_type_3093_,
        v_x_3094_,
        v_a_3095_,
        v_a_3096_,
        v_a_3097_,
        v_a_3098_,
    );
    crate::leanh::lean_dec(v_a_3098_);
    crate::leanh::lean_dec_ref(v_a_3097_);
    crate::leanh::lean_dec(v_a_3096_);
    crate::leanh::lean_dec_ref(v_a_3095_);
    crate::leanh::lean_dec_ref(v_x_3094_);
    return v_res_3100_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__4(
    mut v_msg_3107_: *mut crate::leanh::LeanObject,
    mut v___y_3108_: *mut crate::leanh::LeanObject,
    mut v___y_3109_: *mut crate::leanh::LeanObject,
    mut v___y_3110_: *mut crate::leanh::LeanObject,
    mut v___y_3111_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8866__overap_3114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3113_ = l_panic___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__4___closed__0;
    v___x_8866__overap_3114_ = lean_panic_fn_borrowed(v___f_3113_, v_msg_3107_);
    crate::leanh::lean_inc(v___y_3111_);
    crate::leanh::lean_inc_ref(v___y_3110_);
    crate::leanh::lean_inc(v___y_3109_);
    crate::leanh::lean_inc_ref(v___y_3108_);
    v___x_3115_ = crate::leanh::lean_apply_5(
        v___x_8866__overap_3114_,
        v___y_3108_,
        v___y_3109_,
        v___y_3110_,
        v___y_3111_,
        crate::leanh::lean_box(0),
    );
    return v___x_3115_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__4___boxed(
    mut v_msg_3116_: *mut crate::leanh::LeanObject,
    mut v___y_3117_: *mut crate::leanh::LeanObject,
    mut v___y_3118_: *mut crate::leanh::LeanObject,
    mut v___y_3119_: *mut crate::leanh::LeanObject,
    mut v___y_3120_: *mut crate::leanh::LeanObject,
    mut v___y_3121_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3122_ =
        l_panic___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__4(
            v_msg_3116_,
            v___y_3117_,
            v___y_3118_,
            v___y_3119_,
            v___y_3120_,
        );
    crate::leanh::lean_dec(v___y_3120_);
    crate::leanh::lean_dec_ref(v___y_3119_);
    crate::leanh::lean_dec(v___y_3118_);
    crate::leanh::lean_dec_ref(v___y_3117_);
    return v_res_3122_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2___redArg(
    mut v___x_3123_: *mut crate::leanh::LeanObject,
    mut v_reverted_3124_: *mut crate::leanh::LeanObject,
    mut v_fst_3125_: *mut crate::leanh::LeanObject,
    mut v_n_3126_: *mut crate::leanh::LeanObject,
    mut v_j_3127_: *mut crate::leanh::LeanObject,
    mut v_a_3128_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_3129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_3130_: u8 = 0;
    let mut v___x_3131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_3132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: u8 = 0;
    let mut v___x_3136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_3129_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_3130_ = lean_nat_dec_eq(v_j_3127_, v_zero_3129_);
                if v_isZero_3130_ == 1 {
                    crate::leanh::lean_dec(v_j_3127_);
                    return v_a_3128_;
                } else {
                    v___x_3131_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_3132_ = lean_nat_sub(v_j_3127_, v___x_3131_);
                    v___x_3133_ = lean_nat_sub(v_n_3126_, v_j_3127_);
                    crate::leanh::lean_dec(v_j_3127_);
                    v___x_3134_ = lean_nat_add(v___x_3123_, v___x_3131_);
                    v___x_3135_ = lean_nat_dec_lt(v___x_3133_, v___x_3134_);
                    crate::leanh::lean_dec(v___x_3134_);
                    if v___x_3135_ == 0 {
                        v___x_3136_ = lean_array_fget_borrowed(v_reverted_3124_, v___x_3133_);
                        v___x_3137_ = crate::leanh::lean_box(0);
                        v___x_3138_ = lean_nat_sub(v___x_3133_, v___x_3123_);
                        crate::leanh::lean_dec(v___x_3133_);
                        v___x_3139_ = lean_nat_sub(v___x_3138_, v___x_3131_);
                        crate::leanh::lean_dec(v___x_3138_);
                        v___x_3140_ =
                            lean_array_get_borrowed(v___x_3137_, v_fst_3125_, v___x_3139_);
                        crate::leanh::lean_dec(v___x_3139_);
                        crate::leanh::lean_inc(v___x_3140_);
                        v___x_3141_ = l_Lean_mkFVar(v___x_3140_);
                        crate::leanh::lean_inc(v___x_3136_);
                        v___x_3142_ =
                            l_Lean_Meta_FVarSubst_insert(v_a_3128_, v___x_3136_, v___x_3141_);
                        v_j_3127_ = v_n_3132_;
                        v_a_3128_ = v___x_3142_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_3133_);
                        v_j_3127_ = v_n_3132_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2___redArg___boxed(
    mut v___x_3145_: *mut crate::leanh::LeanObject,
    mut v_reverted_3146_: *mut crate::leanh::LeanObject,
    mut v_fst_3147_: *mut crate::leanh::LeanObject,
    mut v_n_3148_: *mut crate::leanh::LeanObject,
    mut v_j_3149_: *mut crate::leanh::LeanObject,
    mut v_a_3150_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3151_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2___redArg(v___x_3145_, v_reverted_3146_, v_fst_3147_, v_n_3148_, v_j_3149_, v_a_3150_);
    crate::leanh::lean_dec(v_n_3148_);
    crate::leanh::lean_dec_ref(v_fst_3147_);
    crate::leanh::lean_dec_ref(v_reverted_3146_);
    crate::leanh::lean_dec(v___x_3145_);
    return v_res_3151_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__5(
    mut v_mvarId_3152_: *mut crate::leanh::LeanObject,
    mut v_as_3153_: *mut crate::leanh::LeanObject,
    mut v_i_3154_: usize,
    mut v_stop_3155_: usize,
    mut v_b_3156_: *mut crate::leanh::LeanObject,
    mut v___y_3157_: *mut crate::leanh::LeanObject,
    mut v___y_3158_: *mut crate::leanh::LeanObject,
    mut v___y_3159_: *mut crate::leanh::LeanObject,
    mut v___y_3160_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3162_: u8 = 0;
    let mut v_fst_3163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3167_: u8 = 0;
    let mut v___x_3168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3174_: usize = 0;
    let mut v___x_3175_: usize = 0;
    let mut v_reuseFailAlloc_3177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3181_: u8 = 0;
    let mut v___x_3183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3185_: u8 = 0;
    let mut v_isSharedCheck_3186_: u8 = 0;
    let mut v___x_3187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3162_ = lean_usize_dec_eq(v_i_3154_, v_stop_3155_);
                if v___x_3162_ == 0 {
                    v_fst_3163_ = crate::leanh::lean_ctor_get(v_b_3156_, 0);
                    v_snd_3164_ = crate::leanh::lean_ctor_get(v_b_3156_, 1);
                    v_isSharedCheck_3186_ = (!crate::leanh::lean_is_exclusive(v_b_3156_)) as u8;
                    if v_isSharedCheck_3186_ == 0 {
                        v___x_3166_ = v_b_3156_;
                        v_isShared_3167_ = v_isSharedCheck_3186_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3164_);
                        crate::leanh::lean_inc(v_fst_3163_);
                        crate::leanh::lean_dec(v_b_3156_);
                        v___x_3166_ = crate::leanh::lean_box(0);
                        v_isShared_3167_ = v_isSharedCheck_3186_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_mvarId_3152_);
                    v___x_3187_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3187_, 0, v_b_3156_);
                    return v___x_3187_;
                }
            }
            1 => {
                v___x_3168_ = lean_array_uget_borrowed(v_as_3153_, v_i_3154_);
                crate::leanh::lean_inc(v_mvarId_3152_);
                v___x_3169_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(
                    v_mvarId_3152_,
                    v_snd_3164_,
                    v___x_3168_,
                    v___y_3157_,
                    v___y_3158_,
                    v___y_3159_,
                    v___y_3160_,
                );
                if crate::leanh::lean_obj_tag(v___x_3169_) == 0 {
                    v_a_3170_ = crate::leanh::lean_ctor_get(v___x_3169_, 0);
                    crate::leanh::lean_inc(v_a_3170_);
                    crate::leanh::lean_dec_ref_known(v___x_3169_, 1);
                    crate::leanh::lean_inc(v___x_3168_);
                    v___x_3171_ = l_Lean_Expr_app___override(v_fst_3163_, v___x_3168_);
                    if v_isShared_3167_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3166_, 1, v_a_3170_);
                        crate::leanh::lean_ctor_set(v___x_3166_, 0, v___x_3171_);
                        v___x_3173_ = v___x_3166_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3177_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3177_, 0, v___x_3171_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3177_, 1, v_a_3170_);
                        v___x_3173_ = v_reuseFailAlloc_3177_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3166_);
                    crate::leanh::lean_dec(v_fst_3163_);
                    crate::leanh::lean_dec(v_mvarId_3152_);
                    v_a_3178_ = crate::leanh::lean_ctor_get(v___x_3169_, 0);
                    v_isSharedCheck_3185_ = (!crate::leanh::lean_is_exclusive(v___x_3169_)) as u8;
                    if v_isSharedCheck_3185_ == 0 {
                        v___x_3180_ = v___x_3169_;
                        v_isShared_3181_ = v_isSharedCheck_3185_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3178_);
                        crate::leanh::lean_dec(v___x_3169_);
                        v___x_3180_ = crate::leanh::lean_box(0);
                        v_isShared_3181_ = v_isSharedCheck_3185_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3174_ = 1usize;
                v___x_3175_ = lean_usize_add(v_i_3154_, v___x_3174_);
                v_i_3154_ = v___x_3175_;
                v_b_3156_ = v___x_3173_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_3181_ == 0 {
                    v___x_3183_ = v___x_3180_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3184_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3184_, 0, v_a_3178_);
                    v___x_3183_ = v_reuseFailAlloc_3184_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3183_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__5___boxed(
    mut v_mvarId_3188_: *mut crate::leanh::LeanObject,
    mut v_as_3189_: *mut crate::leanh::LeanObject,
    mut v_i_3190_: *mut crate::leanh::LeanObject,
    mut v_stop_3191_: *mut crate::leanh::LeanObject,
    mut v_b_3192_: *mut crate::leanh::LeanObject,
    mut v___y_3193_: *mut crate::leanh::LeanObject,
    mut v___y_3194_: *mut crate::leanh::LeanObject,
    mut v___y_3195_: *mut crate::leanh::LeanObject,
    mut v___y_3196_: *mut crate::leanh::LeanObject,
    mut v___y_3197_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3198_: usize = 0;
    let mut v_stop_boxed_3199_: usize = 0;
    let mut v_res_3200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3198_ = crate::leanh::lean_unbox_usize(v_i_3190_);
    crate::leanh::lean_dec(v_i_3190_);
    v_stop_boxed_3199_ = crate::leanh::lean_unbox_usize(v_stop_3191_);
    crate::leanh::lean_dec(v_stop_3191_);
    v_res_3200_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__5(v_mvarId_3188_, v_as_3189_, v_i_boxed_3198_, v_stop_boxed_3199_, v_b_3192_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_);
    crate::leanh::lean_dec(v___y_3196_);
    crate::leanh::lean_dec_ref(v___y_3195_);
    crate::leanh::lean_dec(v___y_3194_);
    crate::leanh::lean_dec_ref(v___y_3193_);
    crate::leanh::lean_dec_ref(v_as_3189_);
    return v_res_3200_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8_spec__9___redArg(
    mut v_x_3201_: *mut crate::leanh::LeanObject,
    mut v_x_3202_: *mut crate::leanh::LeanObject,
    mut v_x_3203_: *mut crate::leanh::LeanObject,
    mut v_x_3204_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_3205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3209_: u8 = 0;
    let mut v___x_3210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: u8 = 0;
    let mut v___x_3212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_3217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: u8 = 0;
    let mut v___x_3220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3230_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_3205_ = crate::leanh::lean_ctor_get(v_x_3201_, 0);
                v_vs_3206_ = crate::leanh::lean_ctor_get(v_x_3201_, 1);
                v_isSharedCheck_3230_ = (!crate::leanh::lean_is_exclusive(v_x_3201_)) as u8;
                if v_isSharedCheck_3230_ == 0 {
                    v___x_3208_ = v_x_3201_;
                    v_isShared_3209_ = v_isSharedCheck_3230_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_3206_);
                    crate::leanh::lean_inc(v_ks_3205_);
                    crate::leanh::lean_dec(v_x_3201_);
                    v___x_3208_ = crate::leanh::lean_box(0);
                    v_isShared_3209_ = v_isSharedCheck_3230_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3210_ = lean_array_get_size(v_ks_3205_);
                v___x_3211_ = lean_nat_dec_lt(v_x_3202_, v___x_3210_);
                if v___x_3211_ == 0 {
                    crate::leanh::lean_dec(v_x_3202_);
                    v___x_3212_ = lean_array_push(v_ks_3205_, v_x_3203_);
                    v___x_3213_ = lean_array_push(v_vs_3206_, v_x_3204_);
                    if v_isShared_3209_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3208_, 1, v___x_3213_);
                        crate::leanh::lean_ctor_set(v___x_3208_, 0, v___x_3212_);
                        v___x_3215_ = v___x_3208_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3216_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3216_, 0, v___x_3212_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3216_, 1, v___x_3213_);
                        v___x_3215_ = v_reuseFailAlloc_3216_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_3217_ = lean_array_fget_borrowed(v_ks_3205_, v_x_3202_);
                    v___x_3218_ = l_Lean_instBEqMVarId_beq(v_x_3203_, v_k_x27_3217_);
                    if v___x_3218_ == 0 {
                        if v_isShared_3209_ == 0 {
                            v___x_3220_ = v___x_3208_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3224_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3224_, 0, v_ks_3205_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3224_, 1, v_vs_3206_);
                            v___x_3220_ = v_reuseFailAlloc_3224_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_3225_ = lean_array_fset(v_ks_3205_, v_x_3202_, v_x_3203_);
                        v___x_3226_ = lean_array_fset(v_vs_3206_, v_x_3202_, v_x_3204_);
                        crate::leanh::lean_dec(v_x_3202_);
                        if v_isShared_3209_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3208_, 1, v___x_3226_);
                            crate::leanh::lean_ctor_set(v___x_3208_, 0, v___x_3225_);
                            v___x_3228_ = v___x_3208_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_3229_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3229_, 0, v___x_3225_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3229_, 1, v___x_3226_);
                            v___x_3228_ = v_reuseFailAlloc_3229_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_3215_;
            }
            3 => {
                v___x_3221_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3222_ = lean_nat_add(v_x_3202_, v___x_3221_);
                crate::leanh::lean_dec(v_x_3202_);
                v_x_3201_ = v___x_3220_;
                v_x_3202_ = v___x_3222_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_3228_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8___redArg(
    mut v_n_3231_: *mut crate::leanh::LeanObject,
    mut v_k_3232_: *mut crate::leanh::LeanObject,
    mut v_v_3233_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3234_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3235_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8_spec__9___redArg(v_n_3231_, v___x_3234_, v_k_3232_, v_v_3233_);
    return v___x_3235_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg___closed__0()
-> usize {
    let mut v___x_3236_: usize = 0;
    let mut v___x_3237_: usize = 0;
    let mut v___x_3238_: usize = 0;
    v___x_3236_ = 5usize;
    v___x_3237_ = 1usize;
    v___x_3238_ = lean_usize_shift_left(v___x_3237_, v___x_3236_);
    return v___x_3238_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg___closed__1()
-> usize {
    let mut v___x_3239_: usize = 0;
    let mut v___x_3240_: usize = 0;
    let mut v___x_3241_: usize = 0;
    v___x_3239_ = 1usize;
    v___x_3240_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg___closed__0);
    v___x_3241_ = lean_usize_sub(v___x_3240_, v___x_3239_);
    return v___x_3241_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3242_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_3242_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg(
    mut v_x_3243_: *mut crate::leanh::LeanObject,
    mut v_x_3244_: usize,
    mut v_x_3245_: usize,
    mut v_x_3246_: *mut crate::leanh::LeanObject,
    mut v_x_3247_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_3248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3249_: usize = 0;
    let mut v___x_3250_: usize = 0;
    let mut v___x_3251_: usize = 0;
    let mut v___x_3252_: usize = 0;
    let mut v_j_3253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: u8 = 0;
    let mut v___x_3257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3258_: u8 = 0;
    let mut v_v_3259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_3261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3272_: u8 = 0;
    let mut v___x_3273_: u8 = 0;
    let mut v___x_3274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3279_: u8 = 0;
    let mut v_node_3280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3283_: u8 = 0;
    let mut v___x_3284_: usize = 0;
    let mut v___x_3285_: usize = 0;
    let mut v___x_3286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3290_: u8 = 0;
    let mut v___x_3291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3292_: u8 = 0;
    let mut v_unused_3293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_3294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3298_: u8 = 0;
    let mut v___x_3300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_3301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3303_: u8 = 0;
    let mut v_ks_3304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: usize = 0;
    let mut v___x_3310_: u8 = 0;
    let mut v___x_3311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3313_: u8 = 0;
    let mut v_reuseFailAlloc_3314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3315_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3243_) == 0 {
                    v_es_3248_ = crate::leanh::lean_ctor_get(v_x_3243_, 0);
                    v___x_3249_ = 5usize;
                    v___x_3250_ = 1usize;
                    v___x_3251_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg___closed__1);
                    v___x_3252_ = lean_usize_land(v_x_3244_, v___x_3251_);
                    v_j_3253_ = lean_usize_to_nat(v___x_3252_);
                    v___x_3254_ = lean_array_get_size(v_es_3248_);
                    v___x_3255_ = lean_nat_dec_lt(v_j_3253_, v___x_3254_);
                    if v___x_3255_ == 0 {
                        crate::leanh::lean_dec(v_j_3253_);
                        crate::leanh::lean_dec(v_x_3247_);
                        crate::leanh::lean_dec(v_x_3246_);
                        return v_x_3243_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_3248_);
                        v_isSharedCheck_3292_ = (!crate::leanh::lean_is_exclusive(v_x_3243_)) as u8;
                        if v_isSharedCheck_3292_ == 0 {
                            v_unused_3293_ = crate::leanh::lean_ctor_get(v_x_3243_, 0);
                            crate::leanh::lean_dec(v_unused_3293_);
                            v___x_3257_ = v_x_3243_;
                            v_isShared_3258_ = v_isSharedCheck_3292_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_3243_);
                            v___x_3257_ = crate::leanh::lean_box(0);
                            v_isShared_3258_ = v_isSharedCheck_3292_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_3294_ = crate::leanh::lean_ctor_get(v_x_3243_, 0);
                    v_vs_3295_ = crate::leanh::lean_ctor_get(v_x_3243_, 1);
                    v_isSharedCheck_3315_ = (!crate::leanh::lean_is_exclusive(v_x_3243_)) as u8;
                    if v_isSharedCheck_3315_ == 0 {
                        v___x_3297_ = v_x_3243_;
                        v_isShared_3298_ = v_isSharedCheck_3315_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_3295_);
                        crate::leanh::lean_inc(v_ks_3294_);
                        crate::leanh::lean_dec(v_x_3243_);
                        v___x_3297_ = crate::leanh::lean_box(0);
                        v_isShared_3298_ = v_isSharedCheck_3315_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_3259_ = lean_array_fget(v_es_3248_, v_j_3253_);
                v___x_3260_ = crate::leanh::lean_box(0);
                v_xs_x27_3261_ = lean_array_fset(v_es_3248_, v_j_3253_, v___x_3260_);
                match crate::leanh::lean_obj_tag(v_v_3259_) {
                    0 => {
                        v_key_3268_ = crate::leanh::lean_ctor_get(v_v_3259_, 0);
                        v_val_3269_ = crate::leanh::lean_ctor_get(v_v_3259_, 1);
                        v_isSharedCheck_3279_ = (!crate::leanh::lean_is_exclusive(v_v_3259_)) as u8;
                        if v_isSharedCheck_3279_ == 0 {
                            v___x_3271_ = v_v_3259_;
                            v_isShared_3272_ = v_isSharedCheck_3279_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_3269_);
                            crate::leanh::lean_inc(v_key_3268_);
                            crate::leanh::lean_dec(v_v_3259_);
                            v___x_3271_ = crate::leanh::lean_box(0);
                            v_isShared_3272_ = v_isSharedCheck_3279_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_3280_ = crate::leanh::lean_ctor_get(v_v_3259_, 0);
                        v_isSharedCheck_3290_ = (!crate::leanh::lean_is_exclusive(v_v_3259_)) as u8;
                        if v_isSharedCheck_3290_ == 0 {
                            v___x_3282_ = v_v_3259_;
                            v_isShared_3283_ = v_isSharedCheck_3290_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_3280_);
                            crate::leanh::lean_dec(v_v_3259_);
                            v___x_3282_ = crate::leanh::lean_box(0);
                            v_isShared_3283_ = v_isSharedCheck_3290_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_3291_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3291_, 0, v_x_3246_);
                        crate::leanh::lean_ctor_set(v___x_3291_, 1, v_x_3247_);
                        v___y_3263_ = v___x_3291_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3264_ = lean_array_fset(v_xs_x27_3261_, v_j_3253_, v___y_3263_);
                crate::leanh::lean_dec(v_j_3253_);
                if v_isShared_3258_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3257_, 0, v___x_3264_);
                    v___x_3266_ = v___x_3257_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3267_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3267_, 0, v___x_3264_);
                    v___x_3266_ = v_reuseFailAlloc_3267_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3266_;
            }
            4 => {
                v___x_3273_ = l_Lean_instBEqMVarId_beq(v_x_3246_, v_key_3268_);
                if v___x_3273_ == 0 {
                    crate::leanh::lean_del_object(v___x_3271_);
                    v___x_3274_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_3268_,
                        v_val_3269_,
                        v_x_3246_,
                        v_x_3247_,
                    );
                    v___x_3275_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3275_, 0, v___x_3274_);
                    v___y_3263_ = v___x_3275_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_3269_);
                    crate::leanh::lean_dec(v_key_3268_);
                    if v_isShared_3272_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3271_, 1, v_x_3247_);
                        crate::leanh::lean_ctor_set(v___x_3271_, 0, v_x_3246_);
                        v___x_3277_ = v___x_3271_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3278_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3278_, 0, v_x_3246_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3278_, 1, v_x_3247_);
                        v___x_3277_ = v_reuseFailAlloc_3278_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_3263_ = v___x_3277_;
                state = 2;
                continue;
            }
            6 => {
                v___x_3284_ = lean_usize_shift_right(v_x_3244_, v___x_3249_);
                v___x_3285_ = lean_usize_add(v_x_3245_, v___x_3250_);
                v___x_3286_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg(v_node_3280_, v___x_3284_, v___x_3285_, v_x_3246_, v_x_3247_);
                if v_isShared_3283_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3282_, 0, v___x_3286_);
                    v___x_3288_ = v___x_3282_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3289_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3289_, 0, v___x_3286_);
                    v___x_3288_ = v_reuseFailAlloc_3289_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_3263_ = v___x_3288_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_3298_ == 0 {
                    v___x_3300_ = v___x_3297_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3314_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3314_, 0, v_ks_3294_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3314_, 1, v_vs_3295_);
                    v___x_3300_ = v_reuseFailAlloc_3314_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_3301_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8___redArg(v___x_3300_, v_x_3246_, v_x_3247_);
                v___x_3309_ = 7usize;
                v___x_3310_ = lean_usize_dec_le(v___x_3309_, v_x_3245_);
                if v___x_3310_ == 0 {
                    v___x_3311_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3301_);
                    v___x_3312_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_3313_ = lean_nat_dec_lt(v___x_3311_, v___x_3312_);
                    crate::leanh::lean_dec(v___x_3311_);
                    v___y_3303_ = v___x_3313_;
                    state = 10;
                    continue;
                } else {
                    v___y_3303_ = v___x_3310_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_3303_ == 0 {
                    v_ks_3304_ = crate::leanh::lean_ctor_get(v_newNode_3301_, 0);
                    crate::leanh::lean_inc_ref(v_ks_3304_);
                    v_vs_3305_ = crate::leanh::lean_ctor_get(v_newNode_3301_, 1);
                    crate::leanh::lean_inc_ref(v_vs_3305_);
                    crate::leanh::lean_dec_ref(v_newNode_3301_);
                    v___x_3306_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3307_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg___closed__2);
                    v___x_3308_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9___redArg(v_x_3245_, v_ks_3304_, v_vs_3305_, v___x_3306_, v___x_3307_);
                    crate::leanh::lean_dec_ref(v_vs_3305_);
                    crate::leanh::lean_dec_ref(v_ks_3304_);
                    return v___x_3308_;
                } else {
                    return v_newNode_3301_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9___redArg(
    mut v_depth_3316_: usize,
    mut v_keys_3317_: *mut crate::leanh::LeanObject,
    mut v_vals_3318_: *mut crate::leanh::LeanObject,
    mut v_i_3319_: *mut crate::leanh::LeanObject,
    mut v_entries_3320_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3322_: u8 = 0;
    let mut v_k_3323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3325_: u64 = 0;
    let mut v_h_3326_: usize = 0;
    let mut v___x_3327_: usize = 0;
    let mut v___x_3328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3329_: usize = 0;
    let mut v___x_3330_: usize = 0;
    let mut v___x_3331_: usize = 0;
    let mut v_h_3332_: usize = 0;
    let mut v___x_3333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3321_ = lean_array_get_size(v_keys_3317_);
                v___x_3322_ = lean_nat_dec_lt(v_i_3319_, v___x_3321_);
                if v___x_3322_ == 0 {
                    crate::leanh::lean_dec(v_i_3319_);
                    return v_entries_3320_;
                } else {
                    v_k_3323_ = lean_array_fget_borrowed(v_keys_3317_, v_i_3319_);
                    v_v_3324_ = lean_array_fget_borrowed(v_vals_3318_, v_i_3319_);
                    v___x_3325_ = l_Lean_instHashableMVarId_hash(v_k_3323_);
                    v_h_3326_ = lean_uint64_to_usize(v___x_3325_);
                    v___x_3327_ = 5usize;
                    v___x_3328_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3329_ = 1usize;
                    v___x_3330_ = lean_usize_sub(v_depth_3316_, v___x_3329_);
                    v___x_3331_ = lean_usize_mul(v___x_3327_, v___x_3330_);
                    v_h_3332_ = lean_usize_shift_right(v_h_3326_, v___x_3331_);
                    v___x_3333_ = lean_nat_add(v_i_3319_, v___x_3328_);
                    crate::leanh::lean_dec(v_i_3319_);
                    crate::leanh::lean_inc(v_v_3324_);
                    crate::leanh::lean_inc(v_k_3323_);
                    v___x_3334_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg(v_entries_3320_, v_h_3332_, v_depth_3316_, v_k_3323_, v_v_3324_);
                    v_i_3319_ = v___x_3333_;
                    v_entries_3320_ = v___x_3334_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9___redArg___boxed(
    mut v_depth_3336_: *mut crate::leanh::LeanObject,
    mut v_keys_3337_: *mut crate::leanh::LeanObject,
    mut v_vals_3338_: *mut crate::leanh::LeanObject,
    mut v_i_3339_: *mut crate::leanh::LeanObject,
    mut v_entries_3340_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_3341_: usize = 0;
    let mut v_res_3342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_3341_ = crate::leanh::lean_unbox_usize(v_depth_3336_);
    crate::leanh::lean_dec(v_depth_3336_);
    v_res_3342_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9___redArg(v_depth_boxed_3341_, v_keys_3337_, v_vals_3338_, v_i_3339_, v_entries_3340_);
    crate::leanh::lean_dec_ref(v_vals_3338_);
    crate::leanh::lean_dec_ref(v_keys_3337_);
    return v_res_3342_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_x_3343_: *mut crate::leanh::LeanObject,
    mut v_x_3344_: *mut crate::leanh::LeanObject,
    mut v_x_3345_: *mut crate::leanh::LeanObject,
    mut v_x_3346_: *mut crate::leanh::LeanObject,
    mut v_x_3347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_10137__boxed_3348_: usize = 0;
    let mut v_x_10138__boxed_3349_: usize = 0;
    let mut v_res_3350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_10137__boxed_3348_ = crate::leanh::lean_unbox_usize(v_x_3344_);
    crate::leanh::lean_dec(v_x_3344_);
    v_x_10138__boxed_3349_ = crate::leanh::lean_unbox_usize(v_x_3345_);
    crate::leanh::lean_dec(v_x_3345_);
    v_res_3350_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg(v_x_3343_, v_x_10137__boxed_3348_, v_x_10138__boxed_3349_, v_x_3346_, v_x_3347_);
    return v_res_3350_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0___redArg(
    mut v_x_3351_: *mut crate::leanh::LeanObject,
    mut v_x_3352_: *mut crate::leanh::LeanObject,
    mut v_x_3353_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3354_: u64 = 0;
    let mut v___x_3355_: usize = 0;
    let mut v___x_3356_: usize = 0;
    let mut v___x_3357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3354_ = l_Lean_instHashableMVarId_hash(v_x_3352_);
    v___x_3355_ = lean_uint64_to_usize(v___x_3354_);
    v___x_3356_ = 1usize;
    v___x_3357_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg(v_x_3351_, v___x_3355_, v___x_3356_, v_x_3352_, v_x_3353_);
    return v___x_3357_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___redArg(
    mut v_mvarId_3358_: *mut crate::leanh::LeanObject,
    mut v_val_3359_: *mut crate::leanh::LeanObject,
    mut v___y_3360_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_3366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3370_: u8 = 0;
    let mut v_depth_3371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_3372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_3373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_3374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lDecls_3375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_3376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userNames_3377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_3378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_3379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_3380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3383_: u8 = 0;
    let mut v___x_3384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3394_: u8 = 0;
    let mut v_isSharedCheck_3395_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3362_ = lean_st_ref_take(v___y_3360_);
                v_mctx_3363_ = crate::leanh::lean_ctor_get(v___x_3362_, 0);
                v_cache_3364_ = crate::leanh::lean_ctor_get(v___x_3362_, 1);
                v_zetaDeltaFVarIds_3365_ = crate::leanh::lean_ctor_get(v___x_3362_, 2);
                v_postponed_3366_ = crate::leanh::lean_ctor_get(v___x_3362_, 3);
                v_diag_3367_ = crate::leanh::lean_ctor_get(v___x_3362_, 4);
                v_isSharedCheck_3395_ = (!crate::leanh::lean_is_exclusive(v___x_3362_)) as u8;
                if v_isSharedCheck_3395_ == 0 {
                    v___x_3369_ = v___x_3362_;
                    v_isShared_3370_ = v_isSharedCheck_3395_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_3367_);
                    crate::leanh::lean_inc(v_postponed_3366_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_3365_);
                    crate::leanh::lean_inc(v_cache_3364_);
                    crate::leanh::lean_inc(v_mctx_3363_);
                    crate::leanh::lean_dec(v___x_3362_);
                    v___x_3369_ = crate::leanh::lean_box(0);
                    v_isShared_3370_ = v_isSharedCheck_3395_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_3371_ = crate::leanh::lean_ctor_get(v_mctx_3363_, 0);
                v_levelAssignDepth_3372_ = crate::leanh::lean_ctor_get(v_mctx_3363_, 1);
                v_lmvarCounter_3373_ = crate::leanh::lean_ctor_get(v_mctx_3363_, 2);
                v_mvarCounter_3374_ = crate::leanh::lean_ctor_get(v_mctx_3363_, 3);
                v_lDecls_3375_ = crate::leanh::lean_ctor_get(v_mctx_3363_, 4);
                v_decls_3376_ = crate::leanh::lean_ctor_get(v_mctx_3363_, 5);
                v_userNames_3377_ = crate::leanh::lean_ctor_get(v_mctx_3363_, 6);
                v_lAssignment_3378_ = crate::leanh::lean_ctor_get(v_mctx_3363_, 7);
                v_eAssignment_3379_ = crate::leanh::lean_ctor_get(v_mctx_3363_, 8);
                v_dAssignment_3380_ = crate::leanh::lean_ctor_get(v_mctx_3363_, 9);
                v_isSharedCheck_3394_ = (!crate::leanh::lean_is_exclusive(v_mctx_3363_)) as u8;
                if v_isSharedCheck_3394_ == 0 {
                    v___x_3382_ = v_mctx_3363_;
                    v_isShared_3383_ = v_isSharedCheck_3394_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_dAssignment_3380_);
                    crate::leanh::lean_inc(v_eAssignment_3379_);
                    crate::leanh::lean_inc(v_lAssignment_3378_);
                    crate::leanh::lean_inc(v_userNames_3377_);
                    crate::leanh::lean_inc(v_decls_3376_);
                    crate::leanh::lean_inc(v_lDecls_3375_);
                    crate::leanh::lean_inc(v_mvarCounter_3374_);
                    crate::leanh::lean_inc(v_lmvarCounter_3373_);
                    crate::leanh::lean_inc(v_levelAssignDepth_3372_);
                    crate::leanh::lean_inc(v_depth_3371_);
                    crate::leanh::lean_dec(v_mctx_3363_);
                    v___x_3382_ = crate::leanh::lean_box(0);
                    v_isShared_3383_ = v_isSharedCheck_3394_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3384_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0___redArg(v_eAssignment_3379_, v_mvarId_3358_, v_val_3359_);
                if v_isShared_3383_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3382_, 8, v___x_3384_);
                    v___x_3386_ = v___x_3382_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3393_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3393_, 0, v_depth_3371_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3393_,
                        1,
                        v_levelAssignDepth_3372_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3393_, 2, v_lmvarCounter_3373_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3393_, 3, v_mvarCounter_3374_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3393_, 4, v_lDecls_3375_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3393_, 5, v_decls_3376_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3393_, 6, v_userNames_3377_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3393_, 7, v_lAssignment_3378_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3393_, 8, v___x_3384_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3393_, 9, v_dAssignment_3380_);
                    v___x_3386_ = v_reuseFailAlloc_3393_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3370_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3369_, 0, v___x_3386_);
                    v___x_3388_ = v___x_3369_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3392_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3392_, 0, v___x_3386_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3392_, 1, v_cache_3364_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3392_,
                        2,
                        v_zetaDeltaFVarIds_3365_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3392_, 3, v_postponed_3366_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3392_, 4, v_diag_3367_);
                    v___x_3388_ = v_reuseFailAlloc_3392_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3389_ = lean_st_ref_set(v___y_3360_, v___x_3388_);
                v___x_3390_ = crate::leanh::lean_box(0);
                v___x_3391_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3391_, 0, v___x_3390_);
                return v___x_3391_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___redArg___boxed(
    mut v_mvarId_3396_: *mut crate::leanh::LeanObject,
    mut v_val_3397_: *mut crate::leanh::LeanObject,
    mut v___y_3398_: *mut crate::leanh::LeanObject,
    mut v___y_3399_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3400_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___redArg(v_mvarId_3396_, v_val_3397_, v___y_3398_);
    crate::leanh::lean_dec(v___y_3398_);
    return v_res_3400_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1_spec__2(
    mut v_msgData_3401_: *mut crate::leanh::LeanObject,
    mut v___y_3402_: *mut crate::leanh::LeanObject,
    mut v___y_3403_: *mut crate::leanh::LeanObject,
    mut v___y_3404_: *mut crate::leanh::LeanObject,
    mut v___y_3405_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3407_ = lean_st_ref_get(v___y_3405_);
    v_env_3408_ = crate::leanh::lean_ctor_get(v___x_3407_, 0);
    crate::leanh::lean_inc_ref(v_env_3408_);
    crate::leanh::lean_dec(v___x_3407_);
    v___x_3409_ = lean_st_ref_get(v___y_3403_);
    v_mctx_3410_ = crate::leanh::lean_ctor_get(v___x_3409_, 0);
    crate::leanh::lean_inc_ref(v_mctx_3410_);
    crate::leanh::lean_dec(v___x_3409_);
    v_lctx_3411_ = crate::leanh::lean_ctor_get(v___y_3402_, 2);
    v_options_3412_ = crate::leanh::lean_ctor_get(v___y_3404_, 2);
    crate::leanh::lean_inc_ref(v_options_3412_);
    crate::leanh::lean_inc_ref(v_lctx_3411_);
    v___x_3413_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3413_, 0, v_env_3408_);
    crate::leanh::lean_ctor_set(v___x_3413_, 1, v_mctx_3410_);
    crate::leanh::lean_ctor_set(v___x_3413_, 2, v_lctx_3411_);
    crate::leanh::lean_ctor_set(v___x_3413_, 3, v_options_3412_);
    v___x_3414_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3414_, 0, v___x_3413_);
    crate::leanh::lean_ctor_set(v___x_3414_, 1, v_msgData_3401_);
    v___x_3415_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3415_, 0, v___x_3414_);
    return v___x_3415_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1_spec__2___boxed(
    mut v_msgData_3416_: *mut crate::leanh::LeanObject,
    mut v___y_3417_: *mut crate::leanh::LeanObject,
    mut v___y_3418_: *mut crate::leanh::LeanObject,
    mut v___y_3419_: *mut crate::leanh::LeanObject,
    mut v___y_3420_: *mut crate::leanh::LeanObject,
    mut v___y_3421_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3422_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1_spec__2(v_msgData_3416_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_);
    crate::leanh::lean_dec(v___y_3420_);
    crate::leanh::lean_dec_ref(v___y_3419_);
    crate::leanh::lean_dec(v___y_3418_);
    crate::leanh::lean_dec_ref(v___y_3417_);
    return v_res_3422_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__0()
-> f64 {
    let mut v___x_3423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3424_: f64 = 0.0;
    v___x_3423_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3424_ = lean_float_of_nat(v___x_3423_);
    return v___x_3424_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(
    mut v_cls_3428_: *mut crate::leanh::LeanObject,
    mut v_msg_3429_: *mut crate::leanh::LeanObject,
    mut v___y_3430_: *mut crate::leanh::LeanObject,
    mut v___y_3431_: *mut crate::leanh::LeanObject,
    mut v___y_3432_: *mut crate::leanh::LeanObject,
    mut v___y_3433_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_3435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3440_: u8 = 0;
    let mut v___x_3441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3453_: u8 = 0;
    let mut v_tid_3454_: u64 = 0;
    let mut v_traces_3455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3458_: u8 = 0;
    let mut v___x_3459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3460_: f64 = 0.0;
    let mut v___x_3461_: u8 = 0;
    let mut v___x_3462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3479_: u8 = 0;
    let mut v_isSharedCheck_3480_: u8 = 0;
    let mut v_isSharedCheck_3481_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3435_ = crate::leanh::lean_ctor_get(v___y_3432_, 5);
                v___x_3436_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1_spec__2(v_msg_3429_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_);
                v_a_3437_ = crate::leanh::lean_ctor_get(v___x_3436_, 0);
                v_isSharedCheck_3481_ = (!crate::leanh::lean_is_exclusive(v___x_3436_)) as u8;
                if v_isSharedCheck_3481_ == 0 {
                    v___x_3439_ = v___x_3436_;
                    v_isShared_3440_ = v_isSharedCheck_3481_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3437_);
                    crate::leanh::lean_dec(v___x_3436_);
                    v___x_3439_ = crate::leanh::lean_box(0);
                    v_isShared_3440_ = v_isSharedCheck_3481_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3441_ = lean_st_ref_take(v___y_3433_);
                v_traceState_3442_ = crate::leanh::lean_ctor_get(v___x_3441_, 4);
                v_env_3443_ = crate::leanh::lean_ctor_get(v___x_3441_, 0);
                v_nextMacroScope_3444_ = crate::leanh::lean_ctor_get(v___x_3441_, 1);
                v_ngen_3445_ = crate::leanh::lean_ctor_get(v___x_3441_, 2);
                v_auxDeclNGen_3446_ = crate::leanh::lean_ctor_get(v___x_3441_, 3);
                v_cache_3447_ = crate::leanh::lean_ctor_get(v___x_3441_, 5);
                v_messages_3448_ = crate::leanh::lean_ctor_get(v___x_3441_, 6);
                v_infoState_3449_ = crate::leanh::lean_ctor_get(v___x_3441_, 7);
                v_snapshotTasks_3450_ = crate::leanh::lean_ctor_get(v___x_3441_, 8);
                v_isSharedCheck_3480_ = (!crate::leanh::lean_is_exclusive(v___x_3441_)) as u8;
                if v_isSharedCheck_3480_ == 0 {
                    v___x_3452_ = v___x_3441_;
                    v_isShared_3453_ = v_isSharedCheck_3480_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_3450_);
                    crate::leanh::lean_inc(v_infoState_3449_);
                    crate::leanh::lean_inc(v_messages_3448_);
                    crate::leanh::lean_inc(v_cache_3447_);
                    crate::leanh::lean_inc(v_traceState_3442_);
                    crate::leanh::lean_inc(v_auxDeclNGen_3446_);
                    crate::leanh::lean_inc(v_ngen_3445_);
                    crate::leanh::lean_inc(v_nextMacroScope_3444_);
                    crate::leanh::lean_inc(v_env_3443_);
                    crate::leanh::lean_dec(v___x_3441_);
                    v___x_3452_ = crate::leanh::lean_box(0);
                    v_isShared_3453_ = v_isSharedCheck_3480_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_3454_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_3442_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_3455_ = crate::leanh::lean_ctor_get(v_traceState_3442_, 0);
                v_isSharedCheck_3479_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_3442_)) as u8;
                if v_isSharedCheck_3479_ == 0 {
                    v___x_3457_ = v_traceState_3442_;
                    v_isShared_3458_ = v_isSharedCheck_3479_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_3455_);
                    crate::leanh::lean_dec(v_traceState_3442_);
                    v___x_3457_ = crate::leanh::lean_box(0);
                    v_isShared_3458_ = v_isSharedCheck_3479_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3459_ = crate::leanh::lean_box(0);
                v___x_3460_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__0_once), _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__0);
                v___x_3461_ = 0;
                v___x_3462_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__1;
                v___x_3463_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v___x_3463_, 0, v_cls_3428_);
                crate::leanh::lean_ctor_set(v___x_3463_, 1, v___x_3459_);
                crate::leanh::lean_ctor_set(v___x_3463_, 2, v___x_3462_);
                crate::leanh::lean_ctor_set_float(
                    v___x_3463_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_3460_,
                );
                crate::leanh::lean_ctor_set_float(
                    v___x_3463_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_3460_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3463_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_3461_,
                );
                v___x_3464_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___closed__2;
                v___x_3465_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3465_, 0, v___x_3463_);
                crate::leanh::lean_ctor_set(v___x_3465_, 1, v_a_3437_);
                crate::leanh::lean_ctor_set(v___x_3465_, 2, v___x_3464_);
                crate::leanh::lean_inc(v_ref_3435_);
                v___x_3466_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3466_, 0, v_ref_3435_);
                crate::leanh::lean_ctor_set(v___x_3466_, 1, v___x_3465_);
                v___x_3467_ = l_Lean_PersistentArray_push___redArg(v_traces_3455_, v___x_3466_);
                if v_isShared_3458_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3457_, 0, v___x_3467_);
                    v___x_3469_ = v___x_3457_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3478_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3478_, 0, v___x_3467_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_3478_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_3454_,
                    );
                    v___x_3469_ = v_reuseFailAlloc_3478_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3453_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3452_, 4, v___x_3469_);
                    v___x_3471_ = v___x_3452_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3477_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3477_, 0, v_env_3443_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3477_, 1, v_nextMacroScope_3444_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3477_, 2, v_ngen_3445_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3477_, 3, v_auxDeclNGen_3446_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3477_, 4, v___x_3469_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3477_, 5, v_cache_3447_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3477_, 6, v_messages_3448_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3477_, 7, v_infoState_3449_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3477_, 8, v_snapshotTasks_3450_);
                    v___x_3471_ = v_reuseFailAlloc_3477_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3472_ = lean_st_ref_set(v___y_3433_, v___x_3471_);
                v___x_3473_ = crate::leanh::lean_box(0);
                if v_isShared_3440_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3439_, 0, v___x_3473_);
                    v___x_3475_ = v___x_3439_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3476_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3476_, 0, v___x_3473_);
                    v___x_3475_ = v_reuseFailAlloc_3476_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3475_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1___boxed(
    mut v_cls_3482_: *mut crate::leanh::LeanObject,
    mut v_msg_3483_: *mut crate::leanh::LeanObject,
    mut v___y_3484_: *mut crate::leanh::LeanObject,
    mut v___y_3485_: *mut crate::leanh::LeanObject,
    mut v___y_3486_: *mut crate::leanh::LeanObject,
    mut v___y_3487_: *mut crate::leanh::LeanObject,
    mut v___y_3488_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3489_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v_cls_3482_, v_msg_3483_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_);
    crate::leanh::lean_dec(v___y_3487_);
    crate::leanh::lean_dec_ref(v___y_3486_);
    crate::leanh::lean_dec(v___y_3485_);
    crate::leanh::lean_dec_ref(v___y_3484_);
    return v_res_3489_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(
    mut v_sz_3490_: usize,
    mut v_i_3491_: usize,
    mut v_bs_3492_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3493_: u8 = 0;
    let mut v_v_3494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3498_: usize = 0;
    let mut v___x_3499_: usize = 0;
    let mut v___x_3500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3493_ = lean_usize_dec_lt(v_i_3491_, v_sz_3490_);
                if v___x_3493_ == 0 {
                    return v_bs_3492_;
                } else {
                    v_v_3494_ = lean_array_uget(v_bs_3492_, v_i_3491_);
                    v___x_3495_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_3496_ = lean_array_uset(v_bs_3492_, v_i_3491_, v___x_3495_);
                    v___x_3497_ = l_Lean_mkFVar(v_v_3494_);
                    v___x_3498_ = 1usize;
                    v___x_3499_ = lean_usize_add(v_i_3491_, v___x_3498_);
                    v___x_3500_ = lean_array_uset(v_bs_x27_3496_, v_i_3491_, v___x_3497_);
                    v_i_3491_ = v___x_3499_;
                    v_bs_3492_ = v___x_3500_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3___boxed(
    mut v_sz_3502_: *mut crate::leanh::LeanObject,
    mut v_i_3503_: *mut crate::leanh::LeanObject,
    mut v_bs_3504_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3505_: usize = 0;
    let mut v_i_boxed_3506_: usize = 0;
    let mut v_res_3507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3505_ = crate::leanh::lean_unbox_usize(v_sz_3502_);
    crate::leanh::lean_dec(v_sz_3502_);
    v_i_boxed_3506_ = crate::leanh::lean_unbox_usize(v_i_3503_);
    crate::leanh::lean_dec(v_i_3503_);
    v_res_3507_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(v_sz_boxed_3505_, v_i_boxed_3506_, v_bs_3504_);
    return v_res_3507_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3517_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2;
    v___x_3518_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__4;
    v___x_3519_ = l_Lean_Name_append(v___x_3518_, v___x_3517_);
    return v___x_3519_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3521_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__6;
    v___x_3522_ = l_Lean_stringToMessageData(v___x_3521_);
    return v___x_3522_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3524_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__8;
    v___x_3525_ = l_Lean_stringToMessageData(v___x_3524_);
    return v___x_3525_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3527_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__10;
    v___x_3528_ = l_Lean_stringToMessageData(v___x_3527_);
    return v___x_3528_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3532_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__14;
    v___x_3533_ = crate::leanh::lean_unsigned_to_nat(15);
    v___x_3534_ = crate::leanh::lean_unsigned_to_nat(120);
    v___x_3535_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__13;
    v___x_3536_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__12;
    v___x_3537_ = l_mkPanicMessageWithDecl(
        v___x_3536_,
        v___x_3535_,
        v___x_3534_,
        v___x_3533_,
        v___x_3532_,
    );
    return v___x_3537_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop(
    mut v_mvarId_3538_: *mut crate::leanh::LeanObject,
    mut v_givenNames_3539_: *mut crate::leanh::LeanObject,
    mut v_recursorInfo_3540_: *mut crate::leanh::LeanObject,
    mut v_reverted_3541_: *mut crate::leanh::LeanObject,
    mut v_major_3542_: *mut crate::leanh::LeanObject,
    mut v_indices_3543_: *mut crate::leanh::LeanObject,
    mut v_baseSubst_3544_: *mut crate::leanh::LeanObject,
    mut v_initialArity_3545_: *mut crate::leanh::LeanObject,
    mut v_numMinors_3546_: *mut crate::leanh::LeanObject,
    mut v_pos_3547_: *mut crate::leanh::LeanObject,
    mut v_minorIdx_3548_: *mut crate::leanh::LeanObject,
    mut v_recursor_3549_: *mut crate::leanh::LeanObject,
    mut v_recursorType_3550_: *mut crate::leanh::LeanObject,
    mut v_consumedMajor_3551_: u8,
    mut v_subgoals_3552_: *mut crate::leanh::LeanObject,
    mut v_a_3553_: *mut crate::leanh::LeanObject,
    mut v_a_3554_: *mut crate::leanh::LeanObject,
    mut v_a_3555_: *mut crate::leanh::LeanObject,
    mut v_a_3556_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3566_: u8 = 0;
    let mut v_options_3567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3568_: u8 = 0;
    let mut v___x_3570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_3572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: u8 = 0;
    let mut v___x_3577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3590_: u8 = 0;
    let mut v___x_3592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3594_: u8 = 0;
    let mut v_unused_3595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3599_: u8 = 0;
    let mut v___x_3601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3603_: u8 = 0;
    let mut v_isSharedCheck_3604_: u8 = 0;
    let mut v_unused_3605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3609_: u8 = 0;
    let mut v___x_3611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3613_: u8 = 0;
    let mut v___y_3615_: u8 = 0;
    let mut v___y_3616_: u8 = 0;
    let mut v___y_3617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3630_: u8 = 0;
    let mut v___x_3631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3641_: usize = 0;
    let mut v___x_3642_: usize = 0;
    let mut v___x_3643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3652_: u8 = 0;
    let mut v___x_3654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3656_: u8 = 0;
    let mut v_a_3657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3660_: u8 = 0;
    let mut v___x_3662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3664_: u8 = 0;
    let mut v___y_3666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3667_: u8 = 0;
    let mut v___y_3668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3670_: u8 = 0;
    let mut v___y_3671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_explicit_3684_: u8 = 0;
    let mut v_a_3685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_varNames_3686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_varNames_3688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3692_: u8 = 0;
    let mut v___x_3694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3696_: u8 = 0;
    let mut v___y_3698_: u8 = 0;
    let mut v___y_3699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3712_: u8 = 0;
    let mut v___x_3714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3716_: u8 = 0;
    let mut v___y_3718_: u8 = 0;
    let mut v___y_3719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3727_: u8 = 0;
    let mut v___x_3729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3731_: u8 = 0;
    let mut v___x_3732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3737_: u8 = 0;
    let mut v___y_3738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3739_: u8 = 0;
    let mut v___y_3740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_3754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3755_: u8 = 0;
    let mut v___x_3756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3759_: u8 = 0;
    let mut v___x_3760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3768_: u8 = 0;
    let mut v___x_3770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3772_: u8 = 0;
    let mut v_a_3773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3776_: u8 = 0;
    let mut v___x_3778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3780_: u8 = 0;
    let mut v_a_3781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3784_: u8 = 0;
    let mut v___x_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3788_: u8 = 0;
    let mut v___y_3790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3791_: u8 = 0;
    let mut v___y_3792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3793_: u8 = 0;
    let mut v___y_3794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3806_: u8 = 0;
    let mut v___x_3807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3813_: u8 = 0;
    let mut v___y_3814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3819_: u8 = 0;
    let mut v___x_3820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3821_: u8 = 0;
    let mut v___x_3822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3828_: u8 = 0;
    let mut v___x_3830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3832_: u8 = 0;
    let mut v___x_3833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3852_: u8 = 0;
    let mut v___x_3854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3856_: u8 = 0;
    let mut v_a_3857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3860_: u8 = 0;
    let mut v___x_3862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3864_: u8 = 0;
    let mut v_val_3865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3875_: u8 = 0;
    let mut v___x_3877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3879_: u8 = 0;
    let mut v_a_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3883_: u8 = 0;
    let mut v___x_3885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3887_: u8 = 0;
    let mut v___y_3889_: u8 = 0;
    let mut v___y_3890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3896_: u8 = 0;
    let mut v___y_3897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: u8 = 0;
    let mut v___x_3899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3901_: u8 = 0;
    let mut v___y_3903_: u8 = 0;
    let mut v___y_3904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_3909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_3910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_3911_: u8 = 0;
    let mut v___x_3912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3914_: u8 = 0;
    let mut v___x_3915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3920_: u8 = 0;
    let mut v___x_3921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3927_: u8 = 0;
    let mut v___x_3929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3931_: u8 = 0;
    let mut v___x_3932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3933_: u8 = 0;
    let mut v___x_3934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3936_: u8 = 0;
    let mut v___x_3937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3943_: u8 = 0;
    let mut v___x_3945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3947_: u8 = 0;
    let mut v_a_3948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3951_: u8 = 0;
    let mut v___x_3953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3955_: u8 = 0;
    let mut v___x_3956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3958_: u8 = 0;
    let mut v___x_3959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3960_: u8 = 0;
    let mut v___x_3961_: usize = 0;
    let mut v___x_3962_: usize = 0;
    let mut v___x_3963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: usize = 0;
    let mut v___x_3965_: usize = 0;
    let mut v___x_3966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: u8 = 0;
    let mut v_numArgs_3968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3969_: u8 = 0;
    let mut v_a_3970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3973_: u8 = 0;
    let mut v___x_3975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3977_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3732_ = l_Lean_Meta_whnfForall(
                    v_recursorType_3550_,
                    v_a_3553_,
                    v_a_3554_,
                    v_a_3555_,
                    v_a_3556_,
                );
                if crate::leanh::lean_obj_tag(v___x_3732_) == 0 {
                    v_a_3733_ = crate::leanh::lean_ctor_get(v___x_3732_, 0);
                    crate::leanh::lean_inc(v_a_3733_);
                    crate::leanh::lean_dec_ref_known(v___x_3732_, 1);
                    v___x_3967_ = l_Lean_Expr_isForall(v_a_3733_);
                    if v___x_3967_ == 0 {
                        v___y_3920_ = v___x_3967_;
                        state = 46;
                        continue;
                    } else {
                        v_numArgs_3968_ = crate::leanh::lean_ctor_get(v_recursorInfo_3540_, 3);
                        v___x_3969_ = lean_nat_dec_lt(v_pos_3547_, v_numArgs_3968_);
                        v___y_3920_ = v___x_3969_;
                        state = 46;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_subgoals_3552_);
                    crate::leanh::lean_dec_ref(v_recursor_3549_);
                    crate::leanh::lean_dec(v_minorIdx_3548_);
                    crate::leanh::lean_dec(v_pos_3547_);
                    crate::leanh::lean_dec(v_baseSubst_3544_);
                    crate::leanh::lean_dec_ref(v_major_3542_);
                    crate::leanh::lean_dec(v_mvarId_3538_);
                    v_a_3970_ = crate::leanh::lean_ctor_get(v___x_3732_, 0);
                    v_isSharedCheck_3977_ = (!crate::leanh::lean_is_exclusive(v___x_3732_)) as u8;
                    if v_isSharedCheck_3977_ == 0 {
                        v___x_3972_ = v___x_3732_;
                        v_isShared_3973_ = v_isSharedCheck_3977_;
                        state = 53;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3970_);
                        crate::leanh::lean_dec(v___x_3732_);
                        v___x_3972_ = crate::leanh::lean_box(0);
                        v_isShared_3973_ = v_isSharedCheck_3977_;
                        state = 53;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3563_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___redArg(v_mvarId_3538_, v_recursor_3549_, v___y_3560_);
                if crate::leanh::lean_obj_tag(v___x_3563_) == 0 {
                    v_isSharedCheck_3604_ = (!crate::leanh::lean_is_exclusive(v___x_3563_)) as u8;
                    if v_isSharedCheck_3604_ == 0 {
                        v_unused_3605_ = crate::leanh::lean_ctor_get(v___x_3563_, 0);
                        crate::leanh::lean_dec(v_unused_3605_);
                        v___x_3565_ = v___x_3563_;
                        v_isShared_3566_ = v_isSharedCheck_3604_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_3563_);
                        v___x_3565_ = crate::leanh::lean_box(0);
                        v_isShared_3566_ = v_isSharedCheck_3604_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_subgoals_3552_);
                    v_a_3606_ = crate::leanh::lean_ctor_get(v___x_3563_, 0);
                    v_isSharedCheck_3613_ = (!crate::leanh::lean_is_exclusive(v___x_3563_)) as u8;
                    if v_isSharedCheck_3613_ == 0 {
                        v___x_3608_ = v___x_3563_;
                        v_isShared_3609_ = v_isSharedCheck_3613_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3606_);
                        crate::leanh::lean_dec(v___x_3563_);
                        v___x_3608_ = crate::leanh::lean_box(0);
                        v_isShared_3609_ = v_isSharedCheck_3613_;
                        state = 9;
                        continue;
                    }
                }
            }
            2 => {
                v_options_3567_ = crate::leanh::lean_ctor_get(v___y_3561_, 2);
                v_hasTrace_3568_ = crate::leanh::lean_ctor_get_uint8(
                    v_options_3567_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                if v_hasTrace_3568_ == 0 {
                    if v_isShared_3566_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3565_, 0, v_subgoals_3552_);
                        v___x_3570_ = v___x_3565_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3571_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3571_, 0, v_subgoals_3552_);
                        v___x_3570_ = v_reuseFailAlloc_3571_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_inheritedTraceOptions_3572_ = crate::leanh::lean_ctor_get(v___y_3561_, 13);
                    v___x_3573_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2;
                    v___x_3574_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5_once), _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5);
                    v___x_3575_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_3572_,
                        v_options_3567_,
                        v___x_3574_,
                    );
                    if v___x_3575_ == 0 {
                        if v_isShared_3566_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3565_, 0, v_subgoals_3552_);
                            v___x_3577_ = v___x_3565_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_3578_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_3578_,
                                0,
                                v_subgoals_3552_,
                            );
                            v___x_3577_ = v_reuseFailAlloc_3578_;
                            state = 4;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_3565_);
                        v___x_3579_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__7_once), _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__7);
                        v___x_3580_ = lean_array_get_size(v_subgoals_3552_);
                        v___x_3581_ = l_Nat_reprFast(v___x_3580_);
                        v___x_3582_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3582_, 0, v___x_3581_);
                        v___x_3583_ = l_Lean_MessageData_ofFormat(v___x_3582_);
                        v___x_3584_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3584_, 0, v___x_3579_);
                        crate::leanh::lean_ctor_set(v___x_3584_, 1, v___x_3583_);
                        v___x_3585_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__9_once), _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__9);
                        v___x_3586_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3586_, 0, v___x_3584_);
                        crate::leanh::lean_ctor_set(v___x_3586_, 1, v___x_3585_);
                        v___x_3587_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v___x_3573_, v___x_3586_, v___y_3559_, v___y_3560_, v___y_3561_, v___y_3562_);
                        if crate::leanh::lean_obj_tag(v___x_3587_) == 0 {
                            v_isSharedCheck_3594_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3587_)) as u8;
                            if v_isSharedCheck_3594_ == 0 {
                                v_unused_3595_ = crate::leanh::lean_ctor_get(v___x_3587_, 0);
                                crate::leanh::lean_dec(v_unused_3595_);
                                v___x_3589_ = v___x_3587_;
                                v_isShared_3590_ = v_isSharedCheck_3594_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_3587_);
                                v___x_3589_ = crate::leanh::lean_box(0);
                                v_isShared_3590_ = v_isSharedCheck_3594_;
                                state = 5;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_subgoals_3552_);
                            v_a_3596_ = crate::leanh::lean_ctor_get(v___x_3587_, 0);
                            v_isSharedCheck_3603_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3587_)) as u8;
                            if v_isSharedCheck_3603_ == 0 {
                                v___x_3598_ = v___x_3587_;
                                v_isShared_3599_ = v_isSharedCheck_3603_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3596_);
                                crate::leanh::lean_dec(v___x_3587_);
                                v___x_3598_ = crate::leanh::lean_box(0);
                                v_isShared_3599_ = v_isSharedCheck_3603_;
                                state = 7;
                                continue;
                            }
                        }
                    }
                }
            }
            3 => {
                return v___x_3570_;
            }
            4 => {
                return v___x_3577_;
            }
            5 => {
                if v_isShared_3590_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3589_, 0, v_subgoals_3552_);
                    v___x_3592_ = v___x_3589_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3593_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3593_, 0, v_subgoals_3552_);
                    v___x_3592_ = v_reuseFailAlloc_3593_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3592_;
            }
            7 => {
                if v_isShared_3599_ == 0 {
                    v___x_3601_ = v___x_3598_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3602_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3602_, 0, v_a_3596_);
                    v___x_3601_ = v_reuseFailAlloc_3602_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3601_;
            }
            9 => {
                if v_isShared_3609_ == 0 {
                    v___x_3611_ = v___x_3608_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3612_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3612_, 0, v_a_3606_);
                    v___x_3611_ = v_reuseFailAlloc_3612_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3611_;
            }
            11 => {
                v___x_3631_ = l_Lean_Meta_introNCore(
                    v___y_3622_,
                    v___y_3628_,
                    v___y_3617_,
                    v___y_3630_,
                    v___y_3616_,
                    v___y_3629_,
                    v___y_3620_,
                    v___y_3619_,
                    v___y_3618_,
                );
                if crate::leanh::lean_obj_tag(v___x_3631_) == 0 {
                    v_a_3632_ = crate::leanh::lean_ctor_get(v___x_3631_, 0);
                    crate::leanh::lean_inc(v_a_3632_);
                    crate::leanh::lean_dec_ref_known(v___x_3631_, 1);
                    v_fst_3633_ = crate::leanh::lean_ctor_get(v_a_3632_, 0);
                    crate::leanh::lean_inc(v_fst_3633_);
                    v_snd_3634_ = crate::leanh::lean_ctor_get(v_a_3632_, 1);
                    crate::leanh::lean_inc(v_snd_3634_);
                    crate::leanh::lean_dec(v_a_3632_);
                    v___x_3635_ = crate::leanh::lean_box(0);
                    v___x_3636_ = l_Lean_Meta_introNCore(
                        v_snd_3634_,
                        v___y_3623_,
                        v___x_3635_,
                        v___y_3616_,
                        v___y_3615_,
                        v___y_3629_,
                        v___y_3620_,
                        v___y_3619_,
                        v___y_3618_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3636_) == 0 {
                        v_a_3637_ = crate::leanh::lean_ctor_get(v___x_3636_, 0);
                        crate::leanh::lean_inc(v_a_3637_);
                        crate::leanh::lean_dec_ref_known(v___x_3636_, 1);
                        v_fst_3638_ = crate::leanh::lean_ctor_get(v_a_3637_, 0);
                        crate::leanh::lean_inc(v_fst_3638_);
                        v_snd_3639_ = crate::leanh::lean_ctor_get(v_a_3637_, 1);
                        crate::leanh::lean_inc(v_snd_3639_);
                        crate::leanh::lean_dec(v_a_3637_);
                        crate::leanh::lean_inc(v_baseSubst_3544_);
                        crate::leanh::lean_inc(v___y_3627_);
                        v___x_3640_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2___redArg(v___y_3621_, v_reverted_3541_, v_fst_3638_, v___y_3627_, v___y_3627_, v_baseSubst_3544_);
                        crate::leanh::lean_dec(v___y_3627_);
                        crate::leanh::lean_dec(v_fst_3638_);
                        crate::leanh::lean_dec(v___y_3621_);
                        v_sz_3641_ = lean_array_size(v_fst_3633_);
                        v___x_3642_ = 0usize;
                        v___x_3643_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(v_sz_3641_, v___x_3642_, v_fst_3633_);
                        v___x_3644_ = lean_nat_add(v_pos_3547_, v___y_3626_);
                        crate::leanh::lean_dec(v_pos_3547_);
                        v___x_3645_ = lean_nat_add(v_minorIdx_3548_, v___y_3626_);
                        crate::leanh::lean_dec(v_minorIdx_3548_);
                        v___x_3646_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3646_, 0, v_snd_3639_);
                        crate::leanh::lean_ctor_set(v___x_3646_, 1, v___x_3643_);
                        crate::leanh::lean_ctor_set(v___x_3646_, 2, v___x_3640_);
                        v___x_3647_ = lean_array_push(v_subgoals_3552_, v___x_3646_);
                        v_pos_3547_ = v___x_3644_;
                        v_minorIdx_3548_ = v___x_3645_;
                        v_recursor_3549_ = v___y_3624_;
                        v_recursorType_3550_ = v___y_3625_;
                        v_subgoals_3552_ = v___x_3647_;
                        v_a_3553_ = v___y_3629_;
                        v_a_3554_ = v___y_3620_;
                        v_a_3555_ = v___y_3619_;
                        v_a_3556_ = v___y_3618_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_fst_3633_);
                        crate::leanh::lean_dec(v___y_3627_);
                        crate::leanh::lean_dec_ref(v___y_3625_);
                        crate::leanh::lean_dec_ref(v___y_3624_);
                        crate::leanh::lean_dec(v___y_3621_);
                        crate::leanh::lean_dec_ref(v_subgoals_3552_);
                        crate::leanh::lean_dec(v_minorIdx_3548_);
                        crate::leanh::lean_dec(v_pos_3547_);
                        crate::leanh::lean_dec(v_baseSubst_3544_);
                        crate::leanh::lean_dec_ref(v_major_3542_);
                        crate::leanh::lean_dec(v_mvarId_3538_);
                        v_a_3649_ = crate::leanh::lean_ctor_get(v___x_3636_, 0);
                        v_isSharedCheck_3656_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3636_)) as u8;
                        if v_isSharedCheck_3656_ == 0 {
                            v___x_3651_ = v___x_3636_;
                            v_isShared_3652_ = v_isSharedCheck_3656_;
                            state = 12;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3649_);
                            crate::leanh::lean_dec(v___x_3636_);
                            v___x_3651_ = crate::leanh::lean_box(0);
                            v_isShared_3652_ = v_isSharedCheck_3656_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___y_3627_);
                    crate::leanh::lean_dec_ref(v___y_3625_);
                    crate::leanh::lean_dec_ref(v___y_3624_);
                    crate::leanh::lean_dec(v___y_3623_);
                    crate::leanh::lean_dec(v___y_3621_);
                    crate::leanh::lean_dec_ref(v_subgoals_3552_);
                    crate::leanh::lean_dec(v_minorIdx_3548_);
                    crate::leanh::lean_dec(v_pos_3547_);
                    crate::leanh::lean_dec(v_baseSubst_3544_);
                    crate::leanh::lean_dec_ref(v_major_3542_);
                    crate::leanh::lean_dec(v_mvarId_3538_);
                    v_a_3657_ = crate::leanh::lean_ctor_get(v___x_3631_, 0);
                    v_isSharedCheck_3664_ = (!crate::leanh::lean_is_exclusive(v___x_3631_)) as u8;
                    if v_isSharedCheck_3664_ == 0 {
                        v___x_3659_ = v___x_3631_;
                        v_isShared_3660_ = v_isSharedCheck_3664_;
                        state = 14;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3657_);
                        crate::leanh::lean_dec(v___x_3631_);
                        v___x_3659_ = crate::leanh::lean_box(0);
                        v_isShared_3660_ = v_isSharedCheck_3664_;
                        state = 14;
                        continue;
                    }
                }
            }
            12 => {
                if v_isShared_3652_ == 0 {
                    v___x_3654_ = v___x_3651_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3655_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3655_, 0, v_a_3649_);
                    v___x_3654_ = v_reuseFailAlloc_3655_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_3654_;
            }
            14 => {
                if v_isShared_3660_ == 0 {
                    v___x_3662_ = v___x_3659_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3663_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3663_, 0, v_a_3657_);
                    v___x_3662_ = v_reuseFailAlloc_3663_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_3662_;
            }
            16 => {
                v___x_3681_ = l_Lean_Expr_mvarId_x21(v___y_3675_);
                crate::leanh::lean_dec_ref(v___y_3675_);
                v___x_3682_ = l_Lean_Expr_fvarId_x21(v_major_3542_);
                v___x_3683_ = l_Lean_MVarId_tryClear(
                    v___x_3681_,
                    v___x_3682_,
                    v___y_3677_,
                    v___y_3678_,
                    v___y_3679_,
                    v___y_3680_,
                );
                if crate::leanh::lean_obj_tag(v___x_3683_) == 0 {
                    v_explicit_3684_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_3666_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    if v_explicit_3684_ == 0 {
                        v_a_3685_ = crate::leanh::lean_ctor_get(v___x_3683_, 0);
                        crate::leanh::lean_inc(v_a_3685_);
                        crate::leanh::lean_dec_ref_known(v___x_3683_, 1);
                        v_varNames_3686_ = crate::leanh::lean_ctor_get(v___y_3666_, 0);
                        crate::leanh::lean_inc(v_varNames_3686_);
                        crate::leanh::lean_dec_ref(v___y_3666_);
                        v___y_3615_ = v___y_3667_;
                        v___y_3616_ = v___y_3670_;
                        v___y_3617_ = v_varNames_3686_;
                        v___y_3618_ = v___y_3680_;
                        v___y_3619_ = v___y_3679_;
                        v___y_3620_ = v___y_3678_;
                        v___y_3621_ = v___y_3668_;
                        v___y_3622_ = v_a_3685_;
                        v___y_3623_ = v___y_3669_;
                        v___y_3624_ = v___y_3671_;
                        v___y_3625_ = v___y_3674_;
                        v___y_3626_ = v___y_3673_;
                        v___y_3627_ = v___y_3672_;
                        v___y_3628_ = v___y_3676_;
                        v___y_3629_ = v___y_3677_;
                        v___y_3630_ = v___y_3667_;
                        state = 11;
                        continue;
                    } else {
                        v_a_3687_ = crate::leanh::lean_ctor_get(v___x_3683_, 0);
                        crate::leanh::lean_inc(v_a_3687_);
                        crate::leanh::lean_dec_ref_known(v___x_3683_, 1);
                        v_varNames_3688_ = crate::leanh::lean_ctor_get(v___y_3666_, 0);
                        crate::leanh::lean_inc(v_varNames_3688_);
                        crate::leanh::lean_dec_ref(v___y_3666_);
                        v___y_3615_ = v___y_3667_;
                        v___y_3616_ = v___y_3670_;
                        v___y_3617_ = v_varNames_3688_;
                        v___y_3618_ = v___y_3680_;
                        v___y_3619_ = v___y_3679_;
                        v___y_3620_ = v___y_3678_;
                        v___y_3621_ = v___y_3668_;
                        v___y_3622_ = v_a_3687_;
                        v___y_3623_ = v___y_3669_;
                        v___y_3624_ = v___y_3671_;
                        v___y_3625_ = v___y_3674_;
                        v___y_3626_ = v___y_3673_;
                        v___y_3627_ = v___y_3672_;
                        v___y_3628_ = v___y_3676_;
                        v___y_3629_ = v___y_3677_;
                        v___y_3630_ = v___y_3670_;
                        state = 11;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___y_3676_);
                    crate::leanh::lean_dec_ref(v___y_3674_);
                    crate::leanh::lean_dec(v___y_3672_);
                    crate::leanh::lean_dec_ref(v___y_3671_);
                    crate::leanh::lean_dec(v___y_3669_);
                    crate::leanh::lean_dec(v___y_3668_);
                    crate::leanh::lean_dec_ref(v___y_3666_);
                    crate::leanh::lean_dec_ref(v_subgoals_3552_);
                    crate::leanh::lean_dec(v_minorIdx_3548_);
                    crate::leanh::lean_dec(v_pos_3547_);
                    crate::leanh::lean_dec(v_baseSubst_3544_);
                    crate::leanh::lean_dec_ref(v_major_3542_);
                    crate::leanh::lean_dec(v_mvarId_3538_);
                    v_a_3689_ = crate::leanh::lean_ctor_get(v___x_3683_, 0);
                    v_isSharedCheck_3696_ = (!crate::leanh::lean_is_exclusive(v___x_3683_)) as u8;
                    if v_isSharedCheck_3696_ == 0 {
                        v___x_3691_ = v___x_3683_;
                        v_isShared_3692_ = v_isSharedCheck_3696_;
                        state = 17;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3689_);
                        crate::leanh::lean_dec(v___x_3683_);
                        v___x_3691_ = crate::leanh::lean_box(0);
                        v_isShared_3692_ = v_isSharedCheck_3696_;
                        state = 17;
                        continue;
                    }
                }
            }
            17 => {
                if v_isShared_3692_ == 0 {
                    v___x_3694_ = v___x_3691_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3695_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3695_, 0, v_a_3689_);
                    v___x_3694_ = v_reuseFailAlloc_3695_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_3694_;
            }
            19 => {
                crate::leanh::lean_inc(v_mvarId_3538_);
                v___x_3702_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(
                    v_mvarId_3538_,
                    v_snd_3701_,
                    v_major_3542_,
                    v_a_3553_,
                    v_a_3554_,
                    v_a_3555_,
                    v_a_3556_,
                );
                if crate::leanh::lean_obj_tag(v___x_3702_) == 0 {
                    v_a_3703_ = crate::leanh::lean_ctor_get(v___x_3702_, 0);
                    crate::leanh::lean_inc(v_a_3703_);
                    crate::leanh::lean_dec_ref_known(v___x_3702_, 1);
                    crate::leanh::lean_inc_ref(v_major_3542_);
                    v___x_3704_ = l_Lean_Expr_app___override(v_fst_3700_, v_major_3542_);
                    v___x_3705_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3706_ = lean_nat_add(v_pos_3547_, v___x_3705_);
                    crate::leanh::lean_dec(v_pos_3547_);
                    v___x_3707_ = lean_nat_add(v___x_3706_, v___y_3699_);
                    crate::leanh::lean_dec(v___y_3699_);
                    crate::leanh::lean_dec(v___x_3706_);
                    v_pos_3547_ = v___x_3707_;
                    v_recursor_3549_ = v___x_3704_;
                    v_recursorType_3550_ = v_a_3703_;
                    v_consumedMajor_3551_ = v___y_3698_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_fst_3700_);
                    crate::leanh::lean_dec(v___y_3699_);
                    crate::leanh::lean_dec_ref(v_subgoals_3552_);
                    crate::leanh::lean_dec(v_minorIdx_3548_);
                    crate::leanh::lean_dec(v_pos_3547_);
                    crate::leanh::lean_dec(v_baseSubst_3544_);
                    crate::leanh::lean_dec_ref(v_major_3542_);
                    crate::leanh::lean_dec(v_mvarId_3538_);
                    v_a_3709_ = crate::leanh::lean_ctor_get(v___x_3702_, 0);
                    v_isSharedCheck_3716_ = (!crate::leanh::lean_is_exclusive(v___x_3702_)) as u8;
                    if v_isSharedCheck_3716_ == 0 {
                        v___x_3711_ = v___x_3702_;
                        v_isShared_3712_ = v_isSharedCheck_3716_;
                        state = 20;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3709_);
                        crate::leanh::lean_dec(v___x_3702_);
                        v___x_3711_ = crate::leanh::lean_box(0);
                        v_isShared_3712_ = v_isSharedCheck_3716_;
                        state = 20;
                        continue;
                    }
                }
            }
            20 => {
                if v_isShared_3712_ == 0 {
                    v___x_3714_ = v___x_3711_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_3715_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3715_, 0, v_a_3709_);
                    v___x_3714_ = v_reuseFailAlloc_3715_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_3714_;
            }
            22 => {
                if crate::leanh::lean_obj_tag(v___y_3720_) == 0 {
                    v_a_3721_ = crate::leanh::lean_ctor_get(v___y_3720_, 0);
                    crate::leanh::lean_inc(v_a_3721_);
                    crate::leanh::lean_dec_ref_known(v___y_3720_, 1);
                    v_fst_3722_ = crate::leanh::lean_ctor_get(v_a_3721_, 0);
                    crate::leanh::lean_inc(v_fst_3722_);
                    v_snd_3723_ = crate::leanh::lean_ctor_get(v_a_3721_, 1);
                    crate::leanh::lean_inc(v_snd_3723_);
                    crate::leanh::lean_dec(v_a_3721_);
                    v___y_3698_ = v___y_3718_;
                    v___y_3699_ = v___y_3719_;
                    v_fst_3700_ = v_fst_3722_;
                    v_snd_3701_ = v_snd_3723_;
                    state = 19;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_3719_);
                    crate::leanh::lean_dec_ref(v_subgoals_3552_);
                    crate::leanh::lean_dec(v_minorIdx_3548_);
                    crate::leanh::lean_dec(v_pos_3547_);
                    crate::leanh::lean_dec(v_baseSubst_3544_);
                    crate::leanh::lean_dec_ref(v_major_3542_);
                    crate::leanh::lean_dec(v_mvarId_3538_);
                    v_a_3724_ = crate::leanh::lean_ctor_get(v___y_3720_, 0);
                    v_isSharedCheck_3731_ = (!crate::leanh::lean_is_exclusive(v___y_3720_)) as u8;
                    if v_isSharedCheck_3731_ == 0 {
                        v___x_3726_ = v___y_3720_;
                        v_isShared_3727_ = v_isSharedCheck_3731_;
                        state = 23;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3724_);
                        crate::leanh::lean_dec(v___y_3720_);
                        v___x_3726_ = crate::leanh::lean_box(0);
                        v_isShared_3727_ = v_isSharedCheck_3731_;
                        state = 23;
                        continue;
                    }
                }
            }
            23 => {
                if v_isShared_3727_ == 0 {
                    v___x_3729_ = v___x_3726_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_3730_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3730_, 0, v_a_3724_);
                    v___x_3729_ = v_reuseFailAlloc_3730_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_3729_;
            }
            25 => {
                v___x_3749_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                    v___y_3743_,
                    v___y_3740_,
                    v___y_3735_,
                    v___y_3738_,
                    v___y_3744_,
                    v___y_3736_,
                );
                if crate::leanh::lean_obj_tag(v___x_3749_) == 0 {
                    v_a_3750_ = crate::leanh::lean_ctor_get(v___x_3749_, 0);
                    crate::leanh::lean_inc(v_a_3750_);
                    crate::leanh::lean_dec_ref_known(v___x_3749_, 1);
                    crate::leanh::lean_inc(v_mvarId_3538_);
                    v___x_3751_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(
                        v_mvarId_3538_,
                        v_a_3733_,
                        v_a_3750_,
                        v___y_3735_,
                        v___y_3738_,
                        v___y_3744_,
                        v___y_3736_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3751_) == 0 {
                        v_options_3752_ = crate::leanh::lean_ctor_get(v___y_3744_, 2);
                        v_a_3753_ = crate::leanh::lean_ctor_get(v___x_3751_, 0);
                        crate::leanh::lean_inc(v_a_3753_);
                        crate::leanh::lean_dec_ref_known(v___x_3751_, 1);
                        v_inheritedTraceOptions_3754_ =
                            crate::leanh::lean_ctor_get(v___y_3744_, 13);
                        v_hasTrace_3755_ = crate::leanh::lean_ctor_get_uint8(
                            v_options_3752_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        );
                        crate::leanh::lean_inc(v_a_3750_);
                        v___x_3756_ = l_Lean_Expr_app___override(v_recursor_3549_, v_a_3750_);
                        if v_hasTrace_3755_ == 0 {
                            v___y_3666_ = v___y_3748_;
                            v___y_3667_ = v___y_3737_;
                            v___y_3668_ = v___y_3741_;
                            v___y_3669_ = v___y_3742_;
                            v___y_3670_ = v___y_3739_;
                            v___y_3671_ = v___x_3756_;
                            v___y_3672_ = v___y_3745_;
                            v___y_3673_ = v___y_3746_;
                            v___y_3674_ = v_a_3753_;
                            v___y_3675_ = v_a_3750_;
                            v___y_3676_ = v___y_3747_;
                            v___y_3677_ = v___y_3735_;
                            v___y_3678_ = v___y_3738_;
                            v___y_3679_ = v___y_3744_;
                            v___y_3680_ = v___y_3736_;
                            state = 16;
                            continue;
                        } else {
                            v___x_3757_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2;
                            v___x_3758_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5_once), _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5);
                            v___x_3759_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                v_inheritedTraceOptions_3754_,
                                v_options_3752_,
                                v___x_3758_,
                            );
                            if v___x_3759_ == 0 {
                                v___y_3666_ = v___y_3748_;
                                v___y_3667_ = v___y_3737_;
                                v___y_3668_ = v___y_3741_;
                                v___y_3669_ = v___y_3742_;
                                v___y_3670_ = v___y_3739_;
                                v___y_3671_ = v___x_3756_;
                                v___y_3672_ = v___y_3745_;
                                v___y_3673_ = v___y_3746_;
                                v___y_3674_ = v_a_3753_;
                                v___y_3675_ = v_a_3750_;
                                v___y_3676_ = v___y_3747_;
                                v___y_3677_ = v___y_3735_;
                                v___y_3678_ = v___y_3738_;
                                v___y_3679_ = v___y_3744_;
                                v___y_3680_ = v___y_3736_;
                                state = 16;
                                continue;
                            } else {
                                v___x_3760_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__11_once), _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__11);
                                v___x_3761_ = l_Lean_Expr_fvarId_x21(v_major_3542_);
                                v___x_3762_ = l_Lean_MessageData_ofName(v___x_3761_);
                                v___x_3763_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3763_, 0, v___x_3760_);
                                crate::leanh::lean_ctor_set(v___x_3763_, 1, v___x_3762_);
                                v___x_3764_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v___x_3757_, v___x_3763_, v___y_3735_, v___y_3738_, v___y_3744_, v___y_3736_);
                                if crate::leanh::lean_obj_tag(v___x_3764_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_3764_, 1);
                                    v___y_3666_ = v___y_3748_;
                                    v___y_3667_ = v___y_3737_;
                                    v___y_3668_ = v___y_3741_;
                                    v___y_3669_ = v___y_3742_;
                                    v___y_3670_ = v___y_3739_;
                                    v___y_3671_ = v___x_3756_;
                                    v___y_3672_ = v___y_3745_;
                                    v___y_3673_ = v___y_3746_;
                                    v___y_3674_ = v_a_3753_;
                                    v___y_3675_ = v_a_3750_;
                                    v___y_3676_ = v___y_3747_;
                                    v___y_3677_ = v___y_3735_;
                                    v___y_3678_ = v___y_3738_;
                                    v___y_3679_ = v___y_3744_;
                                    v___y_3680_ = v___y_3736_;
                                    state = 16;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec_ref(v___x_3756_);
                                    crate::leanh::lean_dec(v_a_3753_);
                                    crate::leanh::lean_dec(v_a_3750_);
                                    crate::leanh::lean_dec_ref(v___y_3748_);
                                    crate::leanh::lean_dec(v___y_3747_);
                                    crate::leanh::lean_dec(v___y_3745_);
                                    crate::leanh::lean_dec(v___y_3742_);
                                    crate::leanh::lean_dec(v___y_3741_);
                                    crate::leanh::lean_dec_ref(v_subgoals_3552_);
                                    crate::leanh::lean_dec(v_minorIdx_3548_);
                                    crate::leanh::lean_dec(v_pos_3547_);
                                    crate::leanh::lean_dec(v_baseSubst_3544_);
                                    crate::leanh::lean_dec_ref(v_major_3542_);
                                    crate::leanh::lean_dec(v_mvarId_3538_);
                                    v_a_3765_ = crate::leanh::lean_ctor_get(v___x_3764_, 0);
                                    v_isSharedCheck_3772_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_3764_)) as u8;
                                    if v_isSharedCheck_3772_ == 0 {
                                        v___x_3767_ = v___x_3764_;
                                        v_isShared_3768_ = v_isSharedCheck_3772_;
                                        state = 26;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_3765_);
                                        crate::leanh::lean_dec(v___x_3764_);
                                        v___x_3767_ = crate::leanh::lean_box(0);
                                        v_isShared_3768_ = v_isSharedCheck_3772_;
                                        state = 26;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3750_);
                        crate::leanh::lean_dec_ref(v___y_3748_);
                        crate::leanh::lean_dec(v___y_3747_);
                        crate::leanh::lean_dec(v___y_3745_);
                        crate::leanh::lean_dec(v___y_3742_);
                        crate::leanh::lean_dec(v___y_3741_);
                        crate::leanh::lean_dec_ref(v_subgoals_3552_);
                        crate::leanh::lean_dec_ref(v_recursor_3549_);
                        crate::leanh::lean_dec(v_minorIdx_3548_);
                        crate::leanh::lean_dec(v_pos_3547_);
                        crate::leanh::lean_dec(v_baseSubst_3544_);
                        crate::leanh::lean_dec_ref(v_major_3542_);
                        crate::leanh::lean_dec(v_mvarId_3538_);
                        v_a_3773_ = crate::leanh::lean_ctor_get(v___x_3751_, 0);
                        v_isSharedCheck_3780_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3751_)) as u8;
                        if v_isSharedCheck_3780_ == 0 {
                            v___x_3775_ = v___x_3751_;
                            v_isShared_3776_ = v_isSharedCheck_3780_;
                            state = 28;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3773_);
                            crate::leanh::lean_dec(v___x_3751_);
                            v___x_3775_ = crate::leanh::lean_box(0);
                            v_isShared_3776_ = v_isSharedCheck_3780_;
                            state = 28;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_3748_);
                    crate::leanh::lean_dec(v___y_3747_);
                    crate::leanh::lean_dec(v___y_3745_);
                    crate::leanh::lean_dec(v___y_3742_);
                    crate::leanh::lean_dec(v___y_3741_);
                    crate::leanh::lean_dec(v_a_3733_);
                    crate::leanh::lean_dec_ref(v_subgoals_3552_);
                    crate::leanh::lean_dec_ref(v_recursor_3549_);
                    crate::leanh::lean_dec(v_minorIdx_3548_);
                    crate::leanh::lean_dec(v_pos_3547_);
                    crate::leanh::lean_dec(v_baseSubst_3544_);
                    crate::leanh::lean_dec_ref(v_major_3542_);
                    crate::leanh::lean_dec(v_mvarId_3538_);
                    v_a_3781_ = crate::leanh::lean_ctor_get(v___x_3749_, 0);
                    v_isSharedCheck_3788_ = (!crate::leanh::lean_is_exclusive(v___x_3749_)) as u8;
                    if v_isSharedCheck_3788_ == 0 {
                        v___x_3783_ = v___x_3749_;
                        v_isShared_3784_ = v_isSharedCheck_3788_;
                        state = 30;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3781_);
                        crate::leanh::lean_dec(v___x_3749_);
                        v___x_3783_ = crate::leanh::lean_box(0);
                        v_isShared_3784_ = v_isSharedCheck_3788_;
                        state = 30;
                        continue;
                    }
                }
            }
            26 => {
                if v_isShared_3768_ == 0 {
                    v___x_3770_ = v___x_3767_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_3771_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3771_, 0, v_a_3765_);
                    v___x_3770_ = v_reuseFailAlloc_3771_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_3770_;
            }
            28 => {
                if v_isShared_3776_ == 0 {
                    v___x_3778_ = v___x_3775_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_3779_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3779_, 0, v_a_3773_);
                    v___x_3778_ = v_reuseFailAlloc_3779_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_3778_;
            }
            30 => {
                if v_isShared_3784_ == 0 {
                    v___x_3786_ = v___x_3783_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_3787_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3787_, 0, v_a_3781_);
                    v___x_3786_ = v_reuseFailAlloc_3787_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_3786_;
            }
            32 => {
                v___x_3800_ = lean_nat_sub(v___y_3790_, v_initialArity_3545_);
                crate::leanh::lean_dec(v___y_3790_);
                v___x_3801_ = lean_array_get_size(v_reverted_3541_);
                v___x_3802_ = lean_array_get_size(v_indices_3543_);
                v___x_3803_ = lean_nat_sub(v___x_3801_, v___x_3802_);
                v___x_3804_ = lean_nat_sub(v___x_3803_, v___y_3795_);
                crate::leanh::lean_dec(v___x_3803_);
                v___x_3805_ = lean_array_get_size(v_givenNames_3539_);
                v___x_3806_ = lean_nat_dec_lt(v_minorIdx_3548_, v___x_3805_);
                if v___x_3806_ == 0 {
                    v___x_3807_ = crate::leanh::lean_box(0);
                    v___x_3808_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_3808_, 0, v___x_3807_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_3808_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___y_3793_,
                    );
                    v___y_3735_ = v___y_3796_;
                    v___y_3736_ = v___y_3799_;
                    v___y_3737_ = v___y_3791_;
                    v___y_3738_ = v___y_3797_;
                    v___y_3739_ = v___y_3793_;
                    v___y_3740_ = v___y_3794_;
                    v___y_3741_ = v___x_3802_;
                    v___y_3742_ = v___x_3804_;
                    v___y_3743_ = v___y_3792_;
                    v___y_3744_ = v___y_3798_;
                    v___y_3745_ = v___x_3801_;
                    v___y_3746_ = v___y_3795_;
                    v___y_3747_ = v___x_3800_;
                    v___y_3748_ = v___x_3808_;
                    state = 25;
                    continue;
                } else {
                    v___x_3809_ = lean_array_fget_borrowed(v_givenNames_3539_, v_minorIdx_3548_);
                    crate::leanh::lean_inc(v___x_3809_);
                    v___y_3735_ = v___y_3796_;
                    v___y_3736_ = v___y_3799_;
                    v___y_3737_ = v___y_3791_;
                    v___y_3738_ = v___y_3797_;
                    v___y_3739_ = v___y_3793_;
                    v___y_3740_ = v___y_3794_;
                    v___y_3741_ = v___x_3802_;
                    v___y_3742_ = v___x_3804_;
                    v___y_3743_ = v___y_3792_;
                    v___y_3744_ = v___y_3798_;
                    v___y_3745_ = v___x_3801_;
                    v___y_3746_ = v___y_3795_;
                    v___y_3747_ = v___x_3800_;
                    v___y_3748_ = v___x_3809_;
                    state = 25;
                    continue;
                }
            }
            33 => {
                if v___y_3819_ == 0 {
                    crate::leanh::lean_inc_ref(v___y_3815_);
                    v___x_3820_ =
                        l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTargetArity(
                            v___y_3815_,
                        );
                    v___x_3821_ = lean_nat_dec_lt(v___x_3820_, v_initialArity_3545_);
                    if v___x_3821_ == 0 {
                        v___y_3790_ = v___x_3820_;
                        v___y_3791_ = v___y_3813_;
                        v___y_3792_ = v___y_3815_;
                        v___y_3793_ = v___y_3819_;
                        v___y_3794_ = v___y_3817_;
                        v___y_3795_ = v___y_3818_;
                        v___y_3796_ = v___y_3812_;
                        v___y_3797_ = v___y_3811_;
                        v___y_3798_ = v___y_3814_;
                        v___y_3799_ = v___y_3816_;
                        state = 32;
                        continue;
                    } else {
                        v___x_3822_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1;
                        v___x_3823_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once), _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
                        crate::leanh::lean_inc(v_mvarId_3538_);
                        v___x_3824_ = l_Lean_Meta_throwTacticEx___redArg(
                            v___x_3822_,
                            v_mvarId_3538_,
                            v___x_3823_,
                            v___y_3812_,
                            v___y_3811_,
                            v___y_3814_,
                            v___y_3816_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3824_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_3824_, 1);
                            v___y_3790_ = v___x_3820_;
                            v___y_3791_ = v___y_3813_;
                            v___y_3792_ = v___y_3815_;
                            v___y_3793_ = v___y_3819_;
                            v___y_3794_ = v___y_3817_;
                            v___y_3795_ = v___y_3818_;
                            v___y_3796_ = v___y_3812_;
                            v___y_3797_ = v___y_3811_;
                            v___y_3798_ = v___y_3814_;
                            v___y_3799_ = v___y_3816_;
                            state = 32;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_3820_);
                            crate::leanh::lean_dec(v___y_3817_);
                            crate::leanh::lean_dec_ref(v___y_3815_);
                            crate::leanh::lean_dec(v_a_3733_);
                            crate::leanh::lean_dec_ref(v_subgoals_3552_);
                            crate::leanh::lean_dec_ref(v_recursor_3549_);
                            crate::leanh::lean_dec(v_minorIdx_3548_);
                            crate::leanh::lean_dec(v_pos_3547_);
                            crate::leanh::lean_dec(v_baseSubst_3544_);
                            crate::leanh::lean_dec_ref(v_major_3542_);
                            crate::leanh::lean_dec(v_mvarId_3538_);
                            v_a_3825_ = crate::leanh::lean_ctor_get(v___x_3824_, 0);
                            v_isSharedCheck_3832_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3824_)) as u8;
                            if v_isSharedCheck_3832_ == 0 {
                                v___x_3827_ = v___x_3824_;
                                v_isShared_3828_ = v_isSharedCheck_3832_;
                                state = 34;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3825_);
                                crate::leanh::lean_dec(v___x_3824_);
                                v___x_3827_ = crate::leanh::lean_box(0);
                                v_isShared_3828_ = v_isSharedCheck_3832_;
                                state = 34;
                                continue;
                            }
                        }
                    }
                } else {
                    v___x_3833_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc_ref(v___y_3815_);
                    v___x_3834_ = l_Lean_Meta_synthInstance_x3f(
                        v___y_3815_,
                        v___x_3833_,
                        v___y_3812_,
                        v___y_3811_,
                        v___y_3814_,
                        v___y_3816_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3834_) == 0 {
                        v_a_3835_ = crate::leanh::lean_ctor_get(v___x_3834_, 0);
                        crate::leanh::lean_inc(v_a_3835_);
                        crate::leanh::lean_dec_ref_known(v___x_3834_, 1);
                        if crate::leanh::lean_obj_tag(v_a_3835_) == 0 {
                            v___x_3836_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                                v___y_3815_,
                                v___y_3817_,
                                v___y_3812_,
                                v___y_3811_,
                                v___y_3814_,
                                v___y_3816_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_3836_) == 0 {
                                v_a_3837_ = crate::leanh::lean_ctor_get(v___x_3836_, 0);
                                crate::leanh::lean_inc(v_a_3837_);
                                crate::leanh::lean_dec_ref_known(v___x_3836_, 1);
                                crate::leanh::lean_inc(v_mvarId_3538_);
                                v___x_3838_ =
                                    l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(
                                        v_mvarId_3538_,
                                        v_a_3733_,
                                        v_a_3837_,
                                        v___y_3812_,
                                        v___y_3811_,
                                        v___y_3814_,
                                        v___y_3816_,
                                    );
                                if crate::leanh::lean_obj_tag(v___x_3838_) == 0 {
                                    v_a_3839_ = crate::leanh::lean_ctor_get(v___x_3838_, 0);
                                    crate::leanh::lean_inc(v_a_3839_);
                                    crate::leanh::lean_dec_ref_known(v___x_3838_, 1);
                                    crate::leanh::lean_inc(v_a_3837_);
                                    v___x_3840_ =
                                        l_Lean_Expr_app___override(v_recursor_3549_, v_a_3837_);
                                    v___x_3841_ = lean_nat_add(v_pos_3547_, v___y_3818_);
                                    crate::leanh::lean_dec(v_pos_3547_);
                                    v___x_3842_ = lean_nat_add(v_minorIdx_3548_, v___y_3818_);
                                    crate::leanh::lean_dec(v_minorIdx_3548_);
                                    v___x_3843_ = l_Lean_Expr_mvarId_x21(v_a_3837_);
                                    crate::leanh::lean_dec(v_a_3837_);
                                    v___x_3844_ = l_Lean_Meta_instInhabitedInductionSubgoal_default___closed__0;
                                    v___x_3845_ = crate::leanh::lean_box(0);
                                    v___x_3846_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_3846_, 0, v___x_3843_);
                                    crate::leanh::lean_ctor_set(v___x_3846_, 1, v___x_3844_);
                                    crate::leanh::lean_ctor_set(v___x_3846_, 2, v___x_3845_);
                                    v___x_3847_ = lean_array_push(v_subgoals_3552_, v___x_3846_);
                                    v_pos_3547_ = v___x_3841_;
                                    v_minorIdx_3548_ = v___x_3842_;
                                    v_recursor_3549_ = v___x_3840_;
                                    v_recursorType_3550_ = v_a_3839_;
                                    v_subgoals_3552_ = v___x_3847_;
                                    v_a_3553_ = v___y_3812_;
                                    v_a_3554_ = v___y_3811_;
                                    v_a_3555_ = v___y_3814_;
                                    v_a_3556_ = v___y_3816_;
                                    state = 0;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_a_3837_);
                                    crate::leanh::lean_dec_ref(v_subgoals_3552_);
                                    crate::leanh::lean_dec_ref(v_recursor_3549_);
                                    crate::leanh::lean_dec(v_minorIdx_3548_);
                                    crate::leanh::lean_dec(v_pos_3547_);
                                    crate::leanh::lean_dec(v_baseSubst_3544_);
                                    crate::leanh::lean_dec_ref(v_major_3542_);
                                    crate::leanh::lean_dec(v_mvarId_3538_);
                                    v_a_3849_ = crate::leanh::lean_ctor_get(v___x_3838_, 0);
                                    v_isSharedCheck_3856_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_3838_)) as u8;
                                    if v_isSharedCheck_3856_ == 0 {
                                        v___x_3851_ = v___x_3838_;
                                        v_isShared_3852_ = v_isSharedCheck_3856_;
                                        state = 36;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_3849_);
                                        crate::leanh::lean_dec(v___x_3838_);
                                        v___x_3851_ = crate::leanh::lean_box(0);
                                        v_isShared_3852_ = v_isSharedCheck_3856_;
                                        state = 36;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_3733_);
                                crate::leanh::lean_dec_ref(v_subgoals_3552_);
                                crate::leanh::lean_dec_ref(v_recursor_3549_);
                                crate::leanh::lean_dec(v_minorIdx_3548_);
                                crate::leanh::lean_dec(v_pos_3547_);
                                crate::leanh::lean_dec(v_baseSubst_3544_);
                                crate::leanh::lean_dec_ref(v_major_3542_);
                                crate::leanh::lean_dec(v_mvarId_3538_);
                                v_a_3857_ = crate::leanh::lean_ctor_get(v___x_3836_, 0);
                                v_isSharedCheck_3864_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3836_)) as u8;
                                if v_isSharedCheck_3864_ == 0 {
                                    v___x_3859_ = v___x_3836_;
                                    v_isShared_3860_ = v_isSharedCheck_3864_;
                                    state = 38;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3857_);
                                    crate::leanh::lean_dec(v___x_3836_);
                                    v___x_3859_ = crate::leanh::lean_box(0);
                                    v_isShared_3860_ = v_isSharedCheck_3864_;
                                    state = 38;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v___y_3817_);
                            crate::leanh::lean_dec_ref(v___y_3815_);
                            v_val_3865_ = crate::leanh::lean_ctor_get(v_a_3835_, 0);
                            crate::leanh::lean_inc(v_val_3865_);
                            crate::leanh::lean_dec_ref_known(v_a_3835_, 1);
                            crate::leanh::lean_inc(v_mvarId_3538_);
                            v___x_3866_ =
                                l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(
                                    v_mvarId_3538_,
                                    v_a_3733_,
                                    v_val_3865_,
                                    v___y_3812_,
                                    v___y_3811_,
                                    v___y_3814_,
                                    v___y_3816_,
                                );
                            if crate::leanh::lean_obj_tag(v___x_3866_) == 0 {
                                v_a_3867_ = crate::leanh::lean_ctor_get(v___x_3866_, 0);
                                crate::leanh::lean_inc(v_a_3867_);
                                crate::leanh::lean_dec_ref_known(v___x_3866_, 1);
                                v___x_3868_ =
                                    l_Lean_Expr_app___override(v_recursor_3549_, v_val_3865_);
                                v___x_3869_ = lean_nat_add(v_pos_3547_, v___y_3818_);
                                crate::leanh::lean_dec(v_pos_3547_);
                                v___x_3870_ = lean_nat_add(v_minorIdx_3548_, v___y_3818_);
                                crate::leanh::lean_dec(v_minorIdx_3548_);
                                v_pos_3547_ = v___x_3869_;
                                v_minorIdx_3548_ = v___x_3870_;
                                v_recursor_3549_ = v___x_3868_;
                                v_recursorType_3550_ = v_a_3867_;
                                v_a_3553_ = v___y_3812_;
                                v_a_3554_ = v___y_3811_;
                                v_a_3555_ = v___y_3814_;
                                v_a_3556_ = v___y_3816_;
                                state = 0;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_val_3865_);
                                crate::leanh::lean_dec_ref(v_subgoals_3552_);
                                crate::leanh::lean_dec_ref(v_recursor_3549_);
                                crate::leanh::lean_dec(v_minorIdx_3548_);
                                crate::leanh::lean_dec(v_pos_3547_);
                                crate::leanh::lean_dec(v_baseSubst_3544_);
                                crate::leanh::lean_dec_ref(v_major_3542_);
                                crate::leanh::lean_dec(v_mvarId_3538_);
                                v_a_3872_ = crate::leanh::lean_ctor_get(v___x_3866_, 0);
                                v_isSharedCheck_3879_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3866_)) as u8;
                                if v_isSharedCheck_3879_ == 0 {
                                    v___x_3874_ = v___x_3866_;
                                    v_isShared_3875_ = v_isSharedCheck_3879_;
                                    state = 40;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3872_);
                                    crate::leanh::lean_dec(v___x_3866_);
                                    v___x_3874_ = crate::leanh::lean_box(0);
                                    v_isShared_3875_ = v_isSharedCheck_3879_;
                                    state = 40;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___y_3817_);
                        crate::leanh::lean_dec_ref(v___y_3815_);
                        crate::leanh::lean_dec(v_a_3733_);
                        crate::leanh::lean_dec_ref(v_subgoals_3552_);
                        crate::leanh::lean_dec_ref(v_recursor_3549_);
                        crate::leanh::lean_dec(v_minorIdx_3548_);
                        crate::leanh::lean_dec(v_pos_3547_);
                        crate::leanh::lean_dec(v_baseSubst_3544_);
                        crate::leanh::lean_dec_ref(v_major_3542_);
                        crate::leanh::lean_dec(v_mvarId_3538_);
                        v_a_3880_ = crate::leanh::lean_ctor_get(v___x_3834_, 0);
                        v_isSharedCheck_3887_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3834_)) as u8;
                        if v_isSharedCheck_3887_ == 0 {
                            v___x_3882_ = v___x_3834_;
                            v_isShared_3883_ = v_isSharedCheck_3887_;
                            state = 42;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3880_);
                            crate::leanh::lean_dec(v___x_3834_);
                            v___x_3882_ = crate::leanh::lean_box(0);
                            v_isShared_3883_ = v_isSharedCheck_3887_;
                            state = 42;
                            continue;
                        }
                    }
                }
            }
            34 => {
                if v_isShared_3828_ == 0 {
                    v___x_3830_ = v___x_3827_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_3831_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3831_, 0, v_a_3825_);
                    v___x_3830_ = v_reuseFailAlloc_3831_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                return v___x_3830_;
            }
            36 => {
                if v_isShared_3852_ == 0 {
                    v___x_3854_ = v___x_3851_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_3855_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3855_, 0, v_a_3849_);
                    v___x_3854_ = v_reuseFailAlloc_3855_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_3854_;
            }
            38 => {
                if v_isShared_3860_ == 0 {
                    v___x_3862_ = v___x_3859_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_3863_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3863_, 0, v_a_3857_);
                    v___x_3862_ = v_reuseFailAlloc_3863_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                return v___x_3862_;
            }
            40 => {
                if v_isShared_3875_ == 0 {
                    v___x_3877_ = v___x_3874_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_3878_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3878_, 0, v_a_3872_);
                    v___x_3877_ = v_reuseFailAlloc_3878_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_3877_;
            }
            42 => {
                if v_isShared_3883_ == 0 {
                    v___x_3885_ = v___x_3882_;
                    state = 43;
                    continue;
                } else {
                    v_reuseFailAlloc_3886_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3886_, 0, v_a_3880_);
                    v___x_3885_ = v_reuseFailAlloc_3886_;
                    state = 43;
                    continue;
                }
            }
            43 => {
                return v___x_3885_;
            }
            44 => {
                v___x_3898_ = l_Lean_BinderInfo_isInstImplicit(v___y_3896_);
                if v___x_3898_ == 0 {
                    v___y_3811_ = v___y_3891_;
                    v___y_3812_ = v___y_3890_;
                    v___y_3813_ = v___y_3889_;
                    v___y_3814_ = v___y_3893_;
                    v___y_3815_ = v___y_3892_;
                    v___y_3816_ = v___y_3894_;
                    v___y_3817_ = v___y_3897_;
                    v___y_3818_ = v___y_3895_;
                    v___y_3819_ = v___x_3898_;
                    state = 33;
                    continue;
                } else {
                    v___x_3899_ = lean_array_get_size(v_givenNames_3539_);
                    v___x_3900_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3901_ = lean_nat_dec_eq(v___x_3899_, v___x_3900_);
                    v___y_3811_ = v___y_3891_;
                    v___y_3812_ = v___y_3890_;
                    v___y_3813_ = v___y_3889_;
                    v___y_3814_ = v___y_3893_;
                    v___y_3815_ = v___y_3892_;
                    v___y_3816_ = v___y_3894_;
                    v___y_3817_ = v___y_3897_;
                    v___y_3818_ = v___y_3895_;
                    v___y_3819_ = v___x_3901_;
                    state = 33;
                    continue;
                }
            }
            45 => {
                if crate::leanh::lean_obj_tag(v_a_3733_) == 7 {
                    v_binderName_3909_ = crate::leanh::lean_ctor_get(v_a_3733_, 0);
                    v_binderType_3910_ = crate::leanh::lean_ctor_get(v_a_3733_, 1);
                    v_binderInfo_3911_ = crate::leanh::lean_ctor_get_uint8(
                        v_a_3733_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    );
                    crate::leanh::lean_inc_ref(v_binderType_3910_);
                    v___x_3912_ = l_Lean_Expr_headBeta(v_binderType_3910_);
                    v___x_3913_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3914_ = lean_nat_dec_eq(v_numMinors_3546_, v___x_3913_);
                    if v___x_3914_ == 0 {
                        crate::leanh::lean_inc(v_binderName_3909_);
                        v___x_3915_ = lean_erase_macro_scopes(v_binderName_3909_);
                        v___x_3916_ = l_Lean_Name_append(v___y_3904_, v___x_3915_);
                        v___y_3889_ = v___y_3903_;
                        v___y_3890_ = v___y_3905_;
                        v___y_3891_ = v___y_3906_;
                        v___y_3892_ = v___x_3912_;
                        v___y_3893_ = v___y_3907_;
                        v___y_3894_ = v___y_3908_;
                        v___y_3895_ = v___x_3913_;
                        v___y_3896_ = v_binderInfo_3911_;
                        v___y_3897_ = v___x_3916_;
                        state = 44;
                        continue;
                    } else {
                        v___y_3889_ = v___y_3903_;
                        v___y_3890_ = v___y_3905_;
                        v___y_3891_ = v___y_3906_;
                        v___y_3892_ = v___x_3912_;
                        v___y_3893_ = v___y_3907_;
                        v___y_3894_ = v___y_3908_;
                        v___y_3895_ = v___x_3913_;
                        v___y_3896_ = v_binderInfo_3911_;
                        v___y_3897_ = v___y_3904_;
                        state = 44;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___y_3904_);
                    crate::leanh::lean_dec(v_a_3733_);
                    crate::leanh::lean_dec_ref(v_subgoals_3552_);
                    crate::leanh::lean_dec_ref(v_recursor_3549_);
                    crate::leanh::lean_dec(v_minorIdx_3548_);
                    crate::leanh::lean_dec(v_pos_3547_);
                    crate::leanh::lean_dec(v_baseSubst_3544_);
                    crate::leanh::lean_dec_ref(v_major_3542_);
                    crate::leanh::lean_dec(v_mvarId_3538_);
                    v___x_3917_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__15), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__15_once), _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__15);
                    v___x_3918_ = l_panic___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__4(v___x_3917_, v___y_3905_, v___y_3906_, v___y_3907_, v___y_3908_);
                    return v___x_3918_;
                }
            }
            46 => {
                if v___y_3920_ == 0 {
                    crate::leanh::lean_dec(v_a_3733_);
                    crate::leanh::lean_dec(v_minorIdx_3548_);
                    crate::leanh::lean_dec(v_pos_3547_);
                    crate::leanh::lean_dec(v_baseSubst_3544_);
                    crate::leanh::lean_dec_ref(v_major_3542_);
                    if v_consumedMajor_3551_ == 0 {
                        v___x_3921_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1;
                        v___x_3922_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once), _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
                        crate::leanh::lean_inc(v_mvarId_3538_);
                        v___x_3923_ = l_Lean_Meta_throwTacticEx___redArg(
                            v___x_3921_,
                            v_mvarId_3538_,
                            v___x_3922_,
                            v_a_3553_,
                            v_a_3554_,
                            v_a_3555_,
                            v_a_3556_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3923_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_3923_, 1);
                            v___y_3559_ = v_a_3553_;
                            v___y_3560_ = v_a_3554_;
                            v___y_3561_ = v_a_3555_;
                            v___y_3562_ = v_a_3556_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_subgoals_3552_);
                            crate::leanh::lean_dec_ref(v_recursor_3549_);
                            crate::leanh::lean_dec(v_mvarId_3538_);
                            v_a_3924_ = crate::leanh::lean_ctor_get(v___x_3923_, 0);
                            v_isSharedCheck_3931_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3923_)) as u8;
                            if v_isSharedCheck_3931_ == 0 {
                                v___x_3926_ = v___x_3923_;
                                v_isShared_3927_ = v_isSharedCheck_3931_;
                                state = 47;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3924_);
                                crate::leanh::lean_dec(v___x_3923_);
                                v___x_3926_ = crate::leanh::lean_box(0);
                                v_isShared_3927_ = v_isSharedCheck_3931_;
                                state = 47;
                                continue;
                            }
                        }
                    } else {
                        v___y_3559_ = v_a_3553_;
                        v___y_3560_ = v_a_3554_;
                        v___y_3561_ = v_a_3555_;
                        v___y_3562_ = v_a_3556_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_3932_ = l_Lean_Meta_RecursorInfo_firstIndexPos(v_recursorInfo_3540_);
                    v___x_3933_ = lean_nat_dec_eq(v_pos_3547_, v___x_3932_);
                    crate::leanh::lean_dec(v___x_3932_);
                    if v___x_3933_ == 0 {
                        crate::leanh::lean_inc(v_mvarId_3538_);
                        v___x_3934_ = l_Lean_MVarId_getTag(
                            v_mvarId_3538_,
                            v_a_3553_,
                            v_a_3554_,
                            v_a_3555_,
                            v_a_3556_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3934_) == 0 {
                            v_a_3935_ = crate::leanh::lean_ctor_get(v___x_3934_, 0);
                            crate::leanh::lean_inc(v_a_3935_);
                            crate::leanh::lean_dec_ref_known(v___x_3934_, 1);
                            v___x_3936_ = lean_nat_dec_le(v_numMinors_3546_, v_minorIdx_3548_);
                            if v___x_3936_ == 0 {
                                v___y_3903_ = v___y_3920_;
                                v___y_3904_ = v_a_3935_;
                                v___y_3905_ = v_a_3553_;
                                v___y_3906_ = v_a_3554_;
                                v___y_3907_ = v_a_3555_;
                                v___y_3908_ = v_a_3556_;
                                state = 45;
                                continue;
                            } else {
                                v___x_3937_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1;
                                v___x_3938_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once), _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
                                crate::leanh::lean_inc(v_mvarId_3538_);
                                v___x_3939_ = l_Lean_Meta_throwTacticEx___redArg(
                                    v___x_3937_,
                                    v_mvarId_3538_,
                                    v___x_3938_,
                                    v_a_3553_,
                                    v_a_3554_,
                                    v_a_3555_,
                                    v_a_3556_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_3939_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_3939_, 1);
                                    v___y_3903_ = v___y_3920_;
                                    v___y_3904_ = v_a_3935_;
                                    v___y_3905_ = v_a_3553_;
                                    v___y_3906_ = v_a_3554_;
                                    v___y_3907_ = v_a_3555_;
                                    v___y_3908_ = v_a_3556_;
                                    state = 45;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_a_3935_);
                                    crate::leanh::lean_dec(v_a_3733_);
                                    crate::leanh::lean_dec_ref(v_subgoals_3552_);
                                    crate::leanh::lean_dec_ref(v_recursor_3549_);
                                    crate::leanh::lean_dec(v_minorIdx_3548_);
                                    crate::leanh::lean_dec(v_pos_3547_);
                                    crate::leanh::lean_dec(v_baseSubst_3544_);
                                    crate::leanh::lean_dec_ref(v_major_3542_);
                                    crate::leanh::lean_dec(v_mvarId_3538_);
                                    v_a_3940_ = crate::leanh::lean_ctor_get(v___x_3939_, 0);
                                    v_isSharedCheck_3947_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_3939_)) as u8;
                                    if v_isSharedCheck_3947_ == 0 {
                                        v___x_3942_ = v___x_3939_;
                                        v_isShared_3943_ = v_isSharedCheck_3947_;
                                        state = 49;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_3940_);
                                        crate::leanh::lean_dec(v___x_3939_);
                                        v___x_3942_ = crate::leanh::lean_box(0);
                                        v_isShared_3943_ = v_isSharedCheck_3947_;
                                        state = 49;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3733_);
                            crate::leanh::lean_dec_ref(v_subgoals_3552_);
                            crate::leanh::lean_dec_ref(v_recursor_3549_);
                            crate::leanh::lean_dec(v_minorIdx_3548_);
                            crate::leanh::lean_dec(v_pos_3547_);
                            crate::leanh::lean_dec(v_baseSubst_3544_);
                            crate::leanh::lean_dec_ref(v_major_3542_);
                            crate::leanh::lean_dec(v_mvarId_3538_);
                            v_a_3948_ = crate::leanh::lean_ctor_get(v___x_3934_, 0);
                            v_isSharedCheck_3955_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3934_)) as u8;
                            if v_isSharedCheck_3955_ == 0 {
                                v___x_3950_ = v___x_3934_;
                                v_isShared_3951_ = v_isSharedCheck_3955_;
                                state = 51;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3948_);
                                crate::leanh::lean_dec(v___x_3934_);
                                v___x_3950_ = crate::leanh::lean_box(0);
                                v_isShared_3951_ = v_isSharedCheck_3955_;
                                state = 51;
                                continue;
                            }
                        }
                    } else {
                        v___x_3956_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_3957_ = lean_array_get_size(v_indices_3543_);
                        v___x_3958_ = lean_nat_dec_lt(v___x_3956_, v___x_3957_);
                        if v___x_3958_ == 0 {
                            v___y_3698_ = v___x_3933_;
                            v___y_3699_ = v___x_3957_;
                            v_fst_3700_ = v_recursor_3549_;
                            v_snd_3701_ = v_a_3733_;
                            state = 19;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3733_);
                            crate::leanh::lean_inc_ref(v_recursor_3549_);
                            v___x_3959_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3959_, 0, v_recursor_3549_);
                            crate::leanh::lean_ctor_set(v___x_3959_, 1, v_a_3733_);
                            v___x_3960_ = lean_nat_dec_le(v___x_3957_, v___x_3957_);
                            if v___x_3960_ == 0 {
                                if v___x_3958_ == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_3959_, 2);
                                    v___y_3698_ = v___x_3933_;
                                    v___y_3699_ = v___x_3957_;
                                    v_fst_3700_ = v_recursor_3549_;
                                    v_snd_3701_ = v_a_3733_;
                                    state = 19;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_a_3733_);
                                    crate::leanh::lean_dec_ref(v_recursor_3549_);
                                    v___x_3961_ = 0usize;
                                    v___x_3962_ = lean_usize_of_nat(v___x_3957_);
                                    crate::leanh::lean_inc(v_mvarId_3538_);
                                    v___x_3963_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__5(v_mvarId_3538_, v_indices_3543_, v___x_3961_, v___x_3962_, v___x_3959_, v_a_3553_, v_a_3554_, v_a_3555_, v_a_3556_);
                                    v___y_3718_ = v___x_3933_;
                                    v___y_3719_ = v___x_3957_;
                                    v___y_3720_ = v___x_3963_;
                                    state = 22;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_3733_);
                                crate::leanh::lean_dec_ref(v_recursor_3549_);
                                v___x_3964_ = 0usize;
                                v___x_3965_ = lean_usize_of_nat(v___x_3957_);
                                crate::leanh::lean_inc(v_mvarId_3538_);
                                v___x_3966_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__5(v_mvarId_3538_, v_indices_3543_, v___x_3964_, v___x_3965_, v___x_3959_, v_a_3553_, v_a_3554_, v_a_3555_, v_a_3556_);
                                v___y_3718_ = v___x_3933_;
                                v___y_3719_ = v___x_3957_;
                                v___y_3720_ = v___x_3966_;
                                state = 22;
                                continue;
                            }
                        }
                    }
                }
            }
            47 => {
                if v_isShared_3927_ == 0 {
                    v___x_3929_ = v___x_3926_;
                    state = 48;
                    continue;
                } else {
                    v_reuseFailAlloc_3930_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3930_, 0, v_a_3924_);
                    v___x_3929_ = v_reuseFailAlloc_3930_;
                    state = 48;
                    continue;
                }
            }
            48 => {
                return v___x_3929_;
            }
            49 => {
                if v_isShared_3943_ == 0 {
                    v___x_3945_ = v___x_3942_;
                    state = 50;
                    continue;
                } else {
                    v_reuseFailAlloc_3946_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3946_, 0, v_a_3940_);
                    v___x_3945_ = v_reuseFailAlloc_3946_;
                    state = 50;
                    continue;
                }
            }
            50 => {
                return v___x_3945_;
            }
            51 => {
                if v_isShared_3951_ == 0 {
                    v___x_3953_ = v___x_3950_;
                    state = 52;
                    continue;
                } else {
                    v_reuseFailAlloc_3954_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3954_, 0, v_a_3948_);
                    v___x_3953_ = v_reuseFailAlloc_3954_;
                    state = 52;
                    continue;
                }
            }
            52 => {
                return v___x_3953_;
            }
            53 => {
                if v_isShared_3973_ == 0 {
                    v___x_3975_ = v___x_3972_;
                    state = 54;
                    continue;
                } else {
                    v_reuseFailAlloc_3976_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3976_, 0, v_a_3970_);
                    v___x_3975_ = v_reuseFailAlloc_3976_;
                    state = 54;
                    continue;
                }
            }
            54 => {
                return v___x_3975_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_mvarId_3978_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_givenNames_3979_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_recursorInfo_3980_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_reverted_3981_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_major_3982_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_indices_3983_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_baseSubst_3984_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_initialArity_3985_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_numMinors_3986_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_pos_3987_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_minorIdx_3988_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_recursor_3989_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_recursorType_3990_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_consumedMajor_3991_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_subgoals_3992_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_a_3993_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_a_3994_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_a_3995_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_a_3996_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v_a_3997_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v_consumedMajor_boxed_3998_: u8 = 0;
    let mut v_res_3999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_consumedMajor_boxed_3998_ = (crate::leanh::lean_unbox(v_consumedMajor_3991_) as u8);
    v_res_3999_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop(
        v_mvarId_3978_,
        v_givenNames_3979_,
        v_recursorInfo_3980_,
        v_reverted_3981_,
        v_major_3982_,
        v_indices_3983_,
        v_baseSubst_3984_,
        v_initialArity_3985_,
        v_numMinors_3986_,
        v_pos_3987_,
        v_minorIdx_3988_,
        v_recursor_3989_,
        v_recursorType_3990_,
        v_consumedMajor_boxed_3998_,
        v_subgoals_3992_,
        v_a_3993_,
        v_a_3994_,
        v_a_3995_,
        v_a_3996_,
    );
    crate::leanh::lean_dec(v_a_3996_);
    crate::leanh::lean_dec_ref(v_a_3995_);
    crate::leanh::lean_dec(v_a_3994_);
    crate::leanh::lean_dec_ref(v_a_3993_);
    crate::leanh::lean_dec(v_numMinors_3986_);
    crate::leanh::lean_dec(v_initialArity_3985_);
    crate::leanh::lean_dec_ref(v_indices_3983_);
    crate::leanh::lean_dec_ref(v_reverted_3981_);
    crate::leanh::lean_dec_ref(v_recursorInfo_3980_);
    crate::leanh::lean_dec_ref(v_givenNames_3979_);
    return v_res_3999_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0(
    mut v_mvarId_4000_: *mut crate::leanh::LeanObject,
    mut v_val_4001_: *mut crate::leanh::LeanObject,
    mut v___y_4002_: *mut crate::leanh::LeanObject,
    mut v___y_4003_: *mut crate::leanh::LeanObject,
    mut v___y_4004_: *mut crate::leanh::LeanObject,
    mut v___y_4005_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4007_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___redArg(v_mvarId_4000_, v_val_4001_, v___y_4003_);
    return v___x_4007_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0___boxed(
    mut v_mvarId_4008_: *mut crate::leanh::LeanObject,
    mut v_val_4009_: *mut crate::leanh::LeanObject,
    mut v___y_4010_: *mut crate::leanh::LeanObject,
    mut v___y_4011_: *mut crate::leanh::LeanObject,
    mut v___y_4012_: *mut crate::leanh::LeanObject,
    mut v___y_4013_: *mut crate::leanh::LeanObject,
    mut v___y_4014_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4015_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0(v_mvarId_4008_, v_val_4009_, v___y_4010_, v___y_4011_, v___y_4012_, v___y_4013_);
    crate::leanh::lean_dec(v___y_4013_);
    crate::leanh::lean_dec_ref(v___y_4012_);
    crate::leanh::lean_dec(v___y_4011_);
    crate::leanh::lean_dec_ref(v___y_4010_);
    return v_res_4015_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2(
    mut v___x_4016_: *mut crate::leanh::LeanObject,
    mut v_reverted_4017_: *mut crate::leanh::LeanObject,
    mut v_fst_4018_: *mut crate::leanh::LeanObject,
    mut v_n_4019_: *mut crate::leanh::LeanObject,
    mut v_j_4020_: *mut crate::leanh::LeanObject,
    mut v_a_4021_: *mut crate::leanh::LeanObject,
    mut v_a_4022_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4023_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2___redArg(v___x_4016_, v_reverted_4017_, v_fst_4018_, v_n_4019_, v_j_4020_, v_a_4022_);
    return v___x_4023_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2___boxed(
    mut v___x_4024_: *mut crate::leanh::LeanObject,
    mut v_reverted_4025_: *mut crate::leanh::LeanObject,
    mut v_fst_4026_: *mut crate::leanh::LeanObject,
    mut v_n_4027_: *mut crate::leanh::LeanObject,
    mut v_j_4028_: *mut crate::leanh::LeanObject,
    mut v_a_4029_: *mut crate::leanh::LeanObject,
    mut v_a_4030_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4031_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__2(v___x_4024_, v_reverted_4025_, v_fst_4026_, v_n_4027_, v_j_4028_, v_a_4029_, v_a_4030_);
    crate::leanh::lean_dec(v_n_4027_);
    crate::leanh::lean_dec_ref(v_fst_4026_);
    crate::leanh::lean_dec_ref(v_reverted_4025_);
    crate::leanh::lean_dec(v___x_4024_);
    return v_res_4031_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0(
    mut v_00_u03b2_4032_: *mut crate::leanh::LeanObject,
    mut v_x_4033_: *mut crate::leanh::LeanObject,
    mut v_x_4034_: *mut crate::leanh::LeanObject,
    mut v_x_4035_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4036_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0___redArg(v_x_4033_, v_x_4034_, v_x_4035_);
    return v___x_4036_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2(
    mut v_00_u03b2_4037_: *mut crate::leanh::LeanObject,
    mut v_x_4038_: *mut crate::leanh::LeanObject,
    mut v_x_4039_: usize,
    mut v_x_4040_: usize,
    mut v_x_4041_: *mut crate::leanh::LeanObject,
    mut v_x_4042_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4043_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___redArg(v_x_4038_, v_x_4039_, v_x_4040_, v_x_4041_, v_x_4042_);
    return v___x_4043_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b2_4044_: *mut crate::leanh::LeanObject,
    mut v_x_4045_: *mut crate::leanh::LeanObject,
    mut v_x_4046_: *mut crate::leanh::LeanObject,
    mut v_x_4047_: *mut crate::leanh::LeanObject,
    mut v_x_4048_: *mut crate::leanh::LeanObject,
    mut v_x_4049_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_11499__boxed_4050_: usize = 0;
    let mut v_x_11500__boxed_4051_: usize = 0;
    let mut v_res_4052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_11499__boxed_4050_ = crate::leanh::lean_unbox_usize(v_x_4046_);
    crate::leanh::lean_dec(v_x_4046_);
    v_x_11500__boxed_4051_ = crate::leanh::lean_unbox_usize(v_x_4047_);
    crate::leanh::lean_dec(v_x_4047_);
    v_res_4052_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2(v_00_u03b2_4044_, v_x_4045_, v_x_11499__boxed_4050_, v_x_11500__boxed_4051_, v_x_4048_, v_x_4049_);
    return v_res_4052_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8(
    mut v_00_u03b2_4053_: *mut crate::leanh::LeanObject,
    mut v_n_4054_: *mut crate::leanh::LeanObject,
    mut v_k_4055_: *mut crate::leanh::LeanObject,
    mut v_v_4056_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4057_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8___redArg(v_n_4054_, v_k_4055_, v_v_4056_);
    return v___x_4057_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9(
    mut v_00_u03b2_4058_: *mut crate::leanh::LeanObject,
    mut v_depth_4059_: usize,
    mut v_keys_4060_: *mut crate::leanh::LeanObject,
    mut v_vals_4061_: *mut crate::leanh::LeanObject,
    mut v_heq_4062_: *mut crate::leanh::LeanObject,
    mut v_i_4063_: *mut crate::leanh::LeanObject,
    mut v_entries_4064_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4065_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9___redArg(v_depth_4059_, v_keys_4060_, v_vals_4061_, v_i_4063_, v_entries_4064_);
    return v___x_4065_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9___boxed(
    mut v_00_u03b2_4066_: *mut crate::leanh::LeanObject,
    mut v_depth_4067_: *mut crate::leanh::LeanObject,
    mut v_keys_4068_: *mut crate::leanh::LeanObject,
    mut v_vals_4069_: *mut crate::leanh::LeanObject,
    mut v_heq_4070_: *mut crate::leanh::LeanObject,
    mut v_i_4071_: *mut crate::leanh::LeanObject,
    mut v_entries_4072_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_4073_: usize = 0;
    let mut v_res_4074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_4073_ = crate::leanh::lean_unbox_usize(v_depth_4067_);
    crate::leanh::lean_dec(v_depth_4067_);
    v_res_4074_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__9(v_00_u03b2_4066_, v_depth_boxed_4073_, v_keys_4068_, v_vals_4069_, v_heq_4070_, v_i_4071_, v_entries_4072_);
    crate::leanh::lean_dec_ref(v_vals_4069_);
    crate::leanh::lean_dec_ref(v_keys_4068_);
    return v_res_4074_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8_spec__9(
    mut v_00_u03b2_4075_: *mut crate::leanh::LeanObject,
    mut v_x_4076_: *mut crate::leanh::LeanObject,
    mut v_x_4077_: *mut crate::leanh::LeanObject,
    mut v_x_4078_: *mut crate::leanh::LeanObject,
    mut v_x_4079_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4080_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__0_spec__0_spec__2_spec__8_spec__9___redArg(v_x_4076_, v_x_4077_, v_x_4078_, v_x_4079_);
    return v___x_4080_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize(
    mut v_mvarId_4083_: *mut crate::leanh::LeanObject,
    mut v_givenNames_4084_: *mut crate::leanh::LeanObject,
    mut v_recursorInfo_4085_: *mut crate::leanh::LeanObject,
    mut v_reverted_4086_: *mut crate::leanh::LeanObject,
    mut v_major_4087_: *mut crate::leanh::LeanObject,
    mut v_indices_4088_: *mut crate::leanh::LeanObject,
    mut v_baseSubst_4089_: *mut crate::leanh::LeanObject,
    mut v_recursor_4090_: *mut crate::leanh::LeanObject,
    mut v_a_4091_: *mut crate::leanh::LeanObject,
    mut v_a_4092_: *mut crate::leanh::LeanObject,
    mut v_a_4093_: *mut crate::leanh::LeanObject,
    mut v_a_4094_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_paramsPos_4100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_produceMotive_4101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: u8 = 0;
    let mut v___x_4109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4114_: u8 = 0;
    let mut v___x_4116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4118_: u8 = 0;
    let mut v_a_4119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4122_: u8 = 0;
    let mut v___x_4124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4126_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_mvarId_4083_);
                v___x_4096_ = l_Lean_MVarId_getType(
                    v_mvarId_4083_,
                    v_a_4091_,
                    v_a_4092_,
                    v_a_4093_,
                    v_a_4094_,
                );
                if crate::leanh::lean_obj_tag(v___x_4096_) == 0 {
                    v_a_4097_ = crate::leanh::lean_ctor_get(v___x_4096_, 0);
                    crate::leanh::lean_inc(v_a_4097_);
                    crate::leanh::lean_dec_ref_known(v___x_4096_, 1);
                    crate::leanh::lean_inc(v_a_4094_);
                    crate::leanh::lean_inc_ref(v_a_4093_);
                    crate::leanh::lean_inc(v_a_4092_);
                    crate::leanh::lean_inc_ref(v_a_4091_);
                    crate::leanh::lean_inc_ref(v_recursor_4090_);
                    v___x_4098_ = lean_infer_type(
                        v_recursor_4090_,
                        v_a_4091_,
                        v_a_4092_,
                        v_a_4093_,
                        v_a_4094_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4098_) == 0 {
                        v_a_4099_ = crate::leanh::lean_ctor_get(v___x_4098_, 0);
                        crate::leanh::lean_inc(v_a_4099_);
                        crate::leanh::lean_dec_ref_known(v___x_4098_, 1);
                        v_paramsPos_4100_ = crate::leanh::lean_ctor_get(v_recursorInfo_4085_, 5);
                        v_produceMotive_4101_ =
                            crate::leanh::lean_ctor_get(v_recursorInfo_4085_, 7);
                        v___x_4102_ =
                            l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTargetArity(
                                v_a_4097_,
                            );
                        v___x_4103_ = l_List_lengthTR___redArg(v_produceMotive_4101_);
                        v___x_4104_ = l_List_lengthTR___redArg(v_paramsPos_4100_);
                        v___x_4105_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_4106_ = lean_nat_add(v___x_4104_, v___x_4105_);
                        crate::leanh::lean_dec(v___x_4104_);
                        v___x_4107_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_4108_ = 0;
                        v___x_4109_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize___closed__0;
                        v___x_4110_ =
                            l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop(
                                v_mvarId_4083_,
                                v_givenNames_4084_,
                                v_recursorInfo_4085_,
                                v_reverted_4086_,
                                v_major_4087_,
                                v_indices_4088_,
                                v_baseSubst_4089_,
                                v___x_4102_,
                                v___x_4103_,
                                v___x_4106_,
                                v___x_4107_,
                                v_recursor_4090_,
                                v_a_4099_,
                                v___x_4108_,
                                v___x_4109_,
                                v_a_4091_,
                                v_a_4092_,
                                v_a_4093_,
                                v_a_4094_,
                            );
                        crate::leanh::lean_dec(v___x_4103_);
                        crate::leanh::lean_dec(v___x_4102_);
                        return v___x_4110_;
                    } else {
                        crate::leanh::lean_dec(v_a_4097_);
                        crate::leanh::lean_dec_ref(v_recursor_4090_);
                        crate::leanh::lean_dec(v_baseSubst_4089_);
                        crate::leanh::lean_dec_ref(v_major_4087_);
                        crate::leanh::lean_dec(v_mvarId_4083_);
                        v_a_4111_ = crate::leanh::lean_ctor_get(v___x_4098_, 0);
                        v_isSharedCheck_4118_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4098_)) as u8;
                        if v_isSharedCheck_4118_ == 0 {
                            v___x_4113_ = v___x_4098_;
                            v_isShared_4114_ = v_isSharedCheck_4118_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4111_);
                            crate::leanh::lean_dec(v___x_4098_);
                            v___x_4113_ = crate::leanh::lean_box(0);
                            v_isShared_4114_ = v_isSharedCheck_4118_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_recursor_4090_);
                    crate::leanh::lean_dec(v_baseSubst_4089_);
                    crate::leanh::lean_dec_ref(v_major_4087_);
                    crate::leanh::lean_dec(v_mvarId_4083_);
                    v_a_4119_ = crate::leanh::lean_ctor_get(v___x_4096_, 0);
                    v_isSharedCheck_4126_ = (!crate::leanh::lean_is_exclusive(v___x_4096_)) as u8;
                    if v_isSharedCheck_4126_ == 0 {
                        v___x_4121_ = v___x_4096_;
                        v_isShared_4122_ = v_isSharedCheck_4126_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4119_);
                        crate::leanh::lean_dec(v___x_4096_);
                        v___x_4121_ = crate::leanh::lean_box(0);
                        v_isShared_4122_ = v_isSharedCheck_4126_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4114_ == 0 {
                    v___x_4116_ = v___x_4113_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4117_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4117_, 0, v_a_4111_);
                    v___x_4116_ = v_reuseFailAlloc_4117_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4116_;
            }
            3 => {
                if v_isShared_4122_ == 0 {
                    v___x_4124_ = v___x_4121_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4125_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4125_, 0, v_a_4119_);
                    v___x_4124_ = v_reuseFailAlloc_4125_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4124_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize___boxed(
    mut v_mvarId_4127_: *mut crate::leanh::LeanObject,
    mut v_givenNames_4128_: *mut crate::leanh::LeanObject,
    mut v_recursorInfo_4129_: *mut crate::leanh::LeanObject,
    mut v_reverted_4130_: *mut crate::leanh::LeanObject,
    mut v_major_4131_: *mut crate::leanh::LeanObject,
    mut v_indices_4132_: *mut crate::leanh::LeanObject,
    mut v_baseSubst_4133_: *mut crate::leanh::LeanObject,
    mut v_recursor_4134_: *mut crate::leanh::LeanObject,
    mut v_a_4135_: *mut crate::leanh::LeanObject,
    mut v_a_4136_: *mut crate::leanh::LeanObject,
    mut v_a_4137_: *mut crate::leanh::LeanObject,
    mut v_a_4138_: *mut crate::leanh::LeanObject,
    mut v_a_4139_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4140_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize(
        v_mvarId_4127_,
        v_givenNames_4128_,
        v_recursorInfo_4129_,
        v_reverted_4130_,
        v_major_4131_,
        v_indices_4132_,
        v_baseSubst_4133_,
        v_recursor_4134_,
        v_a_4135_,
        v_a_4136_,
        v_a_4137_,
        v_a_4138_,
    );
    crate::leanh::lean_dec(v_a_4138_);
    crate::leanh::lean_dec_ref(v_a_4137_);
    crate::leanh::lean_dec(v_a_4136_);
    crate::leanh::lean_dec_ref(v_a_4135_);
    crate::leanh::lean_dec_ref(v_indices_4132_);
    crate::leanh::lean_dec_ref(v_reverted_4130_);
    crate::leanh::lean_dec_ref(v_recursorInfo_4129_);
    crate::leanh::lean_dec_ref(v_givenNames_4128_);
    return v_res_4140_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4142_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__0;
    v___x_4143_ = l_Lean_stringToMessageData(v___x_4142_);
    return v___x_4143_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(
    mut v_tacticName_4144_: *mut crate::leanh::LeanObject,
    mut v_mvarId_4145_: *mut crate::leanh::LeanObject,
    mut v_majorType_4146_: *mut crate::leanh::LeanObject,
    mut v_a_4147_: *mut crate::leanh::LeanObject,
    mut v_a_4148_: *mut crate::leanh::LeanObject,
    mut v_a_4149_: *mut crate::leanh::LeanObject,
    mut v_a_4150_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4152_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__1_once), _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___closed__1);
    v___x_4153_ = l_Lean_indentExpr(v_majorType_4146_);
    v___x_4154_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4154_, 0, v___x_4152_);
    crate::leanh::lean_ctor_set(v___x_4154_, 1, v___x_4153_);
    v___x_4155_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4155_, 0, v___x_4154_);
    v___x_4156_ = l_Lean_Meta_throwTacticEx___redArg(
        v_tacticName_4144_,
        v_mvarId_4145_,
        v___x_4155_,
        v_a_4147_,
        v_a_4148_,
        v_a_4149_,
        v_a_4150_,
    );
    return v___x_4156_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg___boxed(
    mut v_tacticName_4157_: *mut crate::leanh::LeanObject,
    mut v_mvarId_4158_: *mut crate::leanh::LeanObject,
    mut v_majorType_4159_: *mut crate::leanh::LeanObject,
    mut v_a_4160_: *mut crate::leanh::LeanObject,
    mut v_a_4161_: *mut crate::leanh::LeanObject,
    mut v_a_4162_: *mut crate::leanh::LeanObject,
    mut v_a_4163_: *mut crate::leanh::LeanObject,
    mut v_a_4164_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4165_ =
        l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(
            v_tacticName_4157_,
            v_mvarId_4158_,
            v_majorType_4159_,
            v_a_4160_,
            v_a_4161_,
            v_a_4162_,
            v_a_4163_,
        );
    crate::leanh::lean_dec(v_a_4163_);
    crate::leanh::lean_dec_ref(v_a_4162_);
    crate::leanh::lean_dec(v_a_4161_);
    crate::leanh::lean_dec_ref(v_a_4160_);
    return v_res_4165_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType(
    mut v_00_u03b1_4166_: *mut crate::leanh::LeanObject,
    mut v_tacticName_4167_: *mut crate::leanh::LeanObject,
    mut v_mvarId_4168_: *mut crate::leanh::LeanObject,
    mut v_majorType_4169_: *mut crate::leanh::LeanObject,
    mut v_a_4170_: *mut crate::leanh::LeanObject,
    mut v_a_4171_: *mut crate::leanh::LeanObject,
    mut v_a_4172_: *mut crate::leanh::LeanObject,
    mut v_a_4173_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4175_ =
        l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(
            v_tacticName_4167_,
            v_mvarId_4168_,
            v_majorType_4169_,
            v_a_4170_,
            v_a_4171_,
            v_a_4172_,
            v_a_4173_,
        );
    return v___x_4175_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___boxed(
    mut v_00_u03b1_4176_: *mut crate::leanh::LeanObject,
    mut v_tacticName_4177_: *mut crate::leanh::LeanObject,
    mut v_mvarId_4178_: *mut crate::leanh::LeanObject,
    mut v_majorType_4179_: *mut crate::leanh::LeanObject,
    mut v_a_4180_: *mut crate::leanh::LeanObject,
    mut v_a_4181_: *mut crate::leanh::LeanObject,
    mut v_a_4182_: *mut crate::leanh::LeanObject,
    mut v_a_4183_: *mut crate::leanh::LeanObject,
    mut v_a_4184_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4185_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType(
        v_00_u03b1_4176_,
        v_tacticName_4177_,
        v_mvarId_4178_,
        v_majorType_4179_,
        v_a_4180_,
        v_a_4181_,
        v_a_4182_,
        v_a_4183_,
    );
    crate::leanh::lean_dec(v_a_4183_);
    crate::leanh::lean_dec_ref(v_a_4182_);
    crate::leanh::lean_dec(v_a_4181_);
    crate::leanh::lean_dec_ref(v_a_4180_);
    return v_res_4185_;
}
pub unsafe fn l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__0(
    mut v_fvarId_4186_: *mut crate::leanh::LeanObject,
    mut v_x_4187_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4188_: u8 = 0;
    v___x_4188_ = l_Lean_instBEqFVarId_beq(v_fvarId_4186_, v_x_4187_);
    return v___x_4188_;
}
pub unsafe fn l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__0___boxed(
    mut v_fvarId_4189_: *mut crate::leanh::LeanObject,
    mut v_x_4190_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4191_: u8 = 0;
    let mut v_r_4192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4191_ =
        l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__0(
            v_fvarId_4189_,
            v_x_4190_,
        );
    crate::leanh::lean_dec(v_x_4190_);
    crate::leanh::lean_dec(v_fvarId_4189_);
    v_r_4192_ = crate::leanh::lean_box((v_res_4191_) as usize);
    return v_r_4192_;
}
pub unsafe fn l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__1(
    mut v_x_4193_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4194_: u8 = 0;
    v___x_4194_ = 0;
    return v___x_4194_;
}
pub unsafe fn l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__1___boxed(
    mut v_x_4195_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4196_: u8 = 0;
    let mut v_r_4197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4196_ =
        l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__1(
            v_x_4195_,
        );
    crate::leanh::lean_dec(v_x_4195_);
    v_r_4197_ = crate::leanh::lean_box((v_res_4196_) as usize);
    return v_r_4197_;
}
pub unsafe fn _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4199_ = crate::leanh::lean_box(0);
    v___x_4200_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_4201_ = lean_mk_array(v___x_4200_, v___x_4199_);
    return v___x_4201_;
}
pub unsafe fn _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4202_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__1_once), _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__1);
    v___x_4203_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4204_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4204_, 0, v___x_4203_);
    crate::leanh::lean_ctor_set(v___x_4204_, 1, v___x_4202_);
    return v___x_4204_;
}
pub unsafe fn l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg(
    mut v_localDecl_4205_: *mut crate::leanh::LeanObject,
    mut v_fvarId_4206_: *mut crate::leanh::LeanObject,
    mut v_generalizeNondepLet_4207_: u8,
    mut v___y_4208_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_4211_: u8 = 0;
    let mut v_snd_4212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_4215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_4217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4221_: u8 = 0;
    let mut v___x_4223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4228_: u8 = 0;
    let mut v_unused_4229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4234_: u8 = 0;
    let mut v___f_4235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4240_: u8 = 0;
    let mut v_mctx_4241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_4243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_4245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4249_: u8 = 0;
    let mut v___x_4251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4256_: u8 = 0;
    let mut v_unused_4257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4263_: u8 = 0;
    let mut v_mctx_4264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4267_: u8 = 0;
    let mut v___x_4268_: u8 = 0;
    let mut v___x_4269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nondep_4273_: u8 = 0;
    let mut v_fst_4275_: u8 = 0;
    let mut v_snd_4276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4277_: u8 = 0;
    let mut v___x_4278_: u8 = 0;
    let mut v___x_4279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4285_: u8 = 0;
    let mut v___x_4287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4291_: u8 = 0;
    let mut v___x_4292_: u8 = 0;
    let mut v___x_4293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4297_: u8 = 0;
    let mut v_mctx_4298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_4300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_4302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4306_: u8 = 0;
    let mut v___x_4308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4313_: u8 = 0;
    let mut v_unused_4314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4320_: u8 = 0;
    let mut v_mctx_4321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4324_: u8 = 0;
    let mut v___x_4325_: u8 = 0;
    let mut v___x_4326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_4235_ = crate::leanh::lean_alloc_closure(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
                crate::leanh::lean_closure_set(v___f_4235_, 0, v_fvarId_4206_);
                v___f_4236_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__0;
                if crate::leanh::lean_obj_tag(v_localDecl_4205_) == 0 {
                    v_type_4237_ = crate::leanh::lean_ctor_get(v_localDecl_4205_, 3);
                    crate::leanh::lean_inc_ref(v_type_4237_);
                    crate::leanh::lean_dec_ref_known(v_localDecl_4205_, 4);
                    v___x_4238_ = lean_st_ref_get(v___y_4208_);
                    v_mctx_4264_ = crate::leanh::lean_ctor_get(v___x_4238_, 0);
                    crate::leanh::lean_inc_ref_n(v_mctx_4264_, 2);
                    crate::leanh::lean_dec(v___x_4238_);
                    v___x_4265_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2_once), _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2);
                    v___x_4266_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4266_, 0, v___x_4265_);
                    crate::leanh::lean_ctor_set(v___x_4266_, 1, v_mctx_4264_);
                    v___x_4267_ = l_Lean_Expr_hasFVar(v_type_4237_);
                    if v___x_4267_ == 0 {
                        v___x_4268_ = l_Lean_Expr_hasMVar(v_type_4237_);
                        if v___x_4268_ == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_4266_, 2);
                            crate::leanh::lean_dec_ref(v_type_4237_);
                            crate::leanh::lean_dec_ref(v___f_4235_);
                            v_fst_4240_ = v___x_4268_;
                            v_mctx_4241_ = v_mctx_4264_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_mctx_4264_);
                            v___x_4269_ =
                                l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(
                                    v___f_4235_,
                                    v___f_4236_,
                                    v_type_4237_,
                                    v___x_4266_,
                                );
                            v___y_4259_ = v___x_4269_;
                            state = 8;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_mctx_4264_);
                        v___x_4270_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(
                            v___f_4235_,
                            v___f_4236_,
                            v_type_4237_,
                            v___x_4266_,
                        );
                        v___y_4259_ = v___x_4270_;
                        state = 8;
                        continue;
                    }
                } else {
                    v_type_4271_ = crate::leanh::lean_ctor_get(v_localDecl_4205_, 3);
                    crate::leanh::lean_inc_ref(v_type_4271_);
                    v_value_4272_ = crate::leanh::lean_ctor_get(v_localDecl_4205_, 4);
                    crate::leanh::lean_inc_ref(v_value_4272_);
                    v_nondep_4273_ = crate::leanh::lean_ctor_get_uint8(
                        v_localDecl_4205_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    );
                    crate::leanh::lean_dec_ref_known(v_localDecl_4205_, 5);
                    if v_generalizeNondepLet_4207_ == 0 {
                        state = 11;
                        continue;
                    } else {
                        if v_nondep_4273_ == 0 {
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_value_4272_);
                            v___x_4295_ = lean_st_ref_get(v___y_4208_);
                            v_mctx_4321_ = crate::leanh::lean_ctor_get(v___x_4295_, 0);
                            crate::leanh::lean_inc_ref_n(v_mctx_4321_, 2);
                            crate::leanh::lean_dec(v___x_4295_);
                            v___x_4322_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2_once), _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2);
                            v___x_4323_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4323_, 0, v___x_4322_);
                            crate::leanh::lean_ctor_set(v___x_4323_, 1, v_mctx_4321_);
                            v___x_4324_ = l_Lean_Expr_hasFVar(v_type_4271_);
                            if v___x_4324_ == 0 {
                                v___x_4325_ = l_Lean_Expr_hasMVar(v_type_4271_);
                                if v___x_4325_ == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_4323_, 2);
                                    crate::leanh::lean_dec_ref(v_type_4271_);
                                    crate::leanh::lean_dec_ref(v___f_4235_);
                                    v_fst_4297_ = v___x_4325_;
                                    v_mctx_4298_ = v_mctx_4321_;
                                    state = 12;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec_ref(v_mctx_4321_);
                                    v___x_4326_ =
                                        l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(
                                            v___f_4235_,
                                            v___f_4236_,
                                            v_type_4271_,
                                            v___x_4323_,
                                        );
                                    v___y_4316_ = v___x_4326_;
                                    state = 15;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v_mctx_4321_);
                                v___x_4327_ =
                                    l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(
                                        v___f_4235_,
                                        v___f_4236_,
                                        v_type_4271_,
                                        v___x_4323_,
                                    );
                                v___y_4316_ = v___x_4327_;
                                state = 15;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v_mctx_4213_ = crate::leanh::lean_ctor_get(v_snd_4212_, 1);
                crate::leanh::lean_inc_ref(v_mctx_4213_);
                crate::leanh::lean_dec_ref(v_snd_4212_);
                v___x_4214_ = lean_st_ref_take(v___y_4208_);
                v_cache_4215_ = crate::leanh::lean_ctor_get(v___x_4214_, 1);
                v_zetaDeltaFVarIds_4216_ = crate::leanh::lean_ctor_get(v___x_4214_, 2);
                v_postponed_4217_ = crate::leanh::lean_ctor_get(v___x_4214_, 3);
                v_diag_4218_ = crate::leanh::lean_ctor_get(v___x_4214_, 4);
                v_isSharedCheck_4228_ = (!crate::leanh::lean_is_exclusive(v___x_4214_)) as u8;
                if v_isSharedCheck_4228_ == 0 {
                    v_unused_4229_ = crate::leanh::lean_ctor_get(v___x_4214_, 0);
                    crate::leanh::lean_dec(v_unused_4229_);
                    v___x_4220_ = v___x_4214_;
                    v_isShared_4221_ = v_isSharedCheck_4228_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_4218_);
                    crate::leanh::lean_inc(v_postponed_4217_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_4216_);
                    crate::leanh::lean_inc(v_cache_4215_);
                    crate::leanh::lean_dec(v___x_4214_);
                    v___x_4220_ = crate::leanh::lean_box(0);
                    v_isShared_4221_ = v_isSharedCheck_4228_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_4221_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4220_, 0, v_mctx_4213_);
                    v___x_4223_ = v___x_4220_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4227_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4227_, 0, v_mctx_4213_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4227_, 1, v_cache_4215_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4227_,
                        2,
                        v_zetaDeltaFVarIds_4216_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4227_, 3, v_postponed_4217_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4227_, 4, v_diag_4218_);
                    v___x_4223_ = v_reuseFailAlloc_4227_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4224_ = lean_st_ref_set(v___y_4208_, v___x_4223_);
                v___x_4225_ = crate::leanh::lean_box((v_fst_4211_) as usize);
                v___x_4226_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4226_, 0, v___x_4225_);
                return v___x_4226_;
            }
            4 => {
                v_fst_4232_ = crate::leanh::lean_ctor_get(v___y_4231_, 0);
                crate::leanh::lean_inc(v_fst_4232_);
                v_snd_4233_ = crate::leanh::lean_ctor_get(v___y_4231_, 1);
                crate::leanh::lean_inc(v_snd_4233_);
                crate::leanh::lean_dec_ref(v___y_4231_);
                v___x_4234_ = (crate::leanh::lean_unbox(v_fst_4232_) as u8);
                crate::leanh::lean_dec(v_fst_4232_);
                v_fst_4211_ = v___x_4234_;
                v_snd_4212_ = v_snd_4233_;
                state = 1;
                continue;
            }
            5 => {
                v___x_4242_ = lean_st_ref_take(v___y_4208_);
                v_cache_4243_ = crate::leanh::lean_ctor_get(v___x_4242_, 1);
                v_zetaDeltaFVarIds_4244_ = crate::leanh::lean_ctor_get(v___x_4242_, 2);
                v_postponed_4245_ = crate::leanh::lean_ctor_get(v___x_4242_, 3);
                v_diag_4246_ = crate::leanh::lean_ctor_get(v___x_4242_, 4);
                v_isSharedCheck_4256_ = (!crate::leanh::lean_is_exclusive(v___x_4242_)) as u8;
                if v_isSharedCheck_4256_ == 0 {
                    v_unused_4257_ = crate::leanh::lean_ctor_get(v___x_4242_, 0);
                    crate::leanh::lean_dec(v_unused_4257_);
                    v___x_4248_ = v___x_4242_;
                    v_isShared_4249_ = v_isSharedCheck_4256_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_4246_);
                    crate::leanh::lean_inc(v_postponed_4245_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_4244_);
                    crate::leanh::lean_inc(v_cache_4243_);
                    crate::leanh::lean_dec(v___x_4242_);
                    v___x_4248_ = crate::leanh::lean_box(0);
                    v_isShared_4249_ = v_isSharedCheck_4256_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_4249_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4248_, 0, v_mctx_4241_);
                    v___x_4251_ = v___x_4248_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4255_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4255_, 0, v_mctx_4241_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4255_, 1, v_cache_4243_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4255_,
                        2,
                        v_zetaDeltaFVarIds_4244_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4255_, 3, v_postponed_4245_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4255_, 4, v_diag_4246_);
                    v___x_4251_ = v_reuseFailAlloc_4255_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_4252_ = lean_st_ref_set(v___y_4208_, v___x_4251_);
                v___x_4253_ = crate::leanh::lean_box((v_fst_4240_) as usize);
                v___x_4254_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4254_, 0, v___x_4253_);
                return v___x_4254_;
            }
            8 => {
                v_snd_4260_ = crate::leanh::lean_ctor_get(v___y_4259_, 1);
                crate::leanh::lean_inc(v_snd_4260_);
                v_fst_4261_ = crate::leanh::lean_ctor_get(v___y_4259_, 0);
                crate::leanh::lean_inc(v_fst_4261_);
                crate::leanh::lean_dec_ref(v___y_4259_);
                v_mctx_4262_ = crate::leanh::lean_ctor_get(v_snd_4260_, 1);
                crate::leanh::lean_inc_ref(v_mctx_4262_);
                crate::leanh::lean_dec(v_snd_4260_);
                v___x_4263_ = (crate::leanh::lean_unbox(v_fst_4261_) as u8);
                crate::leanh::lean_dec(v_fst_4261_);
                v_fst_4240_ = v___x_4263_;
                v_mctx_4241_ = v_mctx_4262_;
                state = 5;
                continue;
            }
            9 => {
                if v_fst_4275_ == 0 {
                    v___x_4277_ = l_Lean_Expr_hasFVar(v_value_4272_);
                    if v___x_4277_ == 0 {
                        v___x_4278_ = l_Lean_Expr_hasMVar(v_value_4272_);
                        if v___x_4278_ == 0 {
                            crate::leanh::lean_dec_ref(v_value_4272_);
                            crate::leanh::lean_dec_ref(v___f_4235_);
                            v_fst_4211_ = v___x_4278_;
                            v_snd_4212_ = v_snd_4276_;
                            state = 1;
                            continue;
                        } else {
                            v___x_4279_ =
                                l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(
                                    v___f_4235_,
                                    v___f_4236_,
                                    v_value_4272_,
                                    v_snd_4276_,
                                );
                            v___y_4231_ = v___x_4279_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v___x_4280_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(
                            v___f_4235_,
                            v___f_4236_,
                            v_value_4272_,
                            v_snd_4276_,
                        );
                        v___y_4231_ = v___x_4280_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_value_4272_);
                    crate::leanh::lean_dec_ref(v___f_4235_);
                    v_fst_4211_ = v_fst_4275_;
                    v_snd_4212_ = v_snd_4276_;
                    state = 1;
                    continue;
                }
            }
            10 => {
                v_fst_4283_ = crate::leanh::lean_ctor_get(v___y_4282_, 0);
                crate::leanh::lean_inc(v_fst_4283_);
                v_snd_4284_ = crate::leanh::lean_ctor_get(v___y_4282_, 1);
                crate::leanh::lean_inc(v_snd_4284_);
                crate::leanh::lean_dec_ref(v___y_4282_);
                v___x_4285_ = (crate::leanh::lean_unbox(v_fst_4283_) as u8);
                crate::leanh::lean_dec(v_fst_4283_);
                v_fst_4275_ = v___x_4285_;
                v_snd_4276_ = v_snd_4284_;
                state = 9;
                continue;
            }
            11 => {
                v___x_4287_ = lean_st_ref_get(v___y_4208_);
                v_mctx_4288_ = crate::leanh::lean_ctor_get(v___x_4287_, 0);
                crate::leanh::lean_inc_ref(v_mctx_4288_);
                crate::leanh::lean_dec(v___x_4287_);
                v___x_4289_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2_once), _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2);
                v___x_4290_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4290_, 0, v___x_4289_);
                crate::leanh::lean_ctor_set(v___x_4290_, 1, v_mctx_4288_);
                v___x_4291_ = l_Lean_Expr_hasFVar(v_type_4271_);
                if v___x_4291_ == 0 {
                    v___x_4292_ = l_Lean_Expr_hasMVar(v_type_4271_);
                    if v___x_4292_ == 0 {
                        crate::leanh::lean_dec_ref(v_type_4271_);
                        v_fst_4275_ = v___x_4292_;
                        v_snd_4276_ = v___x_4290_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc_ref(v___f_4235_);
                        v___x_4293_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(
                            v___f_4235_,
                            v___f_4236_,
                            v_type_4271_,
                            v___x_4290_,
                        );
                        v___y_4282_ = v___x_4293_;
                        state = 10;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v___f_4235_);
                    v___x_4294_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(
                        v___f_4235_,
                        v___f_4236_,
                        v_type_4271_,
                        v___x_4290_,
                    );
                    v___y_4282_ = v___x_4294_;
                    state = 10;
                    continue;
                }
            }
            12 => {
                v___x_4299_ = lean_st_ref_take(v___y_4208_);
                v_cache_4300_ = crate::leanh::lean_ctor_get(v___x_4299_, 1);
                v_zetaDeltaFVarIds_4301_ = crate::leanh::lean_ctor_get(v___x_4299_, 2);
                v_postponed_4302_ = crate::leanh::lean_ctor_get(v___x_4299_, 3);
                v_diag_4303_ = crate::leanh::lean_ctor_get(v___x_4299_, 4);
                v_isSharedCheck_4313_ = (!crate::leanh::lean_is_exclusive(v___x_4299_)) as u8;
                if v_isSharedCheck_4313_ == 0 {
                    v_unused_4314_ = crate::leanh::lean_ctor_get(v___x_4299_, 0);
                    crate::leanh::lean_dec(v_unused_4314_);
                    v___x_4305_ = v___x_4299_;
                    v_isShared_4306_ = v_isSharedCheck_4313_;
                    state = 13;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_4303_);
                    crate::leanh::lean_inc(v_postponed_4302_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_4301_);
                    crate::leanh::lean_inc(v_cache_4300_);
                    crate::leanh::lean_dec(v___x_4299_);
                    v___x_4305_ = crate::leanh::lean_box(0);
                    v_isShared_4306_ = v_isSharedCheck_4313_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_4306_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4305_, 0, v_mctx_4298_);
                    v___x_4308_ = v___x_4305_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4312_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4312_, 0, v_mctx_4298_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4312_, 1, v_cache_4300_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4312_,
                        2,
                        v_zetaDeltaFVarIds_4301_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4312_, 3, v_postponed_4302_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4312_, 4, v_diag_4303_);
                    v___x_4308_ = v_reuseFailAlloc_4312_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_4309_ = lean_st_ref_set(v___y_4208_, v___x_4308_);
                v___x_4310_ = crate::leanh::lean_box((v_fst_4297_) as usize);
                v___x_4311_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4311_, 0, v___x_4310_);
                return v___x_4311_;
            }
            15 => {
                v_snd_4317_ = crate::leanh::lean_ctor_get(v___y_4316_, 1);
                crate::leanh::lean_inc(v_snd_4317_);
                v_fst_4318_ = crate::leanh::lean_ctor_get(v___y_4316_, 0);
                crate::leanh::lean_inc(v_fst_4318_);
                crate::leanh::lean_dec_ref(v___y_4316_);
                v_mctx_4319_ = crate::leanh::lean_ctor_get(v_snd_4317_, 1);
                crate::leanh::lean_inc_ref(v_mctx_4319_);
                crate::leanh::lean_dec(v_snd_4317_);
                v___x_4320_ = (crate::leanh::lean_unbox(v_fst_4318_) as u8);
                crate::leanh::lean_dec(v_fst_4318_);
                v_fst_4297_ = v___x_4320_;
                v_mctx_4298_ = v_mctx_4319_;
                state = 12;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___boxed(
    mut v_localDecl_4328_: *mut crate::leanh::LeanObject,
    mut v_fvarId_4329_: *mut crate::leanh::LeanObject,
    mut v_generalizeNondepLet_4330_: *mut crate::leanh::LeanObject,
    mut v___y_4331_: *mut crate::leanh::LeanObject,
    mut v___y_4332_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_generalizeNondepLet_boxed_4333_: u8 = 0;
    let mut v_res_4334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_generalizeNondepLet_boxed_4333_ =
        (crate::leanh::lean_unbox(v_generalizeNondepLet_4330_) as u8);
    v_res_4334_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg(
        v_localDecl_4328_,
        v_fvarId_4329_,
        v_generalizeNondepLet_boxed_4333_,
        v___y_4331_,
    );
    crate::leanh::lean_dec(v___y_4331_);
    return v_res_4334_;
}
pub unsafe fn l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0(
    mut v_localDecl_4335_: *mut crate::leanh::LeanObject,
    mut v_fvarId_4336_: *mut crate::leanh::LeanObject,
    mut v_generalizeNondepLet_4337_: u8,
    mut v___y_4338_: *mut crate::leanh::LeanObject,
    mut v___y_4339_: *mut crate::leanh::LeanObject,
    mut v___y_4340_: *mut crate::leanh::LeanObject,
    mut v___y_4341_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4343_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg(
        v_localDecl_4335_,
        v_fvarId_4336_,
        v_generalizeNondepLet_4337_,
        v___y_4339_,
    );
    return v___x_4343_;
}
pub unsafe fn l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___boxed(
    mut v_localDecl_4344_: *mut crate::leanh::LeanObject,
    mut v_fvarId_4345_: *mut crate::leanh::LeanObject,
    mut v_generalizeNondepLet_4346_: *mut crate::leanh::LeanObject,
    mut v___y_4347_: *mut crate::leanh::LeanObject,
    mut v___y_4348_: *mut crate::leanh::LeanObject,
    mut v___y_4349_: *mut crate::leanh::LeanObject,
    mut v___y_4350_: *mut crate::leanh::LeanObject,
    mut v___y_4351_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_generalizeNondepLet_boxed_4352_: u8 = 0;
    let mut v_res_4353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_generalizeNondepLet_boxed_4352_ =
        (crate::leanh::lean_unbox(v_generalizeNondepLet_4346_) as u8);
    v_res_4353_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0(
        v_localDecl_4344_,
        v_fvarId_4345_,
        v_generalizeNondepLet_boxed_4352_,
        v___y_4347_,
        v___y_4348_,
        v___y_4349_,
        v___y_4350_,
    );
    crate::leanh::lean_dec(v___y_4350_);
    crate::leanh::lean_dec_ref(v___y_4349_);
    crate::leanh::lean_dec(v___y_4348_);
    crate::leanh::lean_dec_ref(v___y_4347_);
    return v_res_4353_;
}
pub unsafe fn l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(
    mut v_e_4354_: *mut crate::leanh::LeanObject,
    mut v_fvarId_4355_: *mut crate::leanh::LeanObject,
    mut v___y_4356_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4360_: u8 = 0;
    let mut v_mctx_4361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_4363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_4365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4369_: u8 = 0;
    let mut v___x_4371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4376_: u8 = 0;
    let mut v_unused_4377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4383_: u8 = 0;
    let mut v_mctx_4384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4389_: u8 = 0;
    let mut v___x_4390_: u8 = 0;
    let mut v___x_4391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4358_ = lean_st_ref_get(v___y_4356_);
                v_mctx_4384_ = crate::leanh::lean_ctor_get(v___x_4358_, 0);
                crate::leanh::lean_inc_ref_n(v_mctx_4384_, 2);
                crate::leanh::lean_dec(v___x_4358_);
                v___f_4385_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__0;
                v___f_4386_ = crate::leanh::lean_alloc_closure(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
                crate::leanh::lean_closure_set(v___f_4386_, 0, v_fvarId_4355_);
                v___x_4387_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2_once), _init_l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg___closed__2);
                v___x_4388_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4388_, 0, v___x_4387_);
                crate::leanh::lean_ctor_set(v___x_4388_, 1, v_mctx_4384_);
                v___x_4389_ = l_Lean_Expr_hasFVar(v_e_4354_);
                if v___x_4389_ == 0 {
                    v___x_4390_ = l_Lean_Expr_hasMVar(v_e_4354_);
                    if v___x_4390_ == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_4388_, 2);
                        crate::leanh::lean_dec_ref(v___f_4386_);
                        crate::leanh::lean_dec_ref(v_e_4354_);
                        v_fst_4360_ = v___x_4390_;
                        v_mctx_4361_ = v_mctx_4384_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_mctx_4384_);
                        v___x_4391_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(
                            v___f_4386_,
                            v___f_4385_,
                            v_e_4354_,
                            v___x_4388_,
                        );
                        v___y_4379_ = v___x_4391_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_mctx_4384_);
                    v___x_4392_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(
                        v___f_4386_,
                        v___f_4385_,
                        v_e_4354_,
                        v___x_4388_,
                    );
                    v___y_4379_ = v___x_4392_;
                    state = 4;
                    continue;
                }
            }
            1 => {
                v___x_4362_ = lean_st_ref_take(v___y_4356_);
                v_cache_4363_ = crate::leanh::lean_ctor_get(v___x_4362_, 1);
                v_zetaDeltaFVarIds_4364_ = crate::leanh::lean_ctor_get(v___x_4362_, 2);
                v_postponed_4365_ = crate::leanh::lean_ctor_get(v___x_4362_, 3);
                v_diag_4366_ = crate::leanh::lean_ctor_get(v___x_4362_, 4);
                v_isSharedCheck_4376_ = (!crate::leanh::lean_is_exclusive(v___x_4362_)) as u8;
                if v_isSharedCheck_4376_ == 0 {
                    v_unused_4377_ = crate::leanh::lean_ctor_get(v___x_4362_, 0);
                    crate::leanh::lean_dec(v_unused_4377_);
                    v___x_4368_ = v___x_4362_;
                    v_isShared_4369_ = v_isSharedCheck_4376_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_4366_);
                    crate::leanh::lean_inc(v_postponed_4365_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_4364_);
                    crate::leanh::lean_inc(v_cache_4363_);
                    crate::leanh::lean_dec(v___x_4362_);
                    v___x_4368_ = crate::leanh::lean_box(0);
                    v_isShared_4369_ = v_isSharedCheck_4376_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_4369_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4368_, 0, v_mctx_4361_);
                    v___x_4371_ = v___x_4368_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4375_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4375_, 0, v_mctx_4361_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4375_, 1, v_cache_4363_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4375_,
                        2,
                        v_zetaDeltaFVarIds_4364_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4375_, 3, v_postponed_4365_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4375_, 4, v_diag_4366_);
                    v___x_4371_ = v_reuseFailAlloc_4375_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4372_ = lean_st_ref_set(v___y_4356_, v___x_4371_);
                v___x_4373_ = crate::leanh::lean_box((v_fst_4360_) as usize);
                v___x_4374_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4374_, 0, v___x_4373_);
                return v___x_4374_;
            }
            4 => {
                v_snd_4380_ = crate::leanh::lean_ctor_get(v___y_4379_, 1);
                crate::leanh::lean_inc(v_snd_4380_);
                v_fst_4381_ = crate::leanh::lean_ctor_get(v___y_4379_, 0);
                crate::leanh::lean_inc(v_fst_4381_);
                crate::leanh::lean_dec_ref(v___y_4379_);
                v_mctx_4382_ = crate::leanh::lean_ctor_get(v_snd_4380_, 1);
                crate::leanh::lean_inc_ref(v_mctx_4382_);
                crate::leanh::lean_dec(v_snd_4380_);
                v___x_4383_ = (crate::leanh::lean_unbox(v_fst_4381_) as u8);
                crate::leanh::lean_dec(v_fst_4381_);
                v_fst_4360_ = v___x_4383_;
                v_mctx_4361_ = v_mctx_4382_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg___boxed(
    mut v_e_4393_: *mut crate::leanh::LeanObject,
    mut v_fvarId_4394_: *mut crate::leanh::LeanObject,
    mut v___y_4395_: *mut crate::leanh::LeanObject,
    mut v___y_4396_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4397_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(
        v_e_4393_,
        v_fvarId_4394_,
        v___y_4395_,
    );
    crate::leanh::lean_dec(v___y_4395_);
    return v_res_4397_;
}
pub unsafe fn l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2(
    mut v_e_4398_: *mut crate::leanh::LeanObject,
    mut v_fvarId_4399_: *mut crate::leanh::LeanObject,
    mut v___y_4400_: *mut crate::leanh::LeanObject,
    mut v___y_4401_: *mut crate::leanh::LeanObject,
    mut v___y_4402_: *mut crate::leanh::LeanObject,
    mut v___y_4403_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4405_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(
        v_e_4398_,
        v_fvarId_4399_,
        v___y_4401_,
    );
    return v___x_4405_;
}
pub unsafe fn l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___boxed(
    mut v_e_4406_: *mut crate::leanh::LeanObject,
    mut v_fvarId_4407_: *mut crate::leanh::LeanObject,
    mut v___y_4408_: *mut crate::leanh::LeanObject,
    mut v___y_4409_: *mut crate::leanh::LeanObject,
    mut v___y_4410_: *mut crate::leanh::LeanObject,
    mut v___y_4411_: *mut crate::leanh::LeanObject,
    mut v___y_4412_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4413_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2(
        v_e_4406_,
        v_fvarId_4407_,
        v___y_4408_,
        v___y_4409_,
        v___y_4410_,
        v___y_4411_,
    );
    crate::leanh::lean_dec(v___y_4411_);
    crate::leanh::lean_dec_ref(v___y_4410_);
    crate::leanh::lean_dec(v___y_4409_);
    crate::leanh::lean_dec_ref(v___y_4408_);
    return v_res_4413_;
}
pub unsafe fn l_List_elem___at___00Lean_Meta_getMajorTypeIndices_spec__1(
    mut v_a_4414_: *mut crate::leanh::LeanObject,
    mut v_x_4415_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4416_: u8 = 0;
    let mut v_head_4417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4419_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4415_) == 0 {
                    v___x_4416_ = 0;
                    return v___x_4416_;
                } else {
                    v_head_4417_ = crate::leanh::lean_ctor_get(v_x_4415_, 0);
                    v_tail_4418_ = crate::leanh::lean_ctor_get(v_x_4415_, 1);
                    v___x_4419_ = lean_nat_dec_eq(v_a_4414_, v_head_4417_);
                    if v___x_4419_ == 0 {
                        v_x_4415_ = v_tail_4418_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_4419_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_elem___at___00Lean_Meta_getMajorTypeIndices_spec__1___boxed(
    mut v_a_4421_: *mut crate::leanh::LeanObject,
    mut v_x_4422_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4423_: u8 = 0;
    let mut v_r_4424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4423_ = l_List_elem___at___00Lean_Meta_getMajorTypeIndices_spec__1(v_a_4421_, v_x_4422_);
    crate::leanh::lean_dec(v_x_4422_);
    crate::leanh::lean_dec(v_a_4421_);
    v_r_4424_ = crate::leanh::lean_box((v_res_4423_) as usize);
    return v_r_4424_;
}
pub unsafe fn _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4426_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__0;
    v___x_4427_ = l_Lean_stringToMessageData(v___x_4426_);
    return v___x_4427_;
}
pub unsafe fn _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4429_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__2;
    v___x_4430_ = l_Lean_stringToMessageData(v___x_4429_);
    return v___x_4430_;
}
pub unsafe fn _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4432_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__4;
    v___x_4433_ = l_Lean_stringToMessageData(v___x_4432_);
    return v___x_4433_;
}
pub unsafe fn _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4435_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__6;
    v___x_4436_ = l_Lean_stringToMessageData(v___x_4435_);
    return v___x_4436_;
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg(
    mut v_majorTypeArgs_4437_: *mut crate::leanh::LeanObject,
    mut v_idx_4438_: *mut crate::leanh::LeanObject,
    mut v_tacticName_4439_: *mut crate::leanh::LeanObject,
    mut v_mvarId_4440_: *mut crate::leanh::LeanObject,
    mut v_idxPos_4441_: *mut crate::leanh::LeanObject,
    mut v_recursorInfo_4442_: *mut crate::leanh::LeanObject,
    mut v_majorType_4443_: *mut crate::leanh::LeanObject,
    mut v_n_4444_: *mut crate::leanh::LeanObject,
    mut v_i_4445_: *mut crate::leanh::LeanObject,
    mut v___y_4446_: *mut crate::leanh::LeanObject,
    mut v___y_4447_: *mut crate::leanh::LeanObject,
    mut v___y_4448_: *mut crate::leanh::LeanObject,
    mut v___y_4449_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_4451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_4452_: u8 = 0;
    let mut v___x_4453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_4455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_4456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_4462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4468_: u8 = 0;
    let mut v___x_4470_: u8 = 0;
    let mut v___x_4472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4480_: u8 = 0;
    let mut v___x_4481_: u8 = 0;
    let mut v___x_4483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4497_: u8 = 0;
    let mut v_a_4498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4501_: u8 = 0;
    let mut v___x_4503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4505_: u8 = 0;
    let mut v___y_4507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4511_: u8 = 0;
    let mut v_indicesPos_4512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4513_: u8 = 0;
    let mut v___y_4515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4519_: u8 = 0;
    let mut v___x_4520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4525_: u8 = 0;
    let mut v___x_4526_: u8 = 0;
    let mut v___x_4527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4538_: u8 = 0;
    let mut v___x_4539_: u8 = 0;
    let mut v___x_4540_: u8 = 0;
    let mut v___x_4541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_4451_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_4452_ = lean_nat_dec_eq(v_i_4445_, v_zero_4451_);
                if v_isZero_4452_ == 1 {
                    crate::leanh::lean_dec(v_i_4445_);
                    crate::leanh::lean_dec_ref(v_majorType_4443_);
                    crate::leanh::lean_dec(v_mvarId_4440_);
                    crate::leanh::lean_dec(v_tacticName_4439_);
                    crate::leanh::lean_dec_ref(v_idx_4438_);
                    v___x_4453_ = crate::leanh::lean_box(0);
                    v___x_4454_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4454_, 0, v___x_4453_);
                    return v___x_4454_;
                } else {
                    v_one_4455_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_4456_ = lean_nat_sub(v_i_4445_, v_one_4455_);
                    crate::leanh::lean_dec(v_i_4445_);
                    v___x_4460_ = lean_nat_sub(v_n_4444_, v_n_4456_);
                    v___x_4461_ = lean_nat_sub(v___x_4460_, v_one_4455_);
                    crate::leanh::lean_dec(v___x_4460_);
                    v_arg_4462_ = lean_array_fget_borrowed(v_majorTypeArgs_4437_, v___x_4461_);
                    v___x_4539_ = lean_nat_dec_eq(v___x_4461_, v_idxPos_4441_);
                    if v___x_4539_ == 0 {
                        v___x_4540_ = lean_expr_eqv(v_arg_4462_, v_idx_4438_);
                        if v___x_4540_ == 0 {
                            v___y_4515_ = v___y_4446_;
                            v___y_4516_ = v___y_4447_;
                            v___y_4517_ = v___y_4448_;
                            v___y_4518_ = v___y_4449_;
                            state = 8;
                            continue;
                        } else {
                            v___x_4541_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1_once), _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1);
                            crate::leanh::lean_inc_ref(v_idx_4438_);
                            v___x_4542_ = l_Lean_MessageData_ofExpr(v_idx_4438_);
                            v___x_4543_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4543_, 0, v___x_4541_);
                            crate::leanh::lean_ctor_set(v___x_4543_, 1, v___x_4542_);
                            v___x_4544_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__7), core::ptr::addr_of_mut!(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__7_once), _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__7);
                            v___x_4545_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4545_, 0, v___x_4543_);
                            crate::leanh::lean_ctor_set(v___x_4545_, 1, v___x_4544_);
                            crate::leanh::lean_inc_ref(v_majorType_4443_);
                            v___x_4546_ = l_Lean_indentExpr(v_majorType_4443_);
                            v___x_4547_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4547_, 0, v___x_4545_);
                            crate::leanh::lean_ctor_set(v___x_4547_, 1, v___x_4546_);
                            v___x_4548_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4548_, 0, v___x_4547_);
                            crate::leanh::lean_inc(v_mvarId_4440_);
                            crate::leanh::lean_inc(v_tacticName_4439_);
                            v___x_4549_ = l_Lean_Meta_throwTacticEx___redArg(
                                v_tacticName_4439_,
                                v_mvarId_4440_,
                                v___x_4548_,
                                v___y_4446_,
                                v___y_4447_,
                                v___y_4448_,
                                v___y_4449_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_4549_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_4549_, 1);
                                v___y_4515_ = v___y_4446_;
                                v___y_4516_ = v___y_4447_;
                                v___y_4517_ = v___y_4448_;
                                v___y_4518_ = v___y_4449_;
                                state = 8;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_4461_);
                                v___y_4458_ = v___x_4549_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        v___y_4515_ = v___y_4446_;
                        v___y_4516_ = v___y_4447_;
                        v___y_4517_ = v___y_4448_;
                        v___y_4518_ = v___y_4449_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v___y_4458_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___y_4458_, 1);
                    v_i_4445_ = v_n_4456_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_n_4456_);
                    crate::leanh::lean_dec_ref(v_majorType_4443_);
                    crate::leanh::lean_dec(v_mvarId_4440_);
                    crate::leanh::lean_dec(v_tacticName_4439_);
                    crate::leanh::lean_dec_ref(v_idx_4438_);
                    return v___y_4458_;
                }
            }
            2 => {
                if v___y_4468_ == 0 {
                    crate::leanh::lean_dec(v___x_4461_);
                    v_i_4445_ = v_n_4456_;
                    state = 0;
                    continue;
                } else {
                    v___x_4470_ = l_Lean_Expr_isFVar(v_arg_4462_);
                    if v___x_4470_ == 0 {
                        crate::leanh::lean_dec(v___x_4461_);
                        v_i_4445_ = v_n_4456_;
                        state = 0;
                        continue;
                    } else {
                        v___x_4472_ = l_Lean_Expr_fvarId_x21(v_idx_4438_);
                        v___x_4473_ = l_Lean_FVarId_getDecl___redArg(
                            v___x_4472_,
                            v___y_4467_,
                            v___y_4465_,
                            v___y_4464_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4473_) == 0 {
                            v_a_4474_ = crate::leanh::lean_ctor_get(v___x_4473_, 0);
                            crate::leanh::lean_inc(v_a_4474_);
                            crate::leanh::lean_dec_ref_known(v___x_4473_, 1);
                            v___x_4475_ = l_Lean_Expr_fvarId_x21(v_arg_4462_);
                            v___x_4476_ = l_Lean_localDeclDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__0___redArg(v_a_4474_, v___x_4475_, v___y_4468_, v___y_4466_);
                            v_a_4477_ = crate::leanh::lean_ctor_get(v___x_4476_, 0);
                            v_isSharedCheck_4497_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4476_)) as u8;
                            if v_isSharedCheck_4497_ == 0 {
                                v___x_4479_ = v___x_4476_;
                                v_isShared_4480_ = v_isSharedCheck_4497_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4477_);
                                crate::leanh::lean_dec(v___x_4476_);
                                v___x_4479_ = crate::leanh::lean_box(0);
                                v_isShared_4480_ = v_isSharedCheck_4497_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_4461_);
                            crate::leanh::lean_dec(v_n_4456_);
                            crate::leanh::lean_dec_ref(v_majorType_4443_);
                            crate::leanh::lean_dec(v_mvarId_4440_);
                            crate::leanh::lean_dec(v_tacticName_4439_);
                            crate::leanh::lean_dec_ref(v_idx_4438_);
                            v_a_4498_ = crate::leanh::lean_ctor_get(v___x_4473_, 0);
                            v_isSharedCheck_4505_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4473_)) as u8;
                            if v_isSharedCheck_4505_ == 0 {
                                v___x_4500_ = v___x_4473_;
                                v_isShared_4501_ = v_isSharedCheck_4505_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4498_);
                                crate::leanh::lean_dec(v___x_4473_);
                                v___x_4500_ = crate::leanh::lean_box(0);
                                v_isShared_4501_ = v_isSharedCheck_4505_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                }
            }
            3 => {
                v___x_4481_ = (crate::leanh::lean_unbox(v_a_4477_) as u8);
                crate::leanh::lean_dec(v_a_4477_);
                if v___x_4481_ == 0 {
                    crate::leanh::lean_del_object(v___x_4479_);
                    crate::leanh::lean_dec(v___x_4461_);
                    v_i_4445_ = v_n_4456_;
                    state = 0;
                    continue;
                } else {
                    v___x_4483_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1_once), _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1);
                    crate::leanh::lean_inc_ref(v_idx_4438_);
                    v___x_4484_ = l_Lean_MessageData_ofExpr(v_idx_4438_);
                    v___x_4485_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4485_, 0, v___x_4483_);
                    crate::leanh::lean_ctor_set(v___x_4485_, 1, v___x_4484_);
                    v___x_4486_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__3_once), _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__3);
                    v___x_4487_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4487_, 0, v___x_4485_);
                    crate::leanh::lean_ctor_set(v___x_4487_, 1, v___x_4486_);
                    v___x_4488_ = lean_nat_add(v___x_4461_, v_one_4455_);
                    crate::leanh::lean_dec(v___x_4461_);
                    v___x_4489_ = l_Nat_reprFast(v___x_4488_);
                    if v_isShared_4480_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_4479_, 3);
                        crate::leanh::lean_ctor_set(v___x_4479_, 0, v___x_4489_);
                        v___x_4491_ = v___x_4479_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4496_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4496_, 0, v___x_4489_);
                        v___x_4491_ = v_reuseFailAlloc_4496_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                v___x_4492_ = l_Lean_MessageData_ofFormat(v___x_4491_);
                v___x_4493_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4493_, 0, v___x_4487_);
                crate::leanh::lean_ctor_set(v___x_4493_, 1, v___x_4492_);
                v___x_4494_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4494_, 0, v___x_4493_);
                crate::leanh::lean_inc(v_mvarId_4440_);
                crate::leanh::lean_inc(v_tacticName_4439_);
                v___x_4495_ = l_Lean_Meta_throwTacticEx___redArg(
                    v_tacticName_4439_,
                    v_mvarId_4440_,
                    v___x_4494_,
                    v___y_4467_,
                    v___y_4466_,
                    v___y_4465_,
                    v___y_4464_,
                );
                v___y_4458_ = v___x_4495_;
                state = 1;
                continue;
            }
            5 => {
                if v_isShared_4501_ == 0 {
                    v___x_4503_ = v___x_4500_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4504_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4504_, 0, v_a_4498_);
                    v___x_4503_ = v_reuseFailAlloc_4504_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4503_;
            }
            7 => {
                v___x_4511_ = lean_nat_dec_lt(v_idxPos_4441_, v___x_4461_);
                if v___x_4511_ == 0 {
                    v___y_4464_ = v___y_4510_;
                    v___y_4465_ = v___y_4509_;
                    v___y_4466_ = v___y_4508_;
                    v___y_4467_ = v___y_4507_;
                    v___y_4468_ = v___x_4511_;
                    state = 2;
                    continue;
                } else {
                    v_indicesPos_4512_ = crate::leanh::lean_ctor_get(v_recursorInfo_4442_, 6);
                    v___x_4513_ = l_List_elem___at___00Lean_Meta_getMajorTypeIndices_spec__1(
                        v___x_4461_,
                        v_indicesPos_4512_,
                    );
                    v___y_4464_ = v___y_4510_;
                    v___y_4465_ = v___y_4509_;
                    v___y_4466_ = v___y_4508_;
                    v___y_4467_ = v___y_4507_;
                    v___y_4468_ = v___x_4513_;
                    state = 2;
                    continue;
                }
            }
            8 => {
                v___x_4519_ = lean_nat_dec_lt(v___x_4461_, v_idxPos_4441_);
                if v___x_4519_ == 0 {
                    v___y_4507_ = v___y_4515_;
                    v___y_4508_ = v___y_4516_;
                    v___y_4509_ = v___y_4517_;
                    v___y_4510_ = v___y_4518_;
                    state = 7;
                    continue;
                } else {
                    v___x_4520_ = l_Lean_Expr_fvarId_x21(v_idx_4438_);
                    crate::leanh::lean_inc(v_arg_4462_);
                    v___x_4521_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_arg_4462_, v___x_4520_, v___y_4516_);
                    v_a_4522_ = crate::leanh::lean_ctor_get(v___x_4521_, 0);
                    v_isSharedCheck_4538_ = (!crate::leanh::lean_is_exclusive(v___x_4521_)) as u8;
                    if v_isSharedCheck_4538_ == 0 {
                        v___x_4524_ = v___x_4521_;
                        v_isShared_4525_ = v_isSharedCheck_4538_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4522_);
                        crate::leanh::lean_dec(v___x_4521_);
                        v___x_4524_ = crate::leanh::lean_box(0);
                        v_isShared_4525_ = v_isSharedCheck_4538_;
                        state = 9;
                        continue;
                    }
                }
            }
            9 => {
                v___x_4526_ = (crate::leanh::lean_unbox(v_a_4522_) as u8);
                crate::leanh::lean_dec(v_a_4522_);
                if v___x_4526_ == 0 {
                    crate::leanh::lean_del_object(v___x_4524_);
                    v___y_4507_ = v___y_4515_;
                    v___y_4508_ = v___y_4516_;
                    v___y_4509_ = v___y_4517_;
                    v___y_4510_ = v___y_4518_;
                    state = 7;
                    continue;
                } else {
                    v___x_4527_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1_once), _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__1);
                    crate::leanh::lean_inc_ref(v_idx_4438_);
                    v___x_4528_ = l_Lean_MessageData_ofExpr(v_idx_4438_);
                    v___x_4529_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4529_, 0, v___x_4527_);
                    crate::leanh::lean_ctor_set(v___x_4529_, 1, v___x_4528_);
                    v___x_4530_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__5), core::ptr::addr_of_mut!(l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__5_once), _init_l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___closed__5);
                    v___x_4531_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4531_, 0, v___x_4529_);
                    crate::leanh::lean_ctor_set(v___x_4531_, 1, v___x_4530_);
                    crate::leanh::lean_inc_ref(v_majorType_4443_);
                    v___x_4532_ = l_Lean_indentExpr(v_majorType_4443_);
                    v___x_4533_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4533_, 0, v___x_4531_);
                    crate::leanh::lean_ctor_set(v___x_4533_, 1, v___x_4532_);
                    if v_isShared_4525_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_4524_, 1);
                        crate::leanh::lean_ctor_set(v___x_4524_, 0, v___x_4533_);
                        v___x_4535_ = v___x_4524_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_4537_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4537_, 0, v___x_4533_);
                        v___x_4535_ = v_reuseFailAlloc_4537_;
                        state = 10;
                        continue;
                    }
                }
            }
            10 => {
                crate::leanh::lean_inc(v_mvarId_4440_);
                crate::leanh::lean_inc(v_tacticName_4439_);
                v___x_4536_ = l_Lean_Meta_throwTacticEx___redArg(
                    v_tacticName_4439_,
                    v_mvarId_4440_,
                    v___x_4535_,
                    v___y_4515_,
                    v___y_4516_,
                    v___y_4517_,
                    v___y_4518_,
                );
                if crate::leanh::lean_obj_tag(v___x_4536_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_4536_, 1);
                    v___y_4507_ = v___y_4515_;
                    v___y_4508_ = v___y_4516_;
                    v___y_4509_ = v___y_4517_;
                    v___y_4510_ = v___y_4518_;
                    state = 7;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_4461_);
                    v___y_4458_ = v___x_4536_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg___boxed(
    mut v_majorTypeArgs_4550_: *mut crate::leanh::LeanObject,
    mut v_idx_4551_: *mut crate::leanh::LeanObject,
    mut v_tacticName_4552_: *mut crate::leanh::LeanObject,
    mut v_mvarId_4553_: *mut crate::leanh::LeanObject,
    mut v_idxPos_4554_: *mut crate::leanh::LeanObject,
    mut v_recursorInfo_4555_: *mut crate::leanh::LeanObject,
    mut v_majorType_4556_: *mut crate::leanh::LeanObject,
    mut v_n_4557_: *mut crate::leanh::LeanObject,
    mut v_i_4558_: *mut crate::leanh::LeanObject,
    mut v___y_4559_: *mut crate::leanh::LeanObject,
    mut v___y_4560_: *mut crate::leanh::LeanObject,
    mut v___y_4561_: *mut crate::leanh::LeanObject,
    mut v___y_4562_: *mut crate::leanh::LeanObject,
    mut v___y_4563_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4564_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg(v_majorTypeArgs_4550_, v_idx_4551_, v_tacticName_4552_, v_mvarId_4553_, v_idxPos_4554_, v_recursorInfo_4555_, v_majorType_4556_, v_n_4557_, v_i_4558_, v___y_4559_, v___y_4560_, v___y_4561_, v___y_4562_);
    crate::leanh::lean_dec(v___y_4562_);
    crate::leanh::lean_dec_ref(v___y_4561_);
    crate::leanh::lean_dec(v___y_4560_);
    crate::leanh::lean_dec_ref(v___y_4559_);
    crate::leanh::lean_dec(v_n_4557_);
    crate::leanh::lean_dec_ref(v_recursorInfo_4555_);
    crate::leanh::lean_dec(v_idxPos_4554_);
    crate::leanh::lean_dec_ref(v_majorTypeArgs_4550_);
    return v_res_4564_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4566_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__0;
    v___x_4567_ = l_Lean_stringToMessageData(v___x_4566_);
    return v___x_4567_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4569_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__2;
    v___x_4570_ = l_Lean_stringToMessageData(v___x_4569_);
    return v___x_4570_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4572_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__4;
    v___x_4573_ = l_Lean_stringToMessageData(v___x_4572_);
    return v___x_4573_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4(
    mut v_majorTypeArgs_4574_: *mut crate::leanh::LeanObject,
    mut v_tacticName_4575_: *mut crate::leanh::LeanObject,
    mut v_mvarId_4576_: *mut crate::leanh::LeanObject,
    mut v_recursorInfo_4577_: *mut crate::leanh::LeanObject,
    mut v_majorType_4578_: *mut crate::leanh::LeanObject,
    mut v_sz_4579_: usize,
    mut v_i_4580_: usize,
    mut v_bs_4581_: *mut crate::leanh::LeanObject,
    mut v___y_4582_: *mut crate::leanh::LeanObject,
    mut v___y_4583_: *mut crate::leanh::LeanObject,
    mut v___y_4584_: *mut crate::leanh::LeanObject,
    mut v___y_4585_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4587_: u8 = 0;
    let mut v___x_4588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4594_: usize = 0;
    let mut v___x_4595_: usize = 0;
    let mut v___x_4596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4599_: u8 = 0;
    let mut v_idx_4600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4610_: u8 = 0;
    let mut v___x_4612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4614_: u8 = 0;
    let mut v___x_4615_: u8 = 0;
    let mut v___x_4616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4628_: u8 = 0;
    let mut v___x_4630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4632_: u8 = 0;
    let mut v___x_4633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4642_: u8 = 0;
    let mut v___x_4644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4646_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4587_ = lean_usize_dec_lt(v_i_4580_, v_sz_4579_);
                if v___x_4587_ == 0 {
                    crate::leanh::lean_dec_ref(v_majorType_4578_);
                    crate::leanh::lean_dec(v_mvarId_4576_);
                    crate::leanh::lean_dec(v_tacticName_4575_);
                    v___x_4588_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4588_, 0, v_bs_4581_);
                    return v___x_4588_;
                } else {
                    v_v_4589_ = lean_array_uget(v_bs_4581_, v_i_4580_);
                    v___x_4590_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_4591_ = lean_array_uset(v_bs_4581_, v_i_4580_, v___x_4590_);
                    v___x_4598_ = lean_array_get_size(v_majorTypeArgs_4574_);
                    v___x_4599_ = lean_nat_dec_le(v___x_4598_, v_v_4589_);
                    if v___x_4599_ == 0 {
                        v_idx_4600_ = lean_array_fget_borrowed(v_majorTypeArgs_4574_, v_v_4589_);
                        v___x_4615_ = l_Lean_Expr_isFVar(v_idx_4600_);
                        if v___x_4615_ == 0 {
                            v___x_4616_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__1);
                            crate::leanh::lean_inc(v_idx_4600_);
                            v___x_4617_ = l_Lean_MessageData_ofExpr(v_idx_4600_);
                            v___x_4618_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4618_, 0, v___x_4616_);
                            crate::leanh::lean_ctor_set(v___x_4618_, 1, v___x_4617_);
                            v___x_4619_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__3);
                            v___x_4620_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4620_, 0, v___x_4618_);
                            crate::leanh::lean_ctor_set(v___x_4620_, 1, v___x_4619_);
                            crate::leanh::lean_inc_ref(v_majorType_4578_);
                            v___x_4621_ = l_Lean_indentExpr(v_majorType_4578_);
                            v___x_4622_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4622_, 0, v___x_4620_);
                            crate::leanh::lean_ctor_set(v___x_4622_, 1, v___x_4621_);
                            v___x_4623_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4623_, 0, v___x_4622_);
                            crate::leanh::lean_inc(v_mvarId_4576_);
                            crate::leanh::lean_inc(v_tacticName_4575_);
                            v___x_4624_ = l_Lean_Meta_throwTacticEx___redArg(
                                v_tacticName_4575_,
                                v_mvarId_4576_,
                                v___x_4623_,
                                v___y_4582_,
                                v___y_4583_,
                                v___y_4584_,
                                v___y_4585_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_4624_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_4624_, 1);
                                v___y_4602_ = v___y_4582_;
                                v___y_4603_ = v___y_4583_;
                                v___y_4604_ = v___y_4584_;
                                v___y_4605_ = v___y_4585_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v_bs_x27_4591_);
                                crate::leanh::lean_dec(v_v_4589_);
                                crate::leanh::lean_dec_ref(v_majorType_4578_);
                                crate::leanh::lean_dec(v_mvarId_4576_);
                                crate::leanh::lean_dec(v_tacticName_4575_);
                                v_a_4625_ = crate::leanh::lean_ctor_get(v___x_4624_, 0);
                                v_isSharedCheck_4632_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4624_)) as u8;
                                if v_isSharedCheck_4632_ == 0 {
                                    v___x_4627_ = v___x_4624_;
                                    v_isShared_4628_ = v_isSharedCheck_4632_;
                                    state = 5;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4625_);
                                    crate::leanh::lean_dec(v___x_4624_);
                                    v___x_4627_ = crate::leanh::lean_box(0);
                                    v_isShared_4628_ = v_isSharedCheck_4632_;
                                    state = 5;
                                    continue;
                                }
                            }
                        } else {
                            v___y_4602_ = v___y_4582_;
                            v___y_4603_ = v___y_4583_;
                            v___y_4604_ = v___y_4584_;
                            v___y_4605_ = v___y_4585_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_v_4589_);
                        v___x_4633_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5);
                        crate::leanh::lean_inc_ref(v_majorType_4578_);
                        v___x_4634_ = l_Lean_indentExpr(v_majorType_4578_);
                        v___x_4635_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4635_, 0, v___x_4633_);
                        crate::leanh::lean_ctor_set(v___x_4635_, 1, v___x_4634_);
                        v___x_4636_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4636_, 0, v___x_4635_);
                        crate::leanh::lean_inc(v_mvarId_4576_);
                        crate::leanh::lean_inc(v_tacticName_4575_);
                        v___x_4637_ = l_Lean_Meta_throwTacticEx___redArg(
                            v_tacticName_4575_,
                            v_mvarId_4576_,
                            v___x_4636_,
                            v___y_4582_,
                            v___y_4583_,
                            v___y_4584_,
                            v___y_4585_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4637_) == 0 {
                            v_a_4638_ = crate::leanh::lean_ctor_get(v___x_4637_, 0);
                            crate::leanh::lean_inc(v_a_4638_);
                            crate::leanh::lean_dec_ref_known(v___x_4637_, 1);
                            v_a_4593_ = v_a_4638_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_bs_x27_4591_);
                            crate::leanh::lean_dec_ref(v_majorType_4578_);
                            crate::leanh::lean_dec(v_mvarId_4576_);
                            crate::leanh::lean_dec(v_tacticName_4575_);
                            v_a_4639_ = crate::leanh::lean_ctor_get(v___x_4637_, 0);
                            v_isSharedCheck_4646_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4637_)) as u8;
                            if v_isSharedCheck_4646_ == 0 {
                                v___x_4641_ = v___x_4637_;
                                v_isShared_4642_ = v_isSharedCheck_4646_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4639_);
                                crate::leanh::lean_dec(v___x_4637_);
                                v___x_4641_ = crate::leanh::lean_box(0);
                                v_isShared_4642_ = v_isSharedCheck_4646_;
                                state = 7;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_4594_ = 1usize;
                v___x_4595_ = lean_usize_add(v_i_4580_, v___x_4594_);
                v___x_4596_ = lean_array_uset(v_bs_x27_4591_, v_i_4580_, v_a_4593_);
                v_i_4580_ = v___x_4595_;
                v_bs_4581_ = v___x_4596_;
                state = 0;
                continue;
            }
            2 => {
                crate::leanh::lean_inc_ref(v_majorType_4578_);
                crate::leanh::lean_inc(v_mvarId_4576_);
                crate::leanh::lean_inc(v_tacticName_4575_);
                crate::leanh::lean_inc(v_idx_4600_);
                v___x_4606_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg(v_majorTypeArgs_4574_, v_idx_4600_, v_tacticName_4575_, v_mvarId_4576_, v_v_4589_, v_recursorInfo_4577_, v_majorType_4578_, v___x_4598_, v___x_4598_, v___y_4602_, v___y_4603_, v___y_4604_, v___y_4605_);
                crate::leanh::lean_dec(v_v_4589_);
                if crate::leanh::lean_obj_tag(v___x_4606_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_4606_, 1);
                    crate::leanh::lean_inc(v_idx_4600_);
                    v_a_4593_ = v_idx_4600_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_bs_x27_4591_);
                    crate::leanh::lean_dec_ref(v_majorType_4578_);
                    crate::leanh::lean_dec(v_mvarId_4576_);
                    crate::leanh::lean_dec(v_tacticName_4575_);
                    v_a_4607_ = crate::leanh::lean_ctor_get(v___x_4606_, 0);
                    v_isSharedCheck_4614_ = (!crate::leanh::lean_is_exclusive(v___x_4606_)) as u8;
                    if v_isSharedCheck_4614_ == 0 {
                        v___x_4609_ = v___x_4606_;
                        v_isShared_4610_ = v_isSharedCheck_4614_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4607_);
                        crate::leanh::lean_dec(v___x_4606_);
                        v___x_4609_ = crate::leanh::lean_box(0);
                        v_isShared_4610_ = v_isSharedCheck_4614_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_4610_ == 0 {
                    v___x_4612_ = v___x_4609_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4613_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4613_, 0, v_a_4607_);
                    v___x_4612_ = v_reuseFailAlloc_4613_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4612_;
            }
            5 => {
                if v_isShared_4628_ == 0 {
                    v___x_4630_ = v___x_4627_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4631_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4631_, 0, v_a_4625_);
                    v___x_4630_ = v_reuseFailAlloc_4631_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4630_;
            }
            7 => {
                if v_isShared_4642_ == 0 {
                    v___x_4644_ = v___x_4641_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4645_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4645_, 0, v_a_4639_);
                    v___x_4644_ = v_reuseFailAlloc_4645_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4644_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___boxed(
    mut v_majorTypeArgs_4647_: *mut crate::leanh::LeanObject,
    mut v_tacticName_4648_: *mut crate::leanh::LeanObject,
    mut v_mvarId_4649_: *mut crate::leanh::LeanObject,
    mut v_recursorInfo_4650_: *mut crate::leanh::LeanObject,
    mut v_majorType_4651_: *mut crate::leanh::LeanObject,
    mut v_sz_4652_: *mut crate::leanh::LeanObject,
    mut v_i_4653_: *mut crate::leanh::LeanObject,
    mut v_bs_4654_: *mut crate::leanh::LeanObject,
    mut v___y_4655_: *mut crate::leanh::LeanObject,
    mut v___y_4656_: *mut crate::leanh::LeanObject,
    mut v___y_4657_: *mut crate::leanh::LeanObject,
    mut v___y_4658_: *mut crate::leanh::LeanObject,
    mut v___y_4659_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4660_: usize = 0;
    let mut v_i_boxed_4661_: usize = 0;
    let mut v_res_4662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4660_ = crate::leanh::lean_unbox_usize(v_sz_4652_);
    crate::leanh::lean_dec(v_sz_4652_);
    v_i_boxed_4661_ = crate::leanh::lean_unbox_usize(v_i_4653_);
    crate::leanh::lean_dec(v_i_4653_);
    v_res_4662_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4(v_majorTypeArgs_4647_, v_tacticName_4648_, v_mvarId_4649_, v_recursorInfo_4650_, v_majorType_4651_, v_sz_boxed_4660_, v_i_boxed_4661_, v_bs_4654_, v___y_4655_, v___y_4656_, v___y_4657_, v___y_4658_);
    crate::leanh::lean_dec(v___y_4658_);
    crate::leanh::lean_dec_ref(v___y_4657_);
    crate::leanh::lean_dec(v___y_4656_);
    crate::leanh::lean_dec_ref(v___y_4655_);
    crate::leanh::lean_dec_ref(v_recursorInfo_4650_);
    crate::leanh::lean_dec_ref(v_majorTypeArgs_4647_);
    return v_res_4662_;
}
pub unsafe fn _init_l_Lean_Meta_getMajorTypeIndices___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_4663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_4664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4663_ = crate::leanh::lean_box(0);
    v_dummy_4664_ = l_Lean_Expr_sort___override(v___x_4663_);
    return v_dummy_4664_;
}
pub unsafe fn l_Lean_Meta_getMajorTypeIndices(
    mut v_mvarId_4665_: *mut crate::leanh::LeanObject,
    mut v_tacticName_4666_: *mut crate::leanh::LeanObject,
    mut v_recursorInfo_4667_: *mut crate::leanh::LeanObject,
    mut v_majorType_4668_: *mut crate::leanh::LeanObject,
    mut v_a_4669_: *mut crate::leanh::LeanObject,
    mut v_a_4670_: *mut crate::leanh::LeanObject,
    mut v_a_4671_: *mut crate::leanh::LeanObject,
    mut v_a_4672_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_indicesPos_4674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_4675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_4676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_majorTypeArgs_4680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4682_: usize = 0;
    let mut v___x_4683_: usize = 0;
    let mut v___x_4684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_indicesPos_4674_ = crate::leanh::lean_ctor_get(v_recursorInfo_4667_, 6);
    v_nargs_4675_ = l_Lean_Expr_getAppNumArgs(v_majorType_4668_);
    v_dummy_4676_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_getMajorTypeIndices___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_getMajorTypeIndices___closed__0_once),
        _init_l_Lean_Meta_getMajorTypeIndices___closed__0,
    );
    crate::leanh::lean_inc(v_nargs_4675_);
    v___x_4677_ = lean_mk_array(v_nargs_4675_, v_dummy_4676_);
    v___x_4678_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_4679_ = lean_nat_sub(v_nargs_4675_, v___x_4678_);
    crate::leanh::lean_dec(v_nargs_4675_);
    crate::leanh::lean_inc_ref(v_majorType_4668_);
    v_majorTypeArgs_4680_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
        v_majorType_4668_,
        v___x_4677_,
        v___x_4679_,
    );
    crate::leanh::lean_inc(v_indicesPos_4674_);
    v___x_4681_ = lean_array_mk(v_indicesPos_4674_);
    v_sz_4682_ = lean_array_size(v___x_4681_);
    v___x_4683_ = 0usize;
    v___x_4684_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4(v_majorTypeArgs_4680_, v_tacticName_4666_, v_mvarId_4665_, v_recursorInfo_4667_, v_majorType_4668_, v_sz_4682_, v___x_4683_, v___x_4681_, v_a_4669_, v_a_4670_, v_a_4671_, v_a_4672_);
    crate::leanh::lean_dec_ref(v_recursorInfo_4667_);
    crate::leanh::lean_dec_ref(v_majorTypeArgs_4680_);
    return v___x_4684_;
}
pub unsafe fn l_Lean_Meta_getMajorTypeIndices___boxed(
    mut v_mvarId_4685_: *mut crate::leanh::LeanObject,
    mut v_tacticName_4686_: *mut crate::leanh::LeanObject,
    mut v_recursorInfo_4687_: *mut crate::leanh::LeanObject,
    mut v_majorType_4688_: *mut crate::leanh::LeanObject,
    mut v_a_4689_: *mut crate::leanh::LeanObject,
    mut v_a_4690_: *mut crate::leanh::LeanObject,
    mut v_a_4691_: *mut crate::leanh::LeanObject,
    mut v_a_4692_: *mut crate::leanh::LeanObject,
    mut v_a_4693_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4694_ = l_Lean_Meta_getMajorTypeIndices(
        v_mvarId_4685_,
        v_tacticName_4686_,
        v_recursorInfo_4687_,
        v_majorType_4688_,
        v_a_4689_,
        v_a_4690_,
        v_a_4691_,
        v_a_4692_,
    );
    crate::leanh::lean_dec(v_a_4692_);
    crate::leanh::lean_dec_ref(v_a_4691_);
    crate::leanh::lean_dec(v_a_4690_);
    crate::leanh::lean_dec_ref(v_a_4689_);
    return v_res_4694_;
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3(
    mut v_majorTypeArgs_4695_: *mut crate::leanh::LeanObject,
    mut v_idx_4696_: *mut crate::leanh::LeanObject,
    mut v_tacticName_4697_: *mut crate::leanh::LeanObject,
    mut v_mvarId_4698_: *mut crate::leanh::LeanObject,
    mut v_idxPos_4699_: *mut crate::leanh::LeanObject,
    mut v_recursorInfo_4700_: *mut crate::leanh::LeanObject,
    mut v_majorType_4701_: *mut crate::leanh::LeanObject,
    mut v_n_4702_: *mut crate::leanh::LeanObject,
    mut v_i_4703_: *mut crate::leanh::LeanObject,
    mut v_a_4704_: *mut crate::leanh::LeanObject,
    mut v___y_4705_: *mut crate::leanh::LeanObject,
    mut v___y_4706_: *mut crate::leanh::LeanObject,
    mut v___y_4707_: *mut crate::leanh::LeanObject,
    mut v___y_4708_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4710_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___redArg(v_majorTypeArgs_4695_, v_idx_4696_, v_tacticName_4697_, v_mvarId_4698_, v_idxPos_4699_, v_recursorInfo_4700_, v_majorType_4701_, v_n_4702_, v_i_4703_, v___y_4705_, v___y_4706_, v___y_4707_, v___y_4708_);
    return v___x_4710_;
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3___boxed(
    mut v_majorTypeArgs_4711_: *mut crate::leanh::LeanObject,
    mut v_idx_4712_: *mut crate::leanh::LeanObject,
    mut v_tacticName_4713_: *mut crate::leanh::LeanObject,
    mut v_mvarId_4714_: *mut crate::leanh::LeanObject,
    mut v_idxPos_4715_: *mut crate::leanh::LeanObject,
    mut v_recursorInfo_4716_: *mut crate::leanh::LeanObject,
    mut v_majorType_4717_: *mut crate::leanh::LeanObject,
    mut v_n_4718_: *mut crate::leanh::LeanObject,
    mut v_i_4719_: *mut crate::leanh::LeanObject,
    mut v_a_4720_: *mut crate::leanh::LeanObject,
    mut v___y_4721_: *mut crate::leanh::LeanObject,
    mut v___y_4722_: *mut crate::leanh::LeanObject,
    mut v___y_4723_: *mut crate::leanh::LeanObject,
    mut v___y_4724_: *mut crate::leanh::LeanObject,
    mut v___y_4725_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4726_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_getMajorTypeIndices_spec__3(v_majorTypeArgs_4711_, v_idx_4712_, v_tacticName_4713_, v_mvarId_4714_, v_idxPos_4715_, v_recursorInfo_4716_, v_majorType_4717_, v_n_4718_, v_i_4719_, v_a_4720_, v___y_4721_, v___y_4722_, v___y_4723_, v___y_4724_);
    crate::leanh::lean_dec(v___y_4724_);
    crate::leanh::lean_dec_ref(v___y_4723_);
    crate::leanh::lean_dec(v___y_4722_);
    crate::leanh::lean_dec_ref(v___y_4721_);
    crate::leanh::lean_dec(v_n_4718_);
    crate::leanh::lean_dec_ref(v_recursorInfo_4716_);
    crate::leanh::lean_dec(v_idxPos_4715_);
    crate::leanh::lean_dec_ref(v_majorTypeArgs_4711_);
    return v_res_4726_;
}
pub unsafe fn l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(
    mut v_name_4727_: *mut crate::leanh::LeanObject,
    mut v_msg_4728_: *mut crate::leanh::LeanObject,
    mut v___y_4729_: *mut crate::leanh::LeanObject,
    mut v___y_4730_: *mut crate::leanh::LeanObject,
    mut v___y_4731_: *mut crate::leanh::LeanObject,
    mut v___y_4732_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_4734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_4735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4740_: u8 = 0;
    let mut v___x_4741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4745_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4734_ = crate::leanh::lean_ctor_get(v___y_4731_, 5);
                v_msg_4735_ = l_Lean_MessageData_tagWithErrorName(v_msg_4728_, v_name_4727_);
                v___x_4736_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1_spec__2(v_msg_4735_, v___y_4729_, v___y_4730_, v___y_4731_, v___y_4732_);
                v_a_4737_ = crate::leanh::lean_ctor_get(v___x_4736_, 0);
                v_isSharedCheck_4745_ = (!crate::leanh::lean_is_exclusive(v___x_4736_)) as u8;
                if v_isSharedCheck_4745_ == 0 {
                    v___x_4739_ = v___x_4736_;
                    v_isShared_4740_ = v_isSharedCheck_4745_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_4737_);
                    crate::leanh::lean_dec(v___x_4736_);
                    v___x_4739_ = crate::leanh::lean_box(0);
                    v_isShared_4740_ = v_isSharedCheck_4745_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_4734_);
                v___x_4741_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4741_, 0, v_ref_4734_);
                crate::leanh::lean_ctor_set(v___x_4741_, 1, v_a_4737_);
                if v_isShared_4740_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4739_, 1);
                    crate::leanh::lean_ctor_set(v___x_4739_, 0, v___x_4741_);
                    v___x_4743_ = v___x_4739_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4744_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4744_, 0, v___x_4741_);
                    v___x_4743_ = v_reuseFailAlloc_4744_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4743_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg___boxed(
    mut v_name_4746_: *mut crate::leanh::LeanObject,
    mut v_msg_4747_: *mut crate::leanh::LeanObject,
    mut v___y_4748_: *mut crate::leanh::LeanObject,
    mut v___y_4749_: *mut crate::leanh::LeanObject,
    mut v___y_4750_: *mut crate::leanh::LeanObject,
    mut v___y_4751_: *mut crate::leanh::LeanObject,
    mut v___y_4752_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4753_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(
        v_name_4746_,
        v_msg_4747_,
        v___y_4748_,
        v___y_4749_,
        v___y_4750_,
        v___y_4751_,
    );
    crate::leanh::lean_dec(v___y_4751_);
    crate::leanh::lean_dec_ref(v___y_4750_);
    crate::leanh::lean_dec(v___y_4749_);
    crate::leanh::lean_dec_ref(v___y_4748_);
    return v_res_4753_;
}
pub unsafe fn l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0(
    mut v_a_4754_: *mut crate::leanh::LeanObject,
    mut v___x_4755_: *mut crate::leanh::LeanObject,
    mut v_tacticName_4756_: *mut crate::leanh::LeanObject,
    mut v_mvarId_4757_: *mut crate::leanh::LeanObject,
    mut v_x_4758_: *mut crate::leanh::LeanObject,
    mut v_x_4759_: *mut crate::leanh::LeanObject,
    mut v___y_4760_: *mut crate::leanh::LeanObject,
    mut v___y_4761_: *mut crate::leanh::LeanObject,
    mut v___y_4762_: *mut crate::leanh::LeanObject,
    mut v___y_4763_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4771_: u8 = 0;
    let mut v___x_4772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4773_: u8 = 0;
    let mut v___x_4774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4779_: u8 = 0;
    let mut v_unused_4780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4786_: u8 = 0;
    let mut v_idx_4787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4789_: u8 = 0;
    let mut v___x_4790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4800_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4759_) == 0 {
                    crate::leanh::lean_dec(v_mvarId_4757_);
                    crate::leanh::lean_dec(v_tacticName_4756_);
                    crate::leanh::lean_dec(v_a_4754_);
                    v___x_4765_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4765_, 0, v_x_4758_);
                    return v___x_4765_;
                } else {
                    v_head_4766_ = crate::leanh::lean_ctor_get(v_x_4759_, 0);
                    if crate::leanh::lean_obj_tag(v_head_4766_) == 0 {
                        v_tail_4767_ = crate::leanh::lean_ctor_get(v_x_4759_, 1);
                        v_fst_4768_ = crate::leanh::lean_ctor_get(v_x_4758_, 0);
                        v_isSharedCheck_4779_ = (!crate::leanh::lean_is_exclusive(v_x_4758_)) as u8;
                        if v_isSharedCheck_4779_ == 0 {
                            v_unused_4780_ = crate::leanh::lean_ctor_get(v_x_4758_, 1);
                            crate::leanh::lean_dec(v_unused_4780_);
                            v___x_4770_ = v_x_4758_;
                            v_isShared_4771_ = v_isSharedCheck_4779_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_fst_4768_);
                            crate::leanh::lean_dec(v_x_4758_);
                            v___x_4770_ = crate::leanh::lean_box(0);
                            v_isShared_4771_ = v_isSharedCheck_4779_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_tail_4781_ = crate::leanh::lean_ctor_get(v_x_4759_, 1);
                        v_fst_4782_ = crate::leanh::lean_ctor_get(v_x_4758_, 0);
                        v_snd_4783_ = crate::leanh::lean_ctor_get(v_x_4758_, 1);
                        v_isSharedCheck_4800_ = (!crate::leanh::lean_is_exclusive(v_x_4758_)) as u8;
                        if v_isSharedCheck_4800_ == 0 {
                            v___x_4785_ = v_x_4758_;
                            v_isShared_4786_ = v_isSharedCheck_4800_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_4783_);
                            crate::leanh::lean_inc(v_fst_4782_);
                            crate::leanh::lean_dec(v_x_4758_);
                            v___x_4785_ = crate::leanh::lean_box(0);
                            v_isShared_4786_ = v_isSharedCheck_4800_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_a_4754_);
                v___x_4772_ = lean_array_push(v_fst_4768_, v_a_4754_);
                v___x_4773_ = 1;
                v___x_4774_ = crate::leanh::lean_box((v___x_4773_) as usize);
                if v_isShared_4771_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4770_, 1, v___x_4774_);
                    crate::leanh::lean_ctor_set(v___x_4770_, 0, v___x_4772_);
                    v___x_4776_ = v___x_4770_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4778_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4778_, 0, v___x_4772_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4778_, 1, v___x_4774_);
                    v___x_4776_ = v_reuseFailAlloc_4778_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_x_4758_ = v___x_4776_;
                v_x_4759_ = v_tail_4767_;
                state = 0;
                continue;
            }
            3 => {
                v_idx_4787_ = crate::leanh::lean_ctor_get(v_head_4766_, 0);
                v___x_4788_ = lean_array_get_size(v___x_4755_);
                v___x_4789_ = lean_nat_dec_le(v___x_4788_, v_idx_4787_);
                if v___x_4789_ == 0 {
                    v___x_4790_ = lean_array_fget_borrowed(v___x_4755_, v_idx_4787_);
                    crate::leanh::lean_inc(v___x_4790_);
                    v___x_4791_ = lean_array_push(v_fst_4782_, v___x_4790_);
                    if v_isShared_4786_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4785_, 0, v___x_4791_);
                        v___x_4793_ = v___x_4785_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4795_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4795_, 0, v___x_4791_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4795_, 1, v_snd_4783_);
                        v___x_4793_ = v_reuseFailAlloc_4795_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4785_);
                    crate::leanh::lean_dec(v_snd_4783_);
                    crate::leanh::lean_dec(v_fst_4782_);
                    v___x_4796_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9_once), _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__9);
                    crate::leanh::lean_inc(v_mvarId_4757_);
                    crate::leanh::lean_inc(v_tacticName_4756_);
                    v___x_4797_ = l_Lean_Meta_throwTacticEx___redArg(
                        v_tacticName_4756_,
                        v_mvarId_4757_,
                        v___x_4796_,
                        v___y_4760_,
                        v___y_4761_,
                        v___y_4762_,
                        v___y_4763_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4797_) == 0 {
                        v_a_4798_ = crate::leanh::lean_ctor_get(v___x_4797_, 0);
                        crate::leanh::lean_inc(v_a_4798_);
                        crate::leanh::lean_dec_ref_known(v___x_4797_, 1);
                        v_x_4758_ = v_a_4798_;
                        v_x_4759_ = v_tail_4781_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_mvarId_4757_);
                        crate::leanh::lean_dec(v_tacticName_4756_);
                        crate::leanh::lean_dec(v_a_4754_);
                        return v___x_4797_;
                    }
                }
            }
            4 => {
                v_x_4758_ = v___x_4793_;
                v_x_4759_ = v_tail_4781_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0___boxed(
    mut v_a_4801_: *mut crate::leanh::LeanObject,
    mut v___x_4802_: *mut crate::leanh::LeanObject,
    mut v_tacticName_4803_: *mut crate::leanh::LeanObject,
    mut v_mvarId_4804_: *mut crate::leanh::LeanObject,
    mut v_x_4805_: *mut crate::leanh::LeanObject,
    mut v_x_4806_: *mut crate::leanh::LeanObject,
    mut v___y_4807_: *mut crate::leanh::LeanObject,
    mut v___y_4808_: *mut crate::leanh::LeanObject,
    mut v___y_4809_: *mut crate::leanh::LeanObject,
    mut v___y_4810_: *mut crate::leanh::LeanObject,
    mut v___y_4811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4812_ = l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0(
        v_a_4801_,
        v___x_4802_,
        v_tacticName_4803_,
        v_mvarId_4804_,
        v_x_4805_,
        v_x_4806_,
        v___y_4807_,
        v___y_4808_,
        v___y_4809_,
        v___y_4810_,
    );
    crate::leanh::lean_dec(v___y_4810_);
    crate::leanh::lean_dec_ref(v___y_4809_);
    crate::leanh::lean_dec(v___y_4808_);
    crate::leanh::lean_dec_ref(v___y_4807_);
    crate::leanh::lean_dec(v_x_4806_);
    crate::leanh::lean_dec_ref(v___x_4802_);
    return v_res_4812_;
}
pub unsafe fn _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4828_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__7;
    v___x_4829_ = l_Lean_stringToMessageData(v___x_4828_);
    return v___x_4829_;
}
pub unsafe fn _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4831_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__9;
    v___x_4832_ = l_Lean_stringToMessageData(v___x_4831_);
    return v___x_4832_;
}
pub unsafe fn _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4836_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__12;
    v___x_4837_ = l_Lean_MessageData_ofFormat(v___x_4836_);
    return v___x_4837_;
}
pub unsafe fn _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4838_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__13), core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__13_once), _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__13);
    v___x_4839_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4839_, 0, v___x_4838_);
    return v___x_4839_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2(
    mut v_recursorInfo_4840_: *mut crate::leanh::LeanObject,
    mut v_a_4841_: *mut crate::leanh::LeanObject,
    mut v_tacticName_4842_: *mut crate::leanh::LeanObject,
    mut v_mvarId_4843_: *mut crate::leanh::LeanObject,
    mut v_indices_4844_: *mut crate::leanh::LeanObject,
    mut v_a_4845_: *mut crate::leanh::LeanObject,
    mut v_major_4846_: *mut crate::leanh::LeanObject,
    mut v_x_4847_: *mut crate::leanh::LeanObject,
    mut v_x_4848_: *mut crate::leanh::LeanObject,
    mut v_x_4849_: *mut crate::leanh::LeanObject,
    mut v___y_4850_: *mut crate::leanh::LeanObject,
    mut v___y_4851_: *mut crate::leanh::LeanObject,
    mut v___y_4852_: *mut crate::leanh::LeanObject,
    mut v___y_4853_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fn_4855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_4856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_4861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_recursorName_4862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_univLevelPos_4863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_depElim_4864_: u8 = 0;
    let mut v_paramsPos_4865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4867_: u8 = 0;
    let mut v___y_4869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_motive_4870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4875_: u8 = 0;
    let mut v___x_4876_: u8 = 0;
    let mut v___x_4877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4881_: u8 = 0;
    let mut v___x_4882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4886_: u8 = 0;
    let mut v___x_4887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4894_: u8 = 0;
    let mut v___y_4896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4913_: u8 = 0;
    let mut v___x_4914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4915_: u8 = 0;
    let mut v___x_4916_: u8 = 0;
    let mut v___x_4917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4929_: u8 = 0;
    let mut v___x_4931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4933_: u8 = 0;
    let mut v_reuseFailAlloc_4934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4935_: u8 = 0;
    let mut v_a_4936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4939_: u8 = 0;
    let mut v___x_4941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4943_: u8 = 0;
    let mut v___x_4944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4847_) == 5 {
                    v_fn_4855_ = crate::leanh::lean_ctor_get(v_x_4847_, 0);
                    crate::leanh::lean_inc_ref(v_fn_4855_);
                    v_arg_4856_ = crate::leanh::lean_ctor_get(v_x_4847_, 1);
                    crate::leanh::lean_inc_ref(v_arg_4856_);
                    crate::leanh::lean_dec_ref_known(v_x_4847_, 2);
                    v___x_4857_ = lean_array_set(v_x_4848_, v_x_4849_, v_arg_4856_);
                    v___x_4858_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4859_ = lean_nat_sub(v_x_4849_, v___x_4858_);
                    crate::leanh::lean_dec(v_x_4849_);
                    v_x_4847_ = v_fn_4855_;
                    v_x_4848_ = v___x_4857_;
                    v_x_4849_ = v___x_4859_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_x_4849_);
                    if crate::leanh::lean_obj_tag(v_x_4847_) == 4 {
                        v_us_4861_ = crate::leanh::lean_ctor_get(v_x_4847_, 1);
                        crate::leanh::lean_inc(v_us_4861_);
                        crate::leanh::lean_dec_ref_known(v_x_4847_, 2);
                        v_recursorName_4862_ = crate::leanh::lean_ctor_get(v_recursorInfo_4840_, 0);
                        crate::leanh::lean_inc(v_recursorName_4862_);
                        v_univLevelPos_4863_ = crate::leanh::lean_ctor_get(v_recursorInfo_4840_, 2);
                        crate::leanh::lean_inc(v_univLevelPos_4863_);
                        v_depElim_4864_ = crate::leanh::lean_ctor_get_uint8(
                            v_recursorInfo_4840_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                        );
                        v_paramsPos_4865_ = crate::leanh::lean_ctor_get(v_recursorInfo_4840_, 5);
                        crate::leanh::lean_inc(v_paramsPos_4865_);
                        crate::leanh::lean_dec_ref(v_recursorInfo_4840_);
                        v___x_4866_ = lean_array_mk(v_us_4861_);
                        v___x_4867_ = 0;
                        v___x_4887_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__1;
                        crate::leanh::lean_inc(v_mvarId_4843_);
                        crate::leanh::lean_inc(v_tacticName_4842_);
                        crate::leanh::lean_inc(v_a_4841_);
                        v___x_4888_ = l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0(
                            v_a_4841_,
                            v___x_4866_,
                            v_tacticName_4842_,
                            v_mvarId_4843_,
                            v___x_4887_,
                            v_univLevelPos_4863_,
                            v___y_4850_,
                            v___y_4851_,
                            v___y_4852_,
                            v___y_4853_,
                        );
                        crate::leanh::lean_dec(v_univLevelPos_4863_);
                        crate::leanh::lean_dec_ref(v___x_4866_);
                        if crate::leanh::lean_obj_tag(v___x_4888_) == 0 {
                            v_a_4889_ = crate::leanh::lean_ctor_get(v___x_4888_, 0);
                            crate::leanh::lean_inc(v_a_4889_);
                            crate::leanh::lean_dec_ref_known(v___x_4888_, 1);
                            v_fst_4890_ = crate::leanh::lean_ctor_get(v_a_4889_, 0);
                            v_snd_4891_ = crate::leanh::lean_ctor_get(v_a_4889_, 1);
                            v_isSharedCheck_4935_ =
                                (!crate::leanh::lean_is_exclusive(v_a_4889_)) as u8;
                            if v_isSharedCheck_4935_ == 0 {
                                v___x_4893_ = v_a_4889_;
                                v_isShared_4894_ = v_isSharedCheck_4935_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_snd_4891_);
                                crate::leanh::lean_inc(v_fst_4890_);
                                crate::leanh::lean_dec(v_a_4889_);
                                v___x_4893_ = crate::leanh::lean_box(0);
                                v_isShared_4894_ = v_isSharedCheck_4935_;
                                state = 4;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_paramsPos_4865_);
                            crate::leanh::lean_dec(v_recursorName_4862_);
                            crate::leanh::lean_dec_ref(v_x_4848_);
                            crate::leanh::lean_dec_ref(v_major_4846_);
                            crate::leanh::lean_dec_ref(v_a_4845_);
                            crate::leanh::lean_dec(v_mvarId_4843_);
                            crate::leanh::lean_dec(v_tacticName_4842_);
                            crate::leanh::lean_dec(v_a_4841_);
                            v_a_4936_ = crate::leanh::lean_ctor_get(v___x_4888_, 0);
                            v_isSharedCheck_4943_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4888_)) as u8;
                            if v_isSharedCheck_4943_ == 0 {
                                v___x_4938_ = v___x_4888_;
                                v_isShared_4939_ = v_isSharedCheck_4943_;
                                state = 9;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4936_);
                                crate::leanh::lean_dec(v___x_4888_);
                                v___x_4938_ = crate::leanh::lean_box(0);
                                v_isShared_4939_ = v_isSharedCheck_4943_;
                                state = 9;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_x_4848_);
                        crate::leanh::lean_dec_ref(v_x_4847_);
                        crate::leanh::lean_dec_ref(v_major_4846_);
                        crate::leanh::lean_dec_ref(v_a_4845_);
                        crate::leanh::lean_dec(v_a_4841_);
                        crate::leanh::lean_dec_ref(v_recursorInfo_4840_);
                        v___x_4944_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14), core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14_once), _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14);
                        v___x_4945_ = l_Lean_Meta_throwTacticEx___redArg(
                            v_tacticName_4842_,
                            v_mvarId_4843_,
                            v___x_4944_,
                            v___y_4850_,
                            v___y_4851_,
                            v___y_4852_,
                            v___y_4853_,
                        );
                        return v___x_4945_;
                    }
                }
            }
            1 => {
                v___x_4875_ = 1;
                v___x_4876_ = 1;
                v___x_4877_ = l_Lean_Meta_mkLambdaFVars(
                    v_indices_4844_,
                    v_motive_4870_,
                    v___x_4867_,
                    v___x_4875_,
                    v___x_4867_,
                    v___x_4875_,
                    v___x_4876_,
                    v___y_4871_,
                    v___y_4872_,
                    v___y_4873_,
                    v___y_4874_,
                );
                if crate::leanh::lean_obj_tag(v___x_4877_) == 0 {
                    v_a_4878_ = crate::leanh::lean_ctor_get(v___x_4877_, 0);
                    v_isSharedCheck_4886_ = (!crate::leanh::lean_is_exclusive(v___x_4877_)) as u8;
                    if v_isSharedCheck_4886_ == 0 {
                        v___x_4880_ = v___x_4877_;
                        v_isShared_4881_ = v_isSharedCheck_4886_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4878_);
                        crate::leanh::lean_dec(v___x_4877_);
                        v___x_4880_ = crate::leanh::lean_box(0);
                        v_isShared_4881_ = v_isSharedCheck_4886_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_4869_);
                    return v___x_4877_;
                }
            }
            2 => {
                v___x_4882_ = l_Lean_Expr_app___override(v___y_4869_, v_a_4878_);
                if v_isShared_4881_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4880_, 0, v___x_4882_);
                    v___x_4884_ = v___x_4880_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4885_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4885_, 0, v___x_4882_);
                    v___x_4884_ = v_reuseFailAlloc_4885_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4884_;
            }
            4 => {
                v___x_4915_ = (crate::leanh::lean_unbox(v_snd_4891_) as u8);
                crate::leanh::lean_dec(v_snd_4891_);
                if v___x_4915_ == 0 {
                    v___x_4916_ = l_Lean_Level_isZero(v_a_4841_);
                    crate::leanh::lean_dec(v_a_4841_);
                    if v___x_4916_ == 0 {
                        crate::leanh::lean_dec(v_fst_4890_);
                        crate::leanh::lean_dec(v_paramsPos_4865_);
                        crate::leanh::lean_dec_ref(v_x_4848_);
                        crate::leanh::lean_dec_ref(v_major_4846_);
                        crate::leanh::lean_dec_ref(v_a_4845_);
                        v___x_4917_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__6;
                        v___x_4918_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8), core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8_once), _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8);
                        v___x_4919_ = l_Lean_MessageData_ofName(v_recursorName_4862_);
                        if v_isShared_4894_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_4893_, 7);
                            crate::leanh::lean_ctor_set(v___x_4893_, 1, v___x_4919_);
                            crate::leanh::lean_ctor_set(v___x_4893_, 0, v___x_4918_);
                            v___x_4921_ = v___x_4893_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_4934_ =
                                crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4934_, 0, v___x_4918_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4934_, 1, v___x_4919_);
                            v___x_4921_ = v_reuseFailAlloc_4934_;
                            state = 6;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_4893_);
                        crate::leanh::lean_dec(v_tacticName_4842_);
                        v___y_4896_ = v___y_4850_;
                        v___y_4897_ = v___y_4851_;
                        v___y_4898_ = v___y_4852_;
                        v___y_4899_ = v___y_4853_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4893_);
                    crate::leanh::lean_dec(v_tacticName_4842_);
                    crate::leanh::lean_dec(v_a_4841_);
                    v___y_4896_ = v___y_4850_;
                    v___y_4897_ = v___y_4851_;
                    v___y_4898_ = v___y_4852_;
                    v___y_4899_ = v___y_4853_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4900_ = lean_array_to_list(v_fst_4890_);
                v___x_4901_ = l_Lean_mkConst(v_recursorName_4862_, v___x_4900_);
                v___x_4902_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams(
                    v_mvarId_4843_,
                    v_x_4848_,
                    v_paramsPos_4865_,
                    v___x_4901_,
                    v___y_4896_,
                    v___y_4897_,
                    v___y_4898_,
                    v___y_4899_,
                );
                crate::leanh::lean_dec_ref(v_x_4848_);
                if crate::leanh::lean_obj_tag(v___x_4902_) == 0 {
                    if v_depElim_4864_ == 0 {
                        crate::leanh::lean_dec_ref(v_major_4846_);
                        v_a_4903_ = crate::leanh::lean_ctor_get(v___x_4902_, 0);
                        crate::leanh::lean_inc(v_a_4903_);
                        crate::leanh::lean_dec_ref_known(v___x_4902_, 1);
                        v___y_4869_ = v_a_4903_;
                        v_motive_4870_ = v_a_4845_;
                        v___y_4871_ = v___y_4896_;
                        v___y_4872_ = v___y_4897_;
                        v___y_4873_ = v___y_4898_;
                        v___y_4874_ = v___y_4899_;
                        state = 1;
                        continue;
                    } else {
                        v_a_4904_ = crate::leanh::lean_ctor_get(v___x_4902_, 0);
                        crate::leanh::lean_inc(v_a_4904_);
                        crate::leanh::lean_dec_ref_known(v___x_4902_, 1);
                        crate::leanh::lean_inc(v___y_4899_);
                        crate::leanh::lean_inc_ref(v___y_4898_);
                        crate::leanh::lean_inc(v___y_4897_);
                        crate::leanh::lean_inc_ref(v___y_4896_);
                        crate::leanh::lean_inc_ref(v_major_4846_);
                        v___x_4905_ = lean_infer_type(
                            v_major_4846_,
                            v___y_4896_,
                            v___y_4897_,
                            v___y_4898_,
                            v___y_4899_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4905_) == 0 {
                            v_a_4906_ = crate::leanh::lean_ctor_get(v___x_4905_, 0);
                            crate::leanh::lean_inc(v_a_4906_);
                            crate::leanh::lean_dec_ref_known(v___x_4905_, 1);
                            v___x_4907_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_4908_ = lean_mk_empty_array_with_capacity(v___x_4907_);
                            v___x_4909_ = lean_array_push(v___x_4908_, v_major_4846_);
                            v___x_4910_ = l_Lean_Expr_abstractM(
                                v_a_4845_,
                                v___x_4909_,
                                v___y_4896_,
                                v___y_4897_,
                                v___y_4898_,
                                v___y_4899_,
                            );
                            crate::leanh::lean_dec_ref(v___x_4909_);
                            if crate::leanh::lean_obj_tag(v___x_4910_) == 0 {
                                v_a_4911_ = crate::leanh::lean_ctor_get(v___x_4910_, 0);
                                crate::leanh::lean_inc(v_a_4911_);
                                crate::leanh::lean_dec_ref_known(v___x_4910_, 1);
                                v___x_4912_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__3;
                                v___x_4913_ = 0;
                                v___x_4914_ =
                                    l_Lean_mkLambda(v___x_4912_, v___x_4913_, v_a_4906_, v_a_4911_);
                                v___y_4869_ = v_a_4904_;
                                v_motive_4870_ = v___x_4914_;
                                v___y_4871_ = v___y_4896_;
                                v___y_4872_ = v___y_4897_;
                                v___y_4873_ = v___y_4898_;
                                v___y_4874_ = v___y_4899_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_a_4906_);
                                crate::leanh::lean_dec(v_a_4904_);
                                return v___x_4910_;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_4904_);
                            crate::leanh::lean_dec_ref(v_major_4846_);
                            crate::leanh::lean_dec_ref(v_a_4845_);
                            return v___x_4905_;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_major_4846_);
                    crate::leanh::lean_dec_ref(v_a_4845_);
                    return v___x_4902_;
                }
            }
            6 => {
                v___x_4922_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10), core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10_once), _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10);
                v___x_4923_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4923_, 0, v___x_4921_);
                crate::leanh::lean_ctor_set(v___x_4923_, 1, v___x_4922_);
                v___x_4924_ =
                    l_Lean_Meta_mkTacticExMsg(v_tacticName_4842_, v_mvarId_4843_, v___x_4923_);
                v___x_4925_ =
                    l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(
                        v___x_4917_,
                        v___x_4924_,
                        v___y_4850_,
                        v___y_4851_,
                        v___y_4852_,
                        v___y_4853_,
                    );
                v_a_4926_ = crate::leanh::lean_ctor_get(v___x_4925_, 0);
                v_isSharedCheck_4933_ = (!crate::leanh::lean_is_exclusive(v___x_4925_)) as u8;
                if v_isSharedCheck_4933_ == 0 {
                    v___x_4928_ = v___x_4925_;
                    v_isShared_4929_ = v_isSharedCheck_4933_;
                    state = 7;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_4926_);
                    crate::leanh::lean_dec(v___x_4925_);
                    v___x_4928_ = crate::leanh::lean_box(0);
                    v_isShared_4929_ = v_isSharedCheck_4933_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_4929_ == 0 {
                    v___x_4931_ = v___x_4928_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4932_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4932_, 0, v_a_4926_);
                    v___x_4931_ = v_reuseFailAlloc_4932_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4931_;
            }
            9 => {
                if v_isShared_4939_ == 0 {
                    v___x_4941_ = v___x_4938_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4942_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4942_, 0, v_a_4936_);
                    v___x_4941_ = v_reuseFailAlloc_4942_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4941_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___boxed(
    mut v_recursorInfo_4946_: *mut crate::leanh::LeanObject,
    mut v_a_4947_: *mut crate::leanh::LeanObject,
    mut v_tacticName_4948_: *mut crate::leanh::LeanObject,
    mut v_mvarId_4949_: *mut crate::leanh::LeanObject,
    mut v_indices_4950_: *mut crate::leanh::LeanObject,
    mut v_a_4951_: *mut crate::leanh::LeanObject,
    mut v_major_4952_: *mut crate::leanh::LeanObject,
    mut v_x_4953_: *mut crate::leanh::LeanObject,
    mut v_x_4954_: *mut crate::leanh::LeanObject,
    mut v_x_4955_: *mut crate::leanh::LeanObject,
    mut v___y_4956_: *mut crate::leanh::LeanObject,
    mut v___y_4957_: *mut crate::leanh::LeanObject,
    mut v___y_4958_: *mut crate::leanh::LeanObject,
    mut v___y_4959_: *mut crate::leanh::LeanObject,
    mut v___y_4960_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4961_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2(v_recursorInfo_4946_, v_a_4947_, v_tacticName_4948_, v_mvarId_4949_, v_indices_4950_, v_a_4951_, v_major_4952_, v_x_4953_, v_x_4954_, v_x_4955_, v___y_4956_, v___y_4957_, v___y_4958_, v___y_4959_);
    crate::leanh::lean_dec(v___y_4959_);
    crate::leanh::lean_dec_ref(v___y_4958_);
    crate::leanh::lean_dec(v___y_4957_);
    crate::leanh::lean_dec_ref(v___y_4956_);
    crate::leanh::lean_dec_ref(v_indices_4950_);
    return v_res_4961_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2(
    mut v_a_4962_: *mut crate::leanh::LeanObject,
    mut v_tacticName_4963_: *mut crate::leanh::LeanObject,
    mut v_mvarId_4964_: *mut crate::leanh::LeanObject,
    mut v_recursorInfo_4965_: *mut crate::leanh::LeanObject,
    mut v_indices_4966_: *mut crate::leanh::LeanObject,
    mut v_a_4967_: *mut crate::leanh::LeanObject,
    mut v_major_4968_: *mut crate::leanh::LeanObject,
    mut v_x_4969_: *mut crate::leanh::LeanObject,
    mut v_x_4970_: *mut crate::leanh::LeanObject,
    mut v_x_4971_: *mut crate::leanh::LeanObject,
    mut v___y_4972_: *mut crate::leanh::LeanObject,
    mut v___y_4973_: *mut crate::leanh::LeanObject,
    mut v___y_4974_: *mut crate::leanh::LeanObject,
    mut v___y_4975_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fn_4977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_4978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_4983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_recursorName_4984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_univLevelPos_4985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_depElim_4986_: u8 = 0;
    let mut v_paramsPos_4987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4989_: u8 = 0;
    let mut v___y_4991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_motive_4992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4997_: u8 = 0;
    let mut v___x_4998_: u8 = 0;
    let mut v___x_4999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5003_: u8 = 0;
    let mut v___x_5004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5008_: u8 = 0;
    let mut v___x_5009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5016_: u8 = 0;
    let mut v___y_5018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5035_: u8 = 0;
    let mut v___x_5036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5037_: u8 = 0;
    let mut v___x_5038_: u8 = 0;
    let mut v___x_5039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5051_: u8 = 0;
    let mut v___x_5053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5055_: u8 = 0;
    let mut v_reuseFailAlloc_5056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5057_: u8 = 0;
    let mut v_a_5058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5061_: u8 = 0;
    let mut v___x_5063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5065_: u8 = 0;
    let mut v___x_5066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4969_) == 5 {
                    v_fn_4977_ = crate::leanh::lean_ctor_get(v_x_4969_, 0);
                    crate::leanh::lean_inc_ref(v_fn_4977_);
                    v_arg_4978_ = crate::leanh::lean_ctor_get(v_x_4969_, 1);
                    crate::leanh::lean_inc_ref(v_arg_4978_);
                    crate::leanh::lean_dec_ref_known(v_x_4969_, 2);
                    v___x_4979_ = lean_array_set(v_x_4970_, v_x_4971_, v_arg_4978_);
                    v___x_4980_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4981_ = lean_nat_sub(v_x_4971_, v___x_4980_);
                    v___x_4982_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2(v_recursorInfo_4965_, v_a_4962_, v_tacticName_4963_, v_mvarId_4964_, v_indices_4966_, v_a_4967_, v_major_4968_, v_fn_4977_, v___x_4979_, v___x_4981_, v___y_4972_, v___y_4973_, v___y_4974_, v___y_4975_);
                    return v___x_4982_;
                } else {
                    if crate::leanh::lean_obj_tag(v_x_4969_) == 4 {
                        v_us_4983_ = crate::leanh::lean_ctor_get(v_x_4969_, 1);
                        crate::leanh::lean_inc(v_us_4983_);
                        crate::leanh::lean_dec_ref_known(v_x_4969_, 2);
                        v_recursorName_4984_ = crate::leanh::lean_ctor_get(v_recursorInfo_4965_, 0);
                        crate::leanh::lean_inc(v_recursorName_4984_);
                        v_univLevelPos_4985_ = crate::leanh::lean_ctor_get(v_recursorInfo_4965_, 2);
                        crate::leanh::lean_inc(v_univLevelPos_4985_);
                        v_depElim_4986_ = crate::leanh::lean_ctor_get_uint8(
                            v_recursorInfo_4965_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                        );
                        v_paramsPos_4987_ = crate::leanh::lean_ctor_get(v_recursorInfo_4965_, 5);
                        crate::leanh::lean_inc(v_paramsPos_4987_);
                        crate::leanh::lean_dec_ref(v_recursorInfo_4965_);
                        v___x_4988_ = lean_array_mk(v_us_4983_);
                        v___x_4989_ = 0;
                        v___x_5009_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__1;
                        crate::leanh::lean_inc(v_mvarId_4964_);
                        crate::leanh::lean_inc(v_tacticName_4963_);
                        crate::leanh::lean_inc(v_a_4962_);
                        v___x_5010_ = l_List_foldlM___at___00Lean_Meta_mkRecursorAppPrefix_spec__0(
                            v_a_4962_,
                            v___x_4988_,
                            v_tacticName_4963_,
                            v_mvarId_4964_,
                            v___x_5009_,
                            v_univLevelPos_4985_,
                            v___y_4972_,
                            v___y_4973_,
                            v___y_4974_,
                            v___y_4975_,
                        );
                        crate::leanh::lean_dec(v_univLevelPos_4985_);
                        crate::leanh::lean_dec_ref(v___x_4988_);
                        if crate::leanh::lean_obj_tag(v___x_5010_) == 0 {
                            v_a_5011_ = crate::leanh::lean_ctor_get(v___x_5010_, 0);
                            crate::leanh::lean_inc(v_a_5011_);
                            crate::leanh::lean_dec_ref_known(v___x_5010_, 1);
                            v_fst_5012_ = crate::leanh::lean_ctor_get(v_a_5011_, 0);
                            v_snd_5013_ = crate::leanh::lean_ctor_get(v_a_5011_, 1);
                            v_isSharedCheck_5057_ =
                                (!crate::leanh::lean_is_exclusive(v_a_5011_)) as u8;
                            if v_isSharedCheck_5057_ == 0 {
                                v___x_5015_ = v_a_5011_;
                                v_isShared_5016_ = v_isSharedCheck_5057_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_snd_5013_);
                                crate::leanh::lean_inc(v_fst_5012_);
                                crate::leanh::lean_dec(v_a_5011_);
                                v___x_5015_ = crate::leanh::lean_box(0);
                                v_isShared_5016_ = v_isSharedCheck_5057_;
                                state = 4;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_paramsPos_4987_);
                            crate::leanh::lean_dec(v_recursorName_4984_);
                            crate::leanh::lean_dec_ref(v_x_4970_);
                            crate::leanh::lean_dec_ref(v_major_4968_);
                            crate::leanh::lean_dec_ref(v_a_4967_);
                            crate::leanh::lean_dec(v_mvarId_4964_);
                            crate::leanh::lean_dec(v_tacticName_4963_);
                            crate::leanh::lean_dec(v_a_4962_);
                            v_a_5058_ = crate::leanh::lean_ctor_get(v___x_5010_, 0);
                            v_isSharedCheck_5065_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5010_)) as u8;
                            if v_isSharedCheck_5065_ == 0 {
                                v___x_5060_ = v___x_5010_;
                                v_isShared_5061_ = v_isSharedCheck_5065_;
                                state = 9;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5058_);
                                crate::leanh::lean_dec(v___x_5010_);
                                v___x_5060_ = crate::leanh::lean_box(0);
                                v_isShared_5061_ = v_isSharedCheck_5065_;
                                state = 9;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_x_4970_);
                        crate::leanh::lean_dec_ref(v_x_4969_);
                        crate::leanh::lean_dec_ref(v_major_4968_);
                        crate::leanh::lean_dec_ref(v_a_4967_);
                        crate::leanh::lean_dec_ref(v_recursorInfo_4965_);
                        crate::leanh::lean_dec(v_a_4962_);
                        v___x_5066_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14), core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14_once), _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__14);
                        v___x_5067_ = l_Lean_Meta_throwTacticEx___redArg(
                            v_tacticName_4963_,
                            v_mvarId_4964_,
                            v___x_5066_,
                            v___y_4972_,
                            v___y_4973_,
                            v___y_4974_,
                            v___y_4975_,
                        );
                        return v___x_5067_;
                    }
                }
            }
            1 => {
                v___x_4997_ = 1;
                v___x_4998_ = 1;
                v___x_4999_ = l_Lean_Meta_mkLambdaFVars(
                    v_indices_4966_,
                    v_motive_4992_,
                    v___x_4989_,
                    v___x_4997_,
                    v___x_4989_,
                    v___x_4997_,
                    v___x_4998_,
                    v___y_4993_,
                    v___y_4994_,
                    v___y_4995_,
                    v___y_4996_,
                );
                if crate::leanh::lean_obj_tag(v___x_4999_) == 0 {
                    v_a_5000_ = crate::leanh::lean_ctor_get(v___x_4999_, 0);
                    v_isSharedCheck_5008_ = (!crate::leanh::lean_is_exclusive(v___x_4999_)) as u8;
                    if v_isSharedCheck_5008_ == 0 {
                        v___x_5002_ = v___x_4999_;
                        v_isShared_5003_ = v_isSharedCheck_5008_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5000_);
                        crate::leanh::lean_dec(v___x_4999_);
                        v___x_5002_ = crate::leanh::lean_box(0);
                        v_isShared_5003_ = v_isSharedCheck_5008_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_4991_);
                    return v___x_4999_;
                }
            }
            2 => {
                v___x_5004_ = l_Lean_Expr_app___override(v___y_4991_, v_a_5000_);
                if v_isShared_5003_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5002_, 0, v___x_5004_);
                    v___x_5006_ = v___x_5002_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5007_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5007_, 0, v___x_5004_);
                    v___x_5006_ = v_reuseFailAlloc_5007_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5006_;
            }
            4 => {
                v___x_5037_ = (crate::leanh::lean_unbox(v_snd_5013_) as u8);
                crate::leanh::lean_dec(v_snd_5013_);
                if v___x_5037_ == 0 {
                    v___x_5038_ = l_Lean_Level_isZero(v_a_4962_);
                    crate::leanh::lean_dec(v_a_4962_);
                    if v___x_5038_ == 0 {
                        crate::leanh::lean_dec(v_fst_5012_);
                        crate::leanh::lean_dec(v_paramsPos_4987_);
                        crate::leanh::lean_dec_ref(v_x_4970_);
                        crate::leanh::lean_dec_ref(v_major_4968_);
                        crate::leanh::lean_dec_ref(v_a_4967_);
                        v___x_5039_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__6;
                        v___x_5040_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8), core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8_once), _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__8);
                        v___x_5041_ = l_Lean_MessageData_ofName(v_recursorName_4984_);
                        if v_isShared_5016_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_5015_, 7);
                            crate::leanh::lean_ctor_set(v___x_5015_, 1, v___x_5041_);
                            crate::leanh::lean_ctor_set(v___x_5015_, 0, v___x_5040_);
                            v___x_5043_ = v___x_5015_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_5056_ =
                                crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5056_, 0, v___x_5040_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5056_, 1, v___x_5041_);
                            v___x_5043_ = v_reuseFailAlloc_5056_;
                            state = 6;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_5015_);
                        crate::leanh::lean_dec(v_tacticName_4963_);
                        v___y_5018_ = v___y_4972_;
                        v___y_5019_ = v___y_4973_;
                        v___y_5020_ = v___y_4974_;
                        v___y_5021_ = v___y_4975_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5015_);
                    crate::leanh::lean_dec(v_tacticName_4963_);
                    crate::leanh::lean_dec(v_a_4962_);
                    v___y_5018_ = v___y_4972_;
                    v___y_5019_ = v___y_4973_;
                    v___y_5020_ = v___y_4974_;
                    v___y_5021_ = v___y_4975_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5022_ = lean_array_to_list(v_fst_5012_);
                v___x_5023_ = l_Lean_mkConst(v_recursorName_4984_, v___x_5022_);
                v___x_5024_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams(
                    v_mvarId_4964_,
                    v_x_4970_,
                    v_paramsPos_4987_,
                    v___x_5023_,
                    v___y_5018_,
                    v___y_5019_,
                    v___y_5020_,
                    v___y_5021_,
                );
                crate::leanh::lean_dec_ref(v_x_4970_);
                if crate::leanh::lean_obj_tag(v___x_5024_) == 0 {
                    if v_depElim_4986_ == 0 {
                        crate::leanh::lean_dec_ref(v_major_4968_);
                        v_a_5025_ = crate::leanh::lean_ctor_get(v___x_5024_, 0);
                        crate::leanh::lean_inc(v_a_5025_);
                        crate::leanh::lean_dec_ref_known(v___x_5024_, 1);
                        v___y_4991_ = v_a_5025_;
                        v_motive_4992_ = v_a_4967_;
                        v___y_4993_ = v___y_5018_;
                        v___y_4994_ = v___y_5019_;
                        v___y_4995_ = v___y_5020_;
                        v___y_4996_ = v___y_5021_;
                        state = 1;
                        continue;
                    } else {
                        v_a_5026_ = crate::leanh::lean_ctor_get(v___x_5024_, 0);
                        crate::leanh::lean_inc(v_a_5026_);
                        crate::leanh::lean_dec_ref_known(v___x_5024_, 1);
                        crate::leanh::lean_inc(v___y_5021_);
                        crate::leanh::lean_inc_ref(v___y_5020_);
                        crate::leanh::lean_inc(v___y_5019_);
                        crate::leanh::lean_inc_ref(v___y_5018_);
                        crate::leanh::lean_inc_ref(v_major_4968_);
                        v___x_5027_ = lean_infer_type(
                            v_major_4968_,
                            v___y_5018_,
                            v___y_5019_,
                            v___y_5020_,
                            v___y_5021_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_5027_) == 0 {
                            v_a_5028_ = crate::leanh::lean_ctor_get(v___x_5027_, 0);
                            crate::leanh::lean_inc(v_a_5028_);
                            crate::leanh::lean_dec_ref_known(v___x_5027_, 1);
                            v___x_5029_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_5030_ = lean_mk_empty_array_with_capacity(v___x_5029_);
                            v___x_5031_ = lean_array_push(v___x_5030_, v_major_4968_);
                            v___x_5032_ = l_Lean_Expr_abstractM(
                                v_a_4967_,
                                v___x_5031_,
                                v___y_5018_,
                                v___y_5019_,
                                v___y_5020_,
                                v___y_5021_,
                            );
                            crate::leanh::lean_dec_ref(v___x_5031_);
                            if crate::leanh::lean_obj_tag(v___x_5032_) == 0 {
                                v_a_5033_ = crate::leanh::lean_ctor_get(v___x_5032_, 0);
                                crate::leanh::lean_inc(v_a_5033_);
                                crate::leanh::lean_dec_ref_known(v___x_5032_, 1);
                                v___x_5034_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__3;
                                v___x_5035_ = 0;
                                v___x_5036_ =
                                    l_Lean_mkLambda(v___x_5034_, v___x_5035_, v_a_5028_, v_a_5033_);
                                v___y_4991_ = v_a_5026_;
                                v_motive_4992_ = v___x_5036_;
                                v___y_4993_ = v___y_5018_;
                                v___y_4994_ = v___y_5019_;
                                v___y_4995_ = v___y_5020_;
                                v___y_4996_ = v___y_5021_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_a_5028_);
                                crate::leanh::lean_dec(v_a_5026_);
                                return v___x_5032_;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_5026_);
                            crate::leanh::lean_dec_ref(v_major_4968_);
                            crate::leanh::lean_dec_ref(v_a_4967_);
                            return v___x_5027_;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_major_4968_);
                    crate::leanh::lean_dec_ref(v_a_4967_);
                    return v___x_5024_;
                }
            }
            6 => {
                v___x_5044_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10), core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10_once), _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2_spec__2___closed__10);
                v___x_5045_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5045_, 0, v___x_5043_);
                crate::leanh::lean_ctor_set(v___x_5045_, 1, v___x_5044_);
                v___x_5046_ =
                    l_Lean_Meta_mkTacticExMsg(v_tacticName_4963_, v_mvarId_4964_, v___x_5045_);
                v___x_5047_ =
                    l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(
                        v___x_5039_,
                        v___x_5046_,
                        v___y_4972_,
                        v___y_4973_,
                        v___y_4974_,
                        v___y_4975_,
                    );
                v_a_5048_ = crate::leanh::lean_ctor_get(v___x_5047_, 0);
                v_isSharedCheck_5055_ = (!crate::leanh::lean_is_exclusive(v___x_5047_)) as u8;
                if v_isSharedCheck_5055_ == 0 {
                    v___x_5050_ = v___x_5047_;
                    v_isShared_5051_ = v_isSharedCheck_5055_;
                    state = 7;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_5048_);
                    crate::leanh::lean_dec(v___x_5047_);
                    v___x_5050_ = crate::leanh::lean_box(0);
                    v_isShared_5051_ = v_isSharedCheck_5055_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_5051_ == 0 {
                    v___x_5053_ = v___x_5050_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5054_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5054_, 0, v_a_5048_);
                    v___x_5053_ = v_reuseFailAlloc_5054_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5053_;
            }
            9 => {
                if v_isShared_5061_ == 0 {
                    v___x_5063_ = v___x_5060_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5064_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5064_, 0, v_a_5058_);
                    v___x_5063_ = v_reuseFailAlloc_5064_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5063_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2___boxed(
    mut v_a_5068_: *mut crate::leanh::LeanObject,
    mut v_tacticName_5069_: *mut crate::leanh::LeanObject,
    mut v_mvarId_5070_: *mut crate::leanh::LeanObject,
    mut v_recursorInfo_5071_: *mut crate::leanh::LeanObject,
    mut v_indices_5072_: *mut crate::leanh::LeanObject,
    mut v_a_5073_: *mut crate::leanh::LeanObject,
    mut v_major_5074_: *mut crate::leanh::LeanObject,
    mut v_x_5075_: *mut crate::leanh::LeanObject,
    mut v_x_5076_: *mut crate::leanh::LeanObject,
    mut v_x_5077_: *mut crate::leanh::LeanObject,
    mut v___y_5078_: *mut crate::leanh::LeanObject,
    mut v___y_5079_: *mut crate::leanh::LeanObject,
    mut v___y_5080_: *mut crate::leanh::LeanObject,
    mut v___y_5081_: *mut crate::leanh::LeanObject,
    mut v___y_5082_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5083_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2(
        v_a_5068_,
        v_tacticName_5069_,
        v_mvarId_5070_,
        v_recursorInfo_5071_,
        v_indices_5072_,
        v_a_5073_,
        v_major_5074_,
        v_x_5075_,
        v_x_5076_,
        v_x_5077_,
        v___y_5078_,
        v___y_5079_,
        v___y_5080_,
        v___y_5081_,
    );
    crate::leanh::lean_dec(v___y_5081_);
    crate::leanh::lean_dec_ref(v___y_5080_);
    crate::leanh::lean_dec(v___y_5079_);
    crate::leanh::lean_dec_ref(v___y_5078_);
    crate::leanh::lean_dec(v_x_5077_);
    crate::leanh::lean_dec_ref(v_indices_5072_);
    return v_res_5083_;
}
pub unsafe fn l_Lean_Meta_mkRecursorAppPrefix(
    mut v_mvarId_5084_: *mut crate::leanh::LeanObject,
    mut v_tacticName_5085_: *mut crate::leanh::LeanObject,
    mut v_majorFVarId_5086_: *mut crate::leanh::LeanObject,
    mut v_recursorInfo_5087_: *mut crate::leanh::LeanObject,
    mut v_indices_5088_: *mut crate::leanh::LeanObject,
    mut v_a_5089_: *mut crate::leanh::LeanObject,
    mut v_a_5090_: *mut crate::leanh::LeanObject,
    mut v_a_5091_: *mut crate::leanh::LeanObject,
    mut v_a_5092_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_major_5100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeName_5103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_5108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_5109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5118_: u8 = 0;
    let mut v___x_5120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5122_: u8 = 0;
    let mut v_a_5123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5126_: u8 = 0;
    let mut v___x_5128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5130_: u8 = 0;
    let mut v_a_5131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5134_: u8 = 0;
    let mut v___x_5136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5138_: u8 = 0;
    let mut v_a_5139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5142_: u8 = 0;
    let mut v___x_5144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5146_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_mvarId_5084_);
                v___x_5094_ = l_Lean_MVarId_getType(
                    v_mvarId_5084_,
                    v_a_5089_,
                    v_a_5090_,
                    v_a_5091_,
                    v_a_5092_,
                );
                if crate::leanh::lean_obj_tag(v___x_5094_) == 0 {
                    v_a_5095_ = crate::leanh::lean_ctor_get(v___x_5094_, 0);
                    crate::leanh::lean_inc_n(v_a_5095_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_5094_, 1);
                    v___x_5096_ =
                        l_Lean_Meta_getLevel(v_a_5095_, v_a_5089_, v_a_5090_, v_a_5091_, v_a_5092_);
                    if crate::leanh::lean_obj_tag(v___x_5096_) == 0 {
                        v_a_5097_ = crate::leanh::lean_ctor_get(v___x_5096_, 0);
                        crate::leanh::lean_inc(v_a_5097_);
                        crate::leanh::lean_dec_ref_known(v___x_5096_, 1);
                        v___x_5098_ = l_Lean_Meta_normalizeLevel(
                            v_a_5097_, v_a_5089_, v_a_5090_, v_a_5091_, v_a_5092_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_5098_) == 0 {
                            v_a_5099_ = crate::leanh::lean_ctor_get(v___x_5098_, 0);
                            crate::leanh::lean_inc(v_a_5099_);
                            crate::leanh::lean_dec_ref_known(v___x_5098_, 1);
                            crate::leanh::lean_inc(v_majorFVarId_5086_);
                            v_major_5100_ = l_Lean_mkFVar(v_majorFVarId_5086_);
                            v___x_5101_ = l_Lean_FVarId_getDecl___redArg(
                                v_majorFVarId_5086_,
                                v_a_5089_,
                                v_a_5091_,
                                v_a_5092_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_5101_) == 0 {
                                v_a_5102_ = crate::leanh::lean_ctor_get(v___x_5101_, 0);
                                crate::leanh::lean_inc(v_a_5102_);
                                crate::leanh::lean_dec_ref_known(v___x_5101_, 1);
                                v_typeName_5103_ =
                                    crate::leanh::lean_ctor_get(v_recursorInfo_5087_, 1);
                                v___x_5104_ = l_Lean_LocalDecl_type(v_a_5102_);
                                crate::leanh::lean_dec(v_a_5102_);
                                crate::leanh::lean_inc_ref(v___x_5104_);
                                v___x_5105_ = l_Lean_Meta_whnfUntil(
                                    v___x_5104_,
                                    v_typeName_5103_,
                                    v_a_5089_,
                                    v_a_5090_,
                                    v_a_5091_,
                                    v_a_5092_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_5105_) == 0 {
                                    v_a_5106_ = crate::leanh::lean_ctor_get(v___x_5105_, 0);
                                    crate::leanh::lean_inc(v_a_5106_);
                                    crate::leanh::lean_dec_ref_known(v___x_5105_, 1);
                                    if crate::leanh::lean_obj_tag(v_a_5106_) == 1 {
                                        crate::leanh::lean_dec_ref(v___x_5104_);
                                        v_val_5107_ = crate::leanh::lean_ctor_get(v_a_5106_, 0);
                                        crate::leanh::lean_inc(v_val_5107_);
                                        crate::leanh::lean_dec_ref_known(v_a_5106_, 1);
                                        v_dummy_5108_ = crate::leanh::lean_obj_once(
                                            core::ptr::addr_of_mut!(
                                                l_Lean_Meta_getMajorTypeIndices___closed__0
                                            ),
                                            core::ptr::addr_of_mut!(
                                                l_Lean_Meta_getMajorTypeIndices___closed__0_once
                                            ),
                                            _init_l_Lean_Meta_getMajorTypeIndices___closed__0,
                                        );
                                        v_nargs_5109_ = l_Lean_Expr_getAppNumArgs(v_val_5107_);
                                        crate::leanh::lean_inc(v_nargs_5109_);
                                        v___x_5110_ = lean_mk_array(v_nargs_5109_, v_dummy_5108_);
                                        v___x_5111_ = crate::leanh::lean_unsigned_to_nat(1);
                                        v___x_5112_ = lean_nat_sub(v_nargs_5109_, v___x_5111_);
                                        crate::leanh::lean_dec(v_nargs_5109_);
                                        v___x_5113_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_mkRecursorAppPrefix_spec__2(v_a_5099_, v_tacticName_5085_, v_mvarId_5084_, v_recursorInfo_5087_, v_indices_5088_, v_a_5095_, v_major_5100_, v_val_5107_, v___x_5110_, v___x_5112_, v_a_5089_, v_a_5090_, v_a_5091_, v_a_5092_);
                                        crate::leanh::lean_dec(v___x_5112_);
                                        return v___x_5113_;
                                    } else {
                                        crate::leanh::lean_dec(v_a_5106_);
                                        crate::leanh::lean_dec_ref(v_major_5100_);
                                        crate::leanh::lean_dec(v_a_5099_);
                                        crate::leanh::lean_dec(v_a_5095_);
                                        crate::leanh::lean_dec_ref(v_recursorInfo_5087_);
                                        v___x_5114_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(v_tacticName_5085_, v_mvarId_5084_, v___x_5104_, v_a_5089_, v_a_5090_, v_a_5091_, v_a_5092_);
                                        return v___x_5114_;
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v___x_5104_);
                                    crate::leanh::lean_dec_ref(v_major_5100_);
                                    crate::leanh::lean_dec(v_a_5099_);
                                    crate::leanh::lean_dec(v_a_5095_);
                                    crate::leanh::lean_dec_ref(v_recursorInfo_5087_);
                                    crate::leanh::lean_dec(v_tacticName_5085_);
                                    crate::leanh::lean_dec(v_mvarId_5084_);
                                    v_a_5115_ = crate::leanh::lean_ctor_get(v___x_5105_, 0);
                                    v_isSharedCheck_5122_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_5105_)) as u8;
                                    if v_isSharedCheck_5122_ == 0 {
                                        v___x_5117_ = v___x_5105_;
                                        v_isShared_5118_ = v_isSharedCheck_5122_;
                                        state = 1;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_5115_);
                                        crate::leanh::lean_dec(v___x_5105_);
                                        v___x_5117_ = crate::leanh::lean_box(0);
                                        v_isShared_5118_ = v_isSharedCheck_5122_;
                                        state = 1;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v_major_5100_);
                                crate::leanh::lean_dec(v_a_5099_);
                                crate::leanh::lean_dec(v_a_5095_);
                                crate::leanh::lean_dec_ref(v_recursorInfo_5087_);
                                crate::leanh::lean_dec(v_tacticName_5085_);
                                crate::leanh::lean_dec(v_mvarId_5084_);
                                v_a_5123_ = crate::leanh::lean_ctor_get(v___x_5101_, 0);
                                v_isSharedCheck_5130_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5101_)) as u8;
                                if v_isSharedCheck_5130_ == 0 {
                                    v___x_5125_ = v___x_5101_;
                                    v_isShared_5126_ = v_isSharedCheck_5130_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5123_);
                                    crate::leanh::lean_dec(v___x_5101_);
                                    v___x_5125_ = crate::leanh::lean_box(0);
                                    v_isShared_5126_ = v_isSharedCheck_5130_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_5095_);
                            crate::leanh::lean_dec_ref(v_recursorInfo_5087_);
                            crate::leanh::lean_dec(v_majorFVarId_5086_);
                            crate::leanh::lean_dec(v_tacticName_5085_);
                            crate::leanh::lean_dec(v_mvarId_5084_);
                            v_a_5131_ = crate::leanh::lean_ctor_get(v___x_5098_, 0);
                            v_isSharedCheck_5138_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5098_)) as u8;
                            if v_isSharedCheck_5138_ == 0 {
                                v___x_5133_ = v___x_5098_;
                                v_isShared_5134_ = v_isSharedCheck_5138_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5131_);
                                crate::leanh::lean_dec(v___x_5098_);
                                v___x_5133_ = crate::leanh::lean_box(0);
                                v_isShared_5134_ = v_isSharedCheck_5138_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_5095_);
                        crate::leanh::lean_dec_ref(v_recursorInfo_5087_);
                        crate::leanh::lean_dec(v_majorFVarId_5086_);
                        crate::leanh::lean_dec(v_tacticName_5085_);
                        crate::leanh::lean_dec(v_mvarId_5084_);
                        v_a_5139_ = crate::leanh::lean_ctor_get(v___x_5096_, 0);
                        v_isSharedCheck_5146_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5096_)) as u8;
                        if v_isSharedCheck_5146_ == 0 {
                            v___x_5141_ = v___x_5096_;
                            v_isShared_5142_ = v_isSharedCheck_5146_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5139_);
                            crate::leanh::lean_dec(v___x_5096_);
                            v___x_5141_ = crate::leanh::lean_box(0);
                            v_isShared_5142_ = v_isSharedCheck_5146_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_recursorInfo_5087_);
                    crate::leanh::lean_dec(v_majorFVarId_5086_);
                    crate::leanh::lean_dec(v_tacticName_5085_);
                    crate::leanh::lean_dec(v_mvarId_5084_);
                    return v___x_5094_;
                }
            }
            1 => {
                if v_isShared_5118_ == 0 {
                    v___x_5120_ = v___x_5117_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5121_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5121_, 0, v_a_5115_);
                    v___x_5120_ = v_reuseFailAlloc_5121_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5120_;
            }
            3 => {
                if v_isShared_5126_ == 0 {
                    v___x_5128_ = v___x_5125_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5129_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5129_, 0, v_a_5123_);
                    v___x_5128_ = v_reuseFailAlloc_5129_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5128_;
            }
            5 => {
                if v_isShared_5134_ == 0 {
                    v___x_5136_ = v___x_5133_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5137_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5137_, 0, v_a_5131_);
                    v___x_5136_ = v_reuseFailAlloc_5137_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5136_;
            }
            7 => {
                if v_isShared_5142_ == 0 {
                    v___x_5144_ = v___x_5141_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5145_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5145_, 0, v_a_5139_);
                    v___x_5144_ = v_reuseFailAlloc_5145_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5144_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_mkRecursorAppPrefix___boxed(
    mut v_mvarId_5147_: *mut crate::leanh::LeanObject,
    mut v_tacticName_5148_: *mut crate::leanh::LeanObject,
    mut v_majorFVarId_5149_: *mut crate::leanh::LeanObject,
    mut v_recursorInfo_5150_: *mut crate::leanh::LeanObject,
    mut v_indices_5151_: *mut crate::leanh::LeanObject,
    mut v_a_5152_: *mut crate::leanh::LeanObject,
    mut v_a_5153_: *mut crate::leanh::LeanObject,
    mut v_a_5154_: *mut crate::leanh::LeanObject,
    mut v_a_5155_: *mut crate::leanh::LeanObject,
    mut v_a_5156_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5157_ = l_Lean_Meta_mkRecursorAppPrefix(
        v_mvarId_5147_,
        v_tacticName_5148_,
        v_majorFVarId_5149_,
        v_recursorInfo_5150_,
        v_indices_5151_,
        v_a_5152_,
        v_a_5153_,
        v_a_5154_,
        v_a_5155_,
    );
    crate::leanh::lean_dec(v_a_5155_);
    crate::leanh::lean_dec_ref(v_a_5154_);
    crate::leanh::lean_dec(v_a_5153_);
    crate::leanh::lean_dec_ref(v_a_5152_);
    crate::leanh::lean_dec_ref(v_indices_5151_);
    return v_res_5157_;
}
pub unsafe fn l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1(
    mut v_00_u03b1_5158_: *mut crate::leanh::LeanObject,
    mut v_name_5159_: *mut crate::leanh::LeanObject,
    mut v_msg_5160_: *mut crate::leanh::LeanObject,
    mut v___y_5161_: *mut crate::leanh::LeanObject,
    mut v___y_5162_: *mut crate::leanh::LeanObject,
    mut v___y_5163_: *mut crate::leanh::LeanObject,
    mut v___y_5164_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5166_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___redArg(
        v_name_5159_,
        v_msg_5160_,
        v___y_5161_,
        v___y_5162_,
        v___y_5163_,
        v___y_5164_,
    );
    return v___x_5166_;
}
pub unsafe fn l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1___boxed(
    mut v_00_u03b1_5167_: *mut crate::leanh::LeanObject,
    mut v_name_5168_: *mut crate::leanh::LeanObject,
    mut v_msg_5169_: *mut crate::leanh::LeanObject,
    mut v___y_5170_: *mut crate::leanh::LeanObject,
    mut v___y_5171_: *mut crate::leanh::LeanObject,
    mut v___y_5172_: *mut crate::leanh::LeanObject,
    mut v___y_5173_: *mut crate::leanh::LeanObject,
    mut v___y_5174_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5175_ = l_Lean_throwNamedError___at___00Lean_Meta_mkRecursorAppPrefix_spec__1(
        v_00_u03b1_5167_,
        v_name_5168_,
        v_msg_5169_,
        v___y_5170_,
        v___y_5171_,
        v___y_5172_,
        v___y_5173_,
    );
    crate::leanh::lean_dec(v___y_5173_);
    crate::leanh::lean_dec_ref(v___y_5172_);
    crate::leanh::lean_dec(v___y_5171_);
    crate::leanh::lean_dec_ref(v___y_5170_);
    return v_res_5175_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(
    mut v_mvarId_5176_: *mut crate::leanh::LeanObject,
    mut v_x_5177_: *mut crate::leanh::LeanObject,
    mut v___y_5178_: *mut crate::leanh::LeanObject,
    mut v___y_5179_: *mut crate::leanh::LeanObject,
    mut v___y_5180_: *mut crate::leanh::LeanObject,
    mut v___y_5181_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5187_: u8 = 0;
    let mut v___x_5189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5191_: u8 = 0;
    let mut v_a_5192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5195_: u8 = 0;
    let mut v___x_5197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5199_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5183_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    crate::leanh::lean_box(0),
                    v_mvarId_5176_,
                    v_x_5177_,
                    v___y_5178_,
                    v___y_5179_,
                    v___y_5180_,
                    v___y_5181_,
                );
                if crate::leanh::lean_obj_tag(v___x_5183_) == 0 {
                    v_a_5184_ = crate::leanh::lean_ctor_get(v___x_5183_, 0);
                    v_isSharedCheck_5191_ = (!crate::leanh::lean_is_exclusive(v___x_5183_)) as u8;
                    if v_isSharedCheck_5191_ == 0 {
                        v___x_5186_ = v___x_5183_;
                        v_isShared_5187_ = v_isSharedCheck_5191_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5184_);
                        crate::leanh::lean_dec(v___x_5183_);
                        v___x_5186_ = crate::leanh::lean_box(0);
                        v_isShared_5187_ = v_isSharedCheck_5191_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5192_ = crate::leanh::lean_ctor_get(v___x_5183_, 0);
                    v_isSharedCheck_5199_ = (!crate::leanh::lean_is_exclusive(v___x_5183_)) as u8;
                    if v_isSharedCheck_5199_ == 0 {
                        v___x_5194_ = v___x_5183_;
                        v_isShared_5195_ = v_isSharedCheck_5199_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5192_);
                        crate::leanh::lean_dec(v___x_5183_);
                        v___x_5194_ = crate::leanh::lean_box(0);
                        v_isShared_5195_ = v_isSharedCheck_5199_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5187_ == 0 {
                    v___x_5189_ = v___x_5186_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5190_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5190_, 0, v_a_5184_);
                    v___x_5189_ = v_reuseFailAlloc_5190_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5189_;
            }
            3 => {
                if v_isShared_5195_ == 0 {
                    v___x_5197_ = v___x_5194_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5198_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5198_, 0, v_a_5192_);
                    v___x_5197_ = v_reuseFailAlloc_5198_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5197_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg___boxed(
    mut v_mvarId_5200_: *mut crate::leanh::LeanObject,
    mut v_x_5201_: *mut crate::leanh::LeanObject,
    mut v___y_5202_: *mut crate::leanh::LeanObject,
    mut v___y_5203_: *mut crate::leanh::LeanObject,
    mut v___y_5204_: *mut crate::leanh::LeanObject,
    mut v___y_5205_: *mut crate::leanh::LeanObject,
    mut v___y_5206_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5207_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(
        v_mvarId_5200_,
        v_x_5201_,
        v___y_5202_,
        v___y_5203_,
        v___y_5204_,
        v___y_5205_,
    );
    crate::leanh::lean_dec(v___y_5205_);
    crate::leanh::lean_dec_ref(v___y_5204_);
    crate::leanh::lean_dec(v___y_5203_);
    crate::leanh::lean_dec_ref(v___y_5202_);
    return v_res_5207_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3(
    mut v_00_u03b1_5208_: *mut crate::leanh::LeanObject,
    mut v_mvarId_5209_: *mut crate::leanh::LeanObject,
    mut v_x_5210_: *mut crate::leanh::LeanObject,
    mut v___y_5211_: *mut crate::leanh::LeanObject,
    mut v___y_5212_: *mut crate::leanh::LeanObject,
    mut v___y_5213_: *mut crate::leanh::LeanObject,
    mut v___y_5214_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5216_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(
        v_mvarId_5209_,
        v_x_5210_,
        v___y_5211_,
        v___y_5212_,
        v___y_5213_,
        v___y_5214_,
    );
    return v___x_5216_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___boxed(
    mut v_00_u03b1_5217_: *mut crate::leanh::LeanObject,
    mut v_mvarId_5218_: *mut crate::leanh::LeanObject,
    mut v_x_5219_: *mut crate::leanh::LeanObject,
    mut v___y_5220_: *mut crate::leanh::LeanObject,
    mut v___y_5221_: *mut crate::leanh::LeanObject,
    mut v___y_5222_: *mut crate::leanh::LeanObject,
    mut v___y_5223_: *mut crate::leanh::LeanObject,
    mut v___y_5224_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5225_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3(
        v_00_u03b1_5217_,
        v_mvarId_5218_,
        v_x_5219_,
        v___y_5220_,
        v___y_5221_,
        v___y_5222_,
        v___y_5223_,
    );
    crate::leanh::lean_dec(v___y_5223_);
    crate::leanh::lean_dec_ref(v___y_5222_);
    crate::leanh::lean_dec(v___y_5221_);
    crate::leanh::lean_dec_ref(v___y_5220_);
    return v_res_5225_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2(
    mut v_fst_5226_: *mut crate::leanh::LeanObject,
    mut v_as_5227_: *mut crate::leanh::LeanObject,
    mut v_sz_5228_: usize,
    mut v_i_5229_: usize,
    mut v_b_5230_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5231_: u8 = 0;
    let mut v_fst_5232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5236_: u8 = 0;
    let mut v___x_5237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5247_: usize = 0;
    let mut v___x_5248_: usize = 0;
    let mut v_reuseFailAlloc_5250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5251_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5231_ = lean_usize_dec_lt(v_i_5229_, v_sz_5228_);
                if v___x_5231_ == 0 {
                    return v_b_5230_;
                } else {
                    v_fst_5232_ = crate::leanh::lean_ctor_get(v_b_5230_, 0);
                    v_snd_5233_ = crate::leanh::lean_ctor_get(v_b_5230_, 1);
                    v_isSharedCheck_5251_ = (!crate::leanh::lean_is_exclusive(v_b_5230_)) as u8;
                    if v_isSharedCheck_5251_ == 0 {
                        v___x_5235_ = v_b_5230_;
                        v_isShared_5236_ = v_isSharedCheck_5251_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_5233_);
                        crate::leanh::lean_inc(v_fst_5232_);
                        crate::leanh::lean_dec(v_b_5230_);
                        v___x_5235_ = crate::leanh::lean_box(0);
                        v_isShared_5236_ = v_isSharedCheck_5251_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5237_ = crate::leanh::lean_box(0);
                v_a_5238_ = lean_array_uget_borrowed(v_as_5227_, v_i_5229_);
                v___x_5239_ = l_Lean_Expr_fvarId_x21(v_a_5238_);
                v___x_5240_ = lean_array_get_borrowed(v___x_5237_, v_fst_5226_, v_snd_5233_);
                crate::leanh::lean_inc(v___x_5240_);
                v___x_5241_ = l_Lean_mkFVar(v___x_5240_);
                v___x_5242_ = l_Lean_Meta_FVarSubst_insert(v_fst_5232_, v___x_5239_, v___x_5241_);
                v___x_5243_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_5244_ = lean_nat_add(v_snd_5233_, v___x_5243_);
                crate::leanh::lean_dec(v_snd_5233_);
                if v_isShared_5236_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5235_, 1, v___x_5244_);
                    crate::leanh::lean_ctor_set(v___x_5235_, 0, v___x_5242_);
                    v___x_5246_ = v___x_5235_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5250_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5250_, 0, v___x_5242_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5250_, 1, v___x_5244_);
                    v___x_5246_ = v_reuseFailAlloc_5250_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5247_ = 1usize;
                v___x_5248_ = lean_usize_add(v_i_5229_, v___x_5247_);
                v_i_5229_ = v___x_5248_;
                v_b_5230_ = v___x_5246_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2___boxed(
    mut v_fst_5252_: *mut crate::leanh::LeanObject,
    mut v_as_5253_: *mut crate::leanh::LeanObject,
    mut v_sz_5254_: *mut crate::leanh::LeanObject,
    mut v_i_5255_: *mut crate::leanh::LeanObject,
    mut v_b_5256_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5257_: usize = 0;
    let mut v_i_boxed_5258_: usize = 0;
    let mut v_res_5259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5257_ = crate::leanh::lean_unbox_usize(v_sz_5254_);
    crate::leanh::lean_dec(v_sz_5254_);
    v_i_boxed_5258_ = crate::leanh::lean_unbox_usize(v_i_5255_);
    crate::leanh::lean_dec(v_i_5255_);
    v_res_5259_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2(v_fst_5252_, v_as_5253_, v_sz_boxed_5257_, v_i_boxed_5258_, v_b_5256_);
    crate::leanh::lean_dec_ref(v_as_5253_);
    crate::leanh::lean_dec_ref(v_fst_5252_);
    return v_res_5259_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0(
    mut v_snd_5260_: *mut crate::leanh::LeanObject,
    mut v___x_5261_: *mut crate::leanh::LeanObject,
    mut v_fst_5262_: *mut crate::leanh::LeanObject,
    mut v_a_5263_: *mut crate::leanh::LeanObject,
    mut v___x_5264_: *mut crate::leanh::LeanObject,
    mut v_givenNames_5265_: *mut crate::leanh::LeanObject,
    mut v_fst_5266_: *mut crate::leanh::LeanObject,
    mut v___x_5267_: *mut crate::leanh::LeanObject,
    mut v_fst_5268_: *mut crate::leanh::LeanObject,
    mut v___y_5269_: *mut crate::leanh::LeanObject,
    mut v___y_5270_: *mut crate::leanh::LeanObject,
    mut v___y_5271_: *mut crate::leanh::LeanObject,
    mut v___y_5272_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5280_: u8 = 0;
    let mut v___x_5282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5284_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_a_5263_);
                crate::leanh::lean_inc(v_snd_5260_);
                v___x_5274_ = l_Lean_Meta_mkRecursorAppPrefix(
                    v_snd_5260_,
                    v___x_5261_,
                    v_fst_5262_,
                    v_a_5263_,
                    v___x_5264_,
                    v___y_5269_,
                    v___y_5270_,
                    v___y_5271_,
                    v___y_5272_,
                );
                if crate::leanh::lean_obj_tag(v___x_5274_) == 0 {
                    v_a_5275_ = crate::leanh::lean_ctor_get(v___x_5274_, 0);
                    crate::leanh::lean_inc(v_a_5275_);
                    crate::leanh::lean_dec_ref_known(v___x_5274_, 1);
                    v___x_5276_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize(
                        v_snd_5260_,
                        v_givenNames_5265_,
                        v_a_5263_,
                        v_fst_5266_,
                        v___x_5267_,
                        v___x_5264_,
                        v_fst_5268_,
                        v_a_5275_,
                        v___y_5269_,
                        v___y_5270_,
                        v___y_5271_,
                        v___y_5272_,
                    );
                    crate::leanh::lean_dec_ref(v_a_5263_);
                    return v___x_5276_;
                } else {
                    crate::leanh::lean_dec(v_fst_5268_);
                    crate::leanh::lean_dec_ref(v___x_5267_);
                    crate::leanh::lean_dec_ref(v_a_5263_);
                    crate::leanh::lean_dec(v_snd_5260_);
                    v_a_5277_ = crate::leanh::lean_ctor_get(v___x_5274_, 0);
                    v_isSharedCheck_5284_ = (!crate::leanh::lean_is_exclusive(v___x_5274_)) as u8;
                    if v_isSharedCheck_5284_ == 0 {
                        v___x_5279_ = v___x_5274_;
                        v_isShared_5280_ = v_isSharedCheck_5284_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5277_);
                        crate::leanh::lean_dec(v___x_5274_);
                        v___x_5279_ = crate::leanh::lean_box(0);
                        v_isShared_5280_ = v_isSharedCheck_5284_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5280_ == 0 {
                    v___x_5282_ = v___x_5279_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5283_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5283_, 0, v_a_5277_);
                    v___x_5282_ = v_reuseFailAlloc_5283_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5282_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0___boxed(
    mut v_snd_5285_: *mut crate::leanh::LeanObject,
    mut v___x_5286_: *mut crate::leanh::LeanObject,
    mut v_fst_5287_: *mut crate::leanh::LeanObject,
    mut v_a_5288_: *mut crate::leanh::LeanObject,
    mut v___x_5289_: *mut crate::leanh::LeanObject,
    mut v_givenNames_5290_: *mut crate::leanh::LeanObject,
    mut v_fst_5291_: *mut crate::leanh::LeanObject,
    mut v___x_5292_: *mut crate::leanh::LeanObject,
    mut v_fst_5293_: *mut crate::leanh::LeanObject,
    mut v___y_5294_: *mut crate::leanh::LeanObject,
    mut v___y_5295_: *mut crate::leanh::LeanObject,
    mut v___y_5296_: *mut crate::leanh::LeanObject,
    mut v___y_5297_: *mut crate::leanh::LeanObject,
    mut v___y_5298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5299_ = l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0(
        v_snd_5285_,
        v___x_5286_,
        v_fst_5287_,
        v_a_5288_,
        v___x_5289_,
        v_givenNames_5290_,
        v_fst_5291_,
        v___x_5292_,
        v_fst_5293_,
        v___y_5294_,
        v___y_5295_,
        v___y_5296_,
        v___y_5297_,
    );
    crate::leanh::lean_dec(v___y_5297_);
    crate::leanh::lean_dec_ref(v___y_5296_);
    crate::leanh::lean_dec(v___y_5295_);
    crate::leanh::lean_dec_ref(v___y_5294_);
    crate::leanh::lean_dec_ref(v_fst_5291_);
    crate::leanh::lean_dec_ref(v_givenNames_5290_);
    crate::leanh::lean_dec_ref(v___x_5289_);
    return v_res_5299_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1(
    mut v_sz_5300_: usize,
    mut v_i_5301_: usize,
    mut v_bs_5302_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5303_: u8 = 0;
    let mut v_v_5304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5308_: usize = 0;
    let mut v___x_5309_: usize = 0;
    let mut v___x_5310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5303_ = lean_usize_dec_lt(v_i_5301_, v_sz_5300_);
                if v___x_5303_ == 0 {
                    return v_bs_5302_;
                } else {
                    v_v_5304_ = lean_array_uget(v_bs_5302_, v_i_5301_);
                    v___x_5305_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_5306_ = lean_array_uset(v_bs_5302_, v_i_5301_, v___x_5305_);
                    v___x_5307_ = l_Lean_Expr_fvarId_x21(v_v_5304_);
                    crate::leanh::lean_dec(v_v_5304_);
                    v___x_5308_ = 1usize;
                    v___x_5309_ = lean_usize_add(v_i_5301_, v___x_5308_);
                    v___x_5310_ = lean_array_uset(v_bs_x27_5306_, v_i_5301_, v___x_5307_);
                    v_i_5301_ = v___x_5309_;
                    v_bs_5302_ = v___x_5310_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1___boxed(
    mut v_sz_5312_: *mut crate::leanh::LeanObject,
    mut v_i_5313_: *mut crate::leanh::LeanObject,
    mut v_bs_5314_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5315_: usize = 0;
    let mut v_i_boxed_5316_: usize = 0;
    let mut v_res_5317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5315_ = crate::leanh::lean_unbox_usize(v_sz_5312_);
    crate::leanh::lean_dec(v_sz_5312_);
    v_i_boxed_5316_ = crate::leanh::lean_unbox_usize(v_i_5313_);
    crate::leanh::lean_dec(v_i_5313_);
    v_res_5317_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1(v_sz_boxed_5315_, v_i_boxed_5316_, v_bs_5314_);
    return v_res_5317_;
}
pub unsafe fn l_List_forM___at___00Lean_MVarId_induction_spec__0(
    mut v_majorTypeArgs_5318_: *mut crate::leanh::LeanObject,
    mut v_val_5319_: *mut crate::leanh::LeanObject,
    mut v_mvarId_5320_: *mut crate::leanh::LeanObject,
    mut v_as_5321_: *mut crate::leanh::LeanObject,
    mut v___y_5322_: *mut crate::leanh::LeanObject,
    mut v___y_5323_: *mut crate::leanh::LeanObject,
    mut v___y_5324_: *mut crate::leanh::LeanObject,
    mut v___y_5325_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_5329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5335_: u8 = 0;
    let mut v_val_5336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5339_: u8 = 0;
    let mut v___x_5340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5341_: u8 = 0;
    let mut v___x_5343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5354_: u8 = 0;
    let mut v_isSharedCheck_5355_: u8 = 0;
    let mut v_unused_5356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_5321_) == 0 {
                    crate::leanh::lean_dec(v_mvarId_5320_);
                    crate::leanh::lean_dec_ref(v_val_5319_);
                    v___x_5327_ = crate::leanh::lean_box(0);
                    v___x_5328_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5328_, 0, v___x_5327_);
                    return v___x_5328_;
                } else {
                    v_head_5329_ = crate::leanh::lean_ctor_get(v_as_5321_, 0);
                    crate::leanh::lean_inc(v_head_5329_);
                    if crate::leanh::lean_obj_tag(v_head_5329_) == 0 {
                        v_tail_5330_ = crate::leanh::lean_ctor_get(v_as_5321_, 1);
                        crate::leanh::lean_inc(v_tail_5330_);
                        crate::leanh::lean_dec_ref_known(v_as_5321_, 2);
                        v_as_5321_ = v_tail_5330_;
                        state = 0;
                        continue;
                    } else {
                        v_tail_5332_ = crate::leanh::lean_ctor_get(v_as_5321_, 1);
                        v_isSharedCheck_5355_ =
                            (!crate::leanh::lean_is_exclusive(v_as_5321_)) as u8;
                        if v_isSharedCheck_5355_ == 0 {
                            v_unused_5356_ = crate::leanh::lean_ctor_get(v_as_5321_, 0);
                            crate::leanh::lean_dec(v_unused_5356_);
                            v___x_5334_ = v_as_5321_;
                            v_isShared_5335_ = v_isSharedCheck_5355_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_tail_5332_);
                            crate::leanh::lean_dec(v_as_5321_);
                            v___x_5334_ = crate::leanh::lean_box(0);
                            v_isShared_5335_ = v_isSharedCheck_5355_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_val_5336_ = crate::leanh::lean_ctor_get(v_head_5329_, 0);
                v_isSharedCheck_5354_ = (!crate::leanh::lean_is_exclusive(v_head_5329_)) as u8;
                if v_isSharedCheck_5354_ == 0 {
                    v___x_5338_ = v_head_5329_;
                    v_isShared_5339_ = v_isSharedCheck_5354_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_val_5336_);
                    crate::leanh::lean_dec(v_head_5329_);
                    v___x_5338_ = crate::leanh::lean_box(0);
                    v_isShared_5339_ = v_isSharedCheck_5354_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5340_ = lean_array_get_size(v_majorTypeArgs_5318_);
                v___x_5341_ = lean_nat_dec_le(v___x_5340_, v_val_5336_);
                crate::leanh::lean_dec(v_val_5336_);
                if v___x_5341_ == 0 {
                    crate::leanh::lean_del_object(v___x_5338_);
                    crate::leanh::lean_del_object(v___x_5334_);
                    v_as_5321_ = v_tail_5332_;
                    state = 0;
                    continue;
                } else {
                    v___x_5343_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1;
                    v___x_5344_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_getMajorTypeIndices_spec__4___closed__5);
                    crate::leanh::lean_inc_ref(v_val_5319_);
                    v___x_5345_ = l_Lean_indentExpr(v_val_5319_);
                    if v_isShared_5335_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_5334_, 7);
                        crate::leanh::lean_ctor_set(v___x_5334_, 1, v___x_5345_);
                        crate::leanh::lean_ctor_set(v___x_5334_, 0, v___x_5344_);
                        v___x_5347_ = v___x_5334_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5353_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5353_, 0, v___x_5344_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5353_, 1, v___x_5345_);
                        v___x_5347_ = v_reuseFailAlloc_5353_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_5339_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5338_, 0, v___x_5347_);
                    v___x_5349_ = v___x_5338_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5352_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5352_, 0, v___x_5347_);
                    v___x_5349_ = v_reuseFailAlloc_5352_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                crate::leanh::lean_inc(v_mvarId_5320_);
                v___x_5350_ = l_Lean_Meta_throwTacticEx___redArg(
                    v___x_5343_,
                    v_mvarId_5320_,
                    v___x_5349_,
                    v___y_5322_,
                    v___y_5323_,
                    v___y_5324_,
                    v___y_5325_,
                );
                if crate::leanh::lean_obj_tag(v___x_5350_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_5350_, 1);
                    v_as_5321_ = v_tail_5332_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_tail_5332_);
                    crate::leanh::lean_dec(v_mvarId_5320_);
                    crate::leanh::lean_dec_ref(v_val_5319_);
                    return v___x_5350_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forM___at___00Lean_MVarId_induction_spec__0___boxed(
    mut v_majorTypeArgs_5357_: *mut crate::leanh::LeanObject,
    mut v_val_5358_: *mut crate::leanh::LeanObject,
    mut v_mvarId_5359_: *mut crate::leanh::LeanObject,
    mut v_as_5360_: *mut crate::leanh::LeanObject,
    mut v___y_5361_: *mut crate::leanh::LeanObject,
    mut v___y_5362_: *mut crate::leanh::LeanObject,
    mut v___y_5363_: *mut crate::leanh::LeanObject,
    mut v___y_5364_: *mut crate::leanh::LeanObject,
    mut v___y_5365_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5366_ = l_List_forM___at___00Lean_MVarId_induction_spec__0(
        v_majorTypeArgs_5357_,
        v_val_5358_,
        v_mvarId_5359_,
        v_as_5360_,
        v___y_5361_,
        v___y_5362_,
        v___y_5363_,
        v___y_5364_,
    );
    crate::leanh::lean_dec(v___y_5364_);
    crate::leanh::lean_dec_ref(v___y_5363_);
    crate::leanh::lean_dec(v___y_5362_);
    crate::leanh::lean_dec_ref(v___y_5361_);
    crate::leanh::lean_dec_ref(v_majorTypeArgs_5357_);
    return v_res_5366_;
}
pub unsafe fn _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5368_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__0;
    v___x_5369_ = l_Lean_stringToMessageData(v___x_5368_);
    return v___x_5369_;
}
pub unsafe fn _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5371_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__2;
    v___x_5372_ = l_Lean_stringToMessageData(v___x_5371_);
    return v___x_5372_;
}
pub unsafe fn _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5374_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__4;
    v___x_5375_ = l_Lean_stringToMessageData(v___x_5374_);
    return v___x_5375_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4(
    mut v_a_5376_: *mut crate::leanh::LeanObject,
    mut v_val_5377_: *mut crate::leanh::LeanObject,
    mut v_mvarId_5378_: *mut crate::leanh::LeanObject,
    mut v_majorFVarId_5379_: *mut crate::leanh::LeanObject,
    mut v_givenNames_5380_: *mut crate::leanh::LeanObject,
    mut v_recursorName_5381_: *mut crate::leanh::LeanObject,
    mut v_x_5382_: *mut crate::leanh::LeanObject,
    mut v_x_5383_: *mut crate::leanh::LeanObject,
    mut v_x_5384_: *mut crate::leanh::LeanObject,
    mut v___y_5385_: *mut crate::leanh::LeanObject,
    mut v___y_5386_: *mut crate::leanh::LeanObject,
    mut v___y_5387_: *mut crate::leanh::LeanObject,
    mut v___y_5388_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fn_5390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_5391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_depElim_5396_: u8 = 0;
    let mut v_paramsPos_5397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5407_: usize = 0;
    let mut v___y_5408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5413_: usize = 0;
    let mut v___x_5414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cls_5421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5427_: usize = 0;
    let mut v___x_5428_: usize = 0;
    let mut v___x_5429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5431_: u8 = 0;
    let mut v___x_5432_: u8 = 0;
    let mut v___x_5433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5449_: u8 = 0;
    let mut v___x_5450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_5457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_5458_: u8 = 0;
    let mut v_fst_5459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5463_: u8 = 0;
    let mut v_inheritedTraceOptions_5464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5466_: u8 = 0;
    let mut v___x_5467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5475_: u8 = 0;
    let mut v___x_5477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5479_: u8 = 0;
    let mut v_reuseFailAlloc_5480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5481_: u8 = 0;
    let mut v_unused_5482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5484_: u8 = 0;
    let mut v_a_5485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5488_: u8 = 0;
    let mut v___x_5490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5492_: u8 = 0;
    let mut v_a_5493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5496_: u8 = 0;
    let mut v___x_5498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5500_: u8 = 0;
    let mut v_a_5501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5504_: u8 = 0;
    let mut v___x_5506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5508_: u8 = 0;
    let mut v___x_5509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5513_: u8 = 0;
    let mut v___x_5514_: u8 = 0;
    let mut v___x_5515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5526_: u8 = 0;
    let mut v___x_5528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5530_: u8 = 0;
    let mut v_reuseFailAlloc_5531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5532_: u8 = 0;
    let mut v_a_5533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5536_: u8 = 0;
    let mut v___x_5538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5540_: u8 = 0;
    let mut v_a_5541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5544_: u8 = 0;
    let mut v___x_5546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5548_: u8 = 0;
    let mut v_a_5549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5552_: u8 = 0;
    let mut v___x_5554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5556_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5382_) == 5 {
                    v_fn_5390_ = crate::leanh::lean_ctor_get(v_x_5382_, 0);
                    crate::leanh::lean_inc_ref(v_fn_5390_);
                    v_arg_5391_ = crate::leanh::lean_ctor_get(v_x_5382_, 1);
                    crate::leanh::lean_inc_ref(v_arg_5391_);
                    crate::leanh::lean_dec_ref_known(v_x_5382_, 2);
                    v___x_5392_ = lean_array_set(v_x_5383_, v_x_5384_, v_arg_5391_);
                    v___x_5393_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_5394_ = lean_nat_sub(v_x_5384_, v___x_5393_);
                    crate::leanh::lean_dec(v_x_5384_);
                    v_x_5382_ = v_fn_5390_;
                    v_x_5383_ = v___x_5392_;
                    v_x_5384_ = v___x_5394_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_x_5384_);
                    crate::leanh::lean_dec_ref(v_x_5382_);
                    v_depElim_5396_ = crate::leanh::lean_ctor_get_uint8(
                        v_a_5376_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                    );
                    v_paramsPos_5397_ = crate::leanh::lean_ctor_get(v_a_5376_, 5);
                    crate::leanh::lean_inc(v_paramsPos_5397_);
                    crate::leanh::lean_inc(v_mvarId_5378_);
                    crate::leanh::lean_inc_ref(v_val_5377_);
                    v___x_5398_ = l_List_forM___at___00Lean_MVarId_induction_spec__0(
                        v_x_5383_,
                        v_val_5377_,
                        v_mvarId_5378_,
                        v_paramsPos_5397_,
                        v___y_5385_,
                        v___y_5386_,
                        v___y_5387_,
                        v___y_5388_,
                    );
                    crate::leanh::lean_dec_ref(v_x_5383_);
                    if crate::leanh::lean_obj_tag(v___x_5398_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_5398_, 1);
                        v___x_5399_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1;
                        crate::leanh::lean_inc_ref(v_a_5376_);
                        crate::leanh::lean_inc(v_mvarId_5378_);
                        v___x_5417_ = l_Lean_Meta_getMajorTypeIndices(
                            v_mvarId_5378_,
                            v___x_5399_,
                            v_a_5376_,
                            v_val_5377_,
                            v___y_5385_,
                            v___y_5386_,
                            v___y_5387_,
                            v___y_5388_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_5417_) == 0 {
                            v_a_5418_ = crate::leanh::lean_ctor_get(v___x_5417_, 0);
                            crate::leanh::lean_inc(v_a_5418_);
                            crate::leanh::lean_dec_ref_known(v___x_5417_, 1);
                            crate::leanh::lean_inc(v_mvarId_5378_);
                            v___x_5419_ = l_Lean_MVarId_getType(
                                v_mvarId_5378_,
                                v___y_5385_,
                                v___y_5386_,
                                v___y_5387_,
                                v___y_5388_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_5419_) == 0 {
                                v_a_5420_ = crate::leanh::lean_ctor_get(v___x_5419_, 0);
                                crate::leanh::lean_inc(v_a_5420_);
                                crate::leanh::lean_dec_ref_known(v___x_5419_, 1);
                                v_cls_5421_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2;
                                if v_depElim_5396_ == 0 {
                                    crate::leanh::lean_inc(v_majorFVarId_5379_);
                                    v___x_5509_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_a_5420_, v_majorFVarId_5379_, v___y_5386_);
                                    v_a_5510_ = crate::leanh::lean_ctor_get(v___x_5509_, 0);
                                    v_isSharedCheck_5532_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_5509_)) as u8;
                                    if v_isSharedCheck_5532_ == 0 {
                                        v___x_5512_ = v___x_5509_;
                                        v_isShared_5513_ = v_isSharedCheck_5532_;
                                        state = 15;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_5510_);
                                        crate::leanh::lean_dec(v___x_5509_);
                                        v___x_5512_ = crate::leanh::lean_box(0);
                                        v_isShared_5513_ = v_isSharedCheck_5532_;
                                        state = 15;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_5420_);
                                    crate::leanh::lean_dec(v_recursorName_5381_);
                                    v___y_5423_ = v___y_5385_;
                                    v___y_5424_ = v___y_5386_;
                                    v___y_5425_ = v___y_5387_;
                                    v___y_5426_ = v___y_5388_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_5418_);
                                crate::leanh::lean_dec(v_recursorName_5381_);
                                crate::leanh::lean_dec_ref(v_givenNames_5380_);
                                crate::leanh::lean_dec(v_majorFVarId_5379_);
                                crate::leanh::lean_dec(v_mvarId_5378_);
                                crate::leanh::lean_dec_ref(v_a_5376_);
                                v_a_5533_ = crate::leanh::lean_ctor_get(v___x_5419_, 0);
                                v_isSharedCheck_5540_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5419_)) as u8;
                                if v_isSharedCheck_5540_ == 0 {
                                    v___x_5535_ = v___x_5419_;
                                    v_isShared_5536_ = v_isSharedCheck_5540_;
                                    state = 19;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5533_);
                                    crate::leanh::lean_dec(v___x_5419_);
                                    v___x_5535_ = crate::leanh::lean_box(0);
                                    v_isShared_5536_ = v_isSharedCheck_5540_;
                                    state = 19;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_recursorName_5381_);
                            crate::leanh::lean_dec_ref(v_givenNames_5380_);
                            crate::leanh::lean_dec(v_majorFVarId_5379_);
                            crate::leanh::lean_dec(v_mvarId_5378_);
                            crate::leanh::lean_dec_ref(v_a_5376_);
                            v_a_5541_ = crate::leanh::lean_ctor_get(v___x_5417_, 0);
                            v_isSharedCheck_5548_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5417_)) as u8;
                            if v_isSharedCheck_5548_ == 0 {
                                v___x_5543_ = v___x_5417_;
                                v_isShared_5544_ = v_isSharedCheck_5548_;
                                state = 21;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5541_);
                                crate::leanh::lean_dec(v___x_5417_);
                                v___x_5543_ = crate::leanh::lean_box(0);
                                v_isShared_5544_ = v_isSharedCheck_5548_;
                                state = 21;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_recursorName_5381_);
                        crate::leanh::lean_dec_ref(v_givenNames_5380_);
                        crate::leanh::lean_dec(v_majorFVarId_5379_);
                        crate::leanh::lean_dec(v_mvarId_5378_);
                        crate::leanh::lean_dec_ref(v_val_5377_);
                        crate::leanh::lean_dec_ref(v_a_5376_);
                        v_a_5549_ = crate::leanh::lean_ctor_get(v___x_5398_, 0);
                        v_isSharedCheck_5556_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5398_)) as u8;
                        if v_isSharedCheck_5556_ == 0 {
                            v___x_5551_ = v___x_5398_;
                            v_isShared_5552_ = v_isSharedCheck_5556_;
                            state = 23;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5549_);
                            crate::leanh::lean_dec(v___x_5398_);
                            v___x_5551_ = crate::leanh::lean_box(0);
                            v_isShared_5552_ = v_isSharedCheck_5556_;
                            state = 23;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_sz_5413_ = lean_array_size(v___y_5408_);
                v___x_5414_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(v_sz_5413_, v___y_5407_, v___y_5408_);
                v___f_5415_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0___boxed
                        as *mut core::ffi::c_void,
                    14,
                    9,
                );
                crate::leanh::lean_closure_set(v___f_5415_, 0, v___y_5403_);
                crate::leanh::lean_closure_set(v___f_5415_, 1, v___x_5399_);
                crate::leanh::lean_closure_set(v___f_5415_, 2, v___y_5402_);
                crate::leanh::lean_closure_set(v___f_5415_, 3, v_a_5376_);
                crate::leanh::lean_closure_set(v___f_5415_, 4, v___x_5414_);
                crate::leanh::lean_closure_set(v___f_5415_, 5, v_givenNames_5380_);
                crate::leanh::lean_closure_set(v___f_5415_, 6, v___y_5405_);
                crate::leanh::lean_closure_set(v___f_5415_, 7, v___y_5404_);
                crate::leanh::lean_closure_set(v___f_5415_, 8, v___y_5401_);
                v___x_5416_ =
                    l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(
                        v___y_5406_,
                        v___f_5415_,
                        v___y_5409_,
                        v___y_5410_,
                        v___y_5411_,
                        v___y_5412_,
                    );
                return v___x_5416_;
            }
            2 => {
                v_sz_5427_ = lean_array_size(v_a_5418_);
                v___x_5428_ = 0usize;
                crate::leanh::lean_inc(v_a_5418_);
                v___x_5429_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1(v_sz_5427_, v___x_5428_, v_a_5418_);
                crate::leanh::lean_inc(v_majorFVarId_5379_);
                v___x_5430_ = lean_array_push(v___x_5429_, v_majorFVarId_5379_);
                v___x_5431_ = 1;
                v___x_5432_ = 0;
                v___x_5433_ = l_Lean_MVarId_revert(
                    v_mvarId_5378_,
                    v___x_5430_,
                    v___x_5431_,
                    v___x_5432_,
                    v___y_5423_,
                    v___y_5424_,
                    v___y_5425_,
                    v___y_5426_,
                );
                if crate::leanh::lean_obj_tag(v___x_5433_) == 0 {
                    v_a_5434_ = crate::leanh::lean_ctor_get(v___x_5433_, 0);
                    crate::leanh::lean_inc(v_a_5434_);
                    crate::leanh::lean_dec_ref_known(v___x_5433_, 1);
                    v_fst_5435_ = crate::leanh::lean_ctor_get(v_a_5434_, 0);
                    crate::leanh::lean_inc(v_fst_5435_);
                    v_snd_5436_ = crate::leanh::lean_ctor_get(v_a_5434_, 1);
                    crate::leanh::lean_inc(v_snd_5436_);
                    crate::leanh::lean_dec(v_a_5434_);
                    v___x_5437_ = lean_array_get_size(v_a_5418_);
                    v___x_5438_ = crate::leanh::lean_box(0);
                    v___x_5439_ = l_Lean_Meta_introNCore(
                        v_snd_5436_,
                        v___x_5437_,
                        v___x_5438_,
                        v___x_5432_,
                        v___x_5431_,
                        v___y_5423_,
                        v___y_5424_,
                        v___y_5425_,
                        v___y_5426_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5439_) == 0 {
                        v_a_5440_ = crate::leanh::lean_ctor_get(v___x_5439_, 0);
                        crate::leanh::lean_inc(v_a_5440_);
                        crate::leanh::lean_dec_ref_known(v___x_5439_, 1);
                        v_fst_5441_ = crate::leanh::lean_ctor_get(v_a_5440_, 0);
                        crate::leanh::lean_inc(v_fst_5441_);
                        v_snd_5442_ = crate::leanh::lean_ctor_get(v_a_5440_, 1);
                        crate::leanh::lean_inc(v_snd_5442_);
                        crate::leanh::lean_dec(v_a_5440_);
                        v___x_5443_ = l_Lean_Meta_intro1Core(
                            v_snd_5442_,
                            v___x_5431_,
                            v___y_5423_,
                            v___y_5424_,
                            v___y_5425_,
                            v___y_5426_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_5443_) == 0 {
                            v_a_5444_ = crate::leanh::lean_ctor_get(v___x_5443_, 0);
                            crate::leanh::lean_inc(v_a_5444_);
                            crate::leanh::lean_dec_ref_known(v___x_5443_, 1);
                            v_fst_5445_ = crate::leanh::lean_ctor_get(v_a_5444_, 0);
                            v_snd_5446_ = crate::leanh::lean_ctor_get(v_a_5444_, 1);
                            v_isSharedCheck_5484_ =
                                (!crate::leanh::lean_is_exclusive(v_a_5444_)) as u8;
                            if v_isSharedCheck_5484_ == 0 {
                                v___x_5448_ = v_a_5444_;
                                v_isShared_5449_ = v_isSharedCheck_5484_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_snd_5446_);
                                crate::leanh::lean_inc(v_fst_5445_);
                                crate::leanh::lean_dec(v_a_5444_);
                                v___x_5448_ = crate::leanh::lean_box(0);
                                v_isShared_5449_ = v_isSharedCheck_5484_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_fst_5441_);
                            crate::leanh::lean_dec(v_fst_5435_);
                            crate::leanh::lean_dec(v_a_5418_);
                            crate::leanh::lean_dec_ref(v_givenNames_5380_);
                            crate::leanh::lean_dec(v_majorFVarId_5379_);
                            crate::leanh::lean_dec_ref(v_a_5376_);
                            v_a_5485_ = crate::leanh::lean_ctor_get(v___x_5443_, 0);
                            v_isSharedCheck_5492_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5443_)) as u8;
                            if v_isSharedCheck_5492_ == 0 {
                                v___x_5487_ = v___x_5443_;
                                v_isShared_5488_ = v_isSharedCheck_5492_;
                                state = 9;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5485_);
                                crate::leanh::lean_dec(v___x_5443_);
                                v___x_5487_ = crate::leanh::lean_box(0);
                                v_isShared_5488_ = v_isSharedCheck_5492_;
                                state = 9;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_fst_5435_);
                        crate::leanh::lean_dec(v_a_5418_);
                        crate::leanh::lean_dec_ref(v_givenNames_5380_);
                        crate::leanh::lean_dec(v_majorFVarId_5379_);
                        crate::leanh::lean_dec_ref(v_a_5376_);
                        v_a_5493_ = crate::leanh::lean_ctor_get(v___x_5439_, 0);
                        v_isSharedCheck_5500_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5439_)) as u8;
                        if v_isSharedCheck_5500_ == 0 {
                            v___x_5495_ = v___x_5439_;
                            v_isShared_5496_ = v_isSharedCheck_5500_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5493_);
                            crate::leanh::lean_dec(v___x_5439_);
                            v___x_5495_ = crate::leanh::lean_box(0);
                            v_isShared_5496_ = v_isSharedCheck_5500_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_5418_);
                    crate::leanh::lean_dec_ref(v_givenNames_5380_);
                    crate::leanh::lean_dec(v_majorFVarId_5379_);
                    crate::leanh::lean_dec_ref(v_a_5376_);
                    v_a_5501_ = crate::leanh::lean_ctor_get(v___x_5433_, 0);
                    v_isSharedCheck_5508_ = (!crate::leanh::lean_is_exclusive(v___x_5433_)) as u8;
                    if v_isSharedCheck_5508_ == 0 {
                        v___x_5503_ = v___x_5433_;
                        v_isShared_5504_ = v_isSharedCheck_5508_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5501_);
                        crate::leanh::lean_dec(v___x_5433_);
                        v___x_5503_ = crate::leanh::lean_box(0);
                        v_isShared_5504_ = v_isSharedCheck_5508_;
                        state = 13;
                        continue;
                    }
                }
            }
            3 => {
                v___x_5450_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v_fst_5445_);
                v___x_5451_ = l_Lean_mkFVar(v_fst_5445_);
                crate::leanh::lean_inc_ref(v___x_5451_);
                v___x_5452_ =
                    l_Lean_Meta_FVarSubst_insert(v___x_5450_, v_majorFVarId_5379_, v___x_5451_);
                v___x_5453_ = crate::leanh::lean_unsigned_to_nat(0);
                if v_isShared_5449_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5448_, 1, v___x_5453_);
                    crate::leanh::lean_ctor_set(v___x_5448_, 0, v___x_5452_);
                    v___x_5455_ = v___x_5448_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5483_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5483_, 0, v___x_5452_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5483_, 1, v___x_5453_);
                    v___x_5455_ = v_reuseFailAlloc_5483_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5456_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2(v_fst_5441_, v_a_5418_, v_sz_5427_, v___x_5428_, v___x_5455_);
                crate::leanh::lean_dec(v_a_5418_);
                v_options_5457_ = crate::leanh::lean_ctor_get(v___y_5425_, 2);
                v_hasTrace_5458_ = crate::leanh::lean_ctor_get_uint8(
                    v_options_5457_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                if v_hasTrace_5458_ == 0 {
                    v_fst_5459_ = crate::leanh::lean_ctor_get(v___x_5456_, 0);
                    crate::leanh::lean_inc(v_fst_5459_);
                    crate::leanh::lean_dec_ref(v___x_5456_);
                    crate::leanh::lean_inc(v_snd_5446_);
                    v___y_5401_ = v_fst_5459_;
                    v___y_5402_ = v_fst_5445_;
                    v___y_5403_ = v_snd_5446_;
                    v___y_5404_ = v___x_5451_;
                    v___y_5405_ = v_fst_5435_;
                    v___y_5406_ = v_snd_5446_;
                    v___y_5407_ = v___x_5428_;
                    v___y_5408_ = v_fst_5441_;
                    v___y_5409_ = v___y_5423_;
                    v___y_5410_ = v___y_5424_;
                    v___y_5411_ = v___y_5425_;
                    v___y_5412_ = v___y_5426_;
                    state = 1;
                    continue;
                } else {
                    v_fst_5460_ = crate::leanh::lean_ctor_get(v___x_5456_, 0);
                    v_isSharedCheck_5481_ = (!crate::leanh::lean_is_exclusive(v___x_5456_)) as u8;
                    if v_isSharedCheck_5481_ == 0 {
                        v_unused_5482_ = crate::leanh::lean_ctor_get(v___x_5456_, 1);
                        crate::leanh::lean_dec(v_unused_5482_);
                        v___x_5462_ = v___x_5456_;
                        v_isShared_5463_ = v_isSharedCheck_5481_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fst_5460_);
                        crate::leanh::lean_dec(v___x_5456_);
                        v___x_5462_ = crate::leanh::lean_box(0);
                        v_isShared_5463_ = v_isSharedCheck_5481_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v_inheritedTraceOptions_5464_ = crate::leanh::lean_ctor_get(v___y_5425_, 13);
                v___x_5465_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5_once), _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5);
                v___x_5466_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                    v_inheritedTraceOptions_5464_,
                    v_options_5457_,
                    v___x_5465_,
                );
                if v___x_5466_ == 0 {
                    crate::leanh::lean_del_object(v___x_5462_);
                    crate::leanh::lean_inc(v_snd_5446_);
                    v___y_5401_ = v_fst_5460_;
                    v___y_5402_ = v_fst_5445_;
                    v___y_5403_ = v_snd_5446_;
                    v___y_5404_ = v___x_5451_;
                    v___y_5405_ = v_fst_5435_;
                    v___y_5406_ = v_snd_5446_;
                    v___y_5407_ = v___x_5428_;
                    v___y_5408_ = v_fst_5441_;
                    v___y_5409_ = v___y_5423_;
                    v___y_5410_ = v___y_5424_;
                    v___y_5411_ = v___y_5425_;
                    v___y_5412_ = v___y_5426_;
                    state = 1;
                    continue;
                } else {
                    v___x_5467_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1), core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1_once), _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1);
                    crate::leanh::lean_inc(v_snd_5446_);
                    v___x_5468_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5468_, 0, v_snd_5446_);
                    if v_isShared_5463_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_5462_, 7);
                        crate::leanh::lean_ctor_set(v___x_5462_, 1, v___x_5468_);
                        crate::leanh::lean_ctor_set(v___x_5462_, 0, v___x_5467_);
                        v___x_5470_ = v___x_5462_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_5480_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5480_, 0, v___x_5467_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5480_, 1, v___x_5468_);
                        v___x_5470_ = v_reuseFailAlloc_5480_;
                        state = 6;
                        continue;
                    }
                }
            }
            6 => {
                v___x_5471_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v_cls_5421_, v___x_5470_, v___y_5423_, v___y_5424_, v___y_5425_, v___y_5426_);
                if crate::leanh::lean_obj_tag(v___x_5471_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_5471_, 1);
                    crate::leanh::lean_inc(v_snd_5446_);
                    v___y_5401_ = v_fst_5460_;
                    v___y_5402_ = v_fst_5445_;
                    v___y_5403_ = v_snd_5446_;
                    v___y_5404_ = v___x_5451_;
                    v___y_5405_ = v_fst_5435_;
                    v___y_5406_ = v_snd_5446_;
                    v___y_5407_ = v___x_5428_;
                    v___y_5408_ = v_fst_5441_;
                    v___y_5409_ = v___y_5423_;
                    v___y_5410_ = v___y_5424_;
                    v___y_5411_ = v___y_5425_;
                    v___y_5412_ = v___y_5426_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_fst_5460_);
                    crate::leanh::lean_dec_ref(v___x_5451_);
                    crate::leanh::lean_dec(v_snd_5446_);
                    crate::leanh::lean_dec(v_fst_5445_);
                    crate::leanh::lean_dec(v_fst_5441_);
                    crate::leanh::lean_dec(v_fst_5435_);
                    crate::leanh::lean_dec_ref(v_givenNames_5380_);
                    crate::leanh::lean_dec_ref(v_a_5376_);
                    v_a_5472_ = crate::leanh::lean_ctor_get(v___x_5471_, 0);
                    v_isSharedCheck_5479_ = (!crate::leanh::lean_is_exclusive(v___x_5471_)) as u8;
                    if v_isSharedCheck_5479_ == 0 {
                        v___x_5474_ = v___x_5471_;
                        v_isShared_5475_ = v_isSharedCheck_5479_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5472_);
                        crate::leanh::lean_dec(v___x_5471_);
                        v___x_5474_ = crate::leanh::lean_box(0);
                        v_isShared_5475_ = v_isSharedCheck_5479_;
                        state = 7;
                        continue;
                    }
                }
            }
            7 => {
                if v_isShared_5475_ == 0 {
                    v___x_5477_ = v___x_5474_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5478_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5478_, 0, v_a_5472_);
                    v___x_5477_ = v_reuseFailAlloc_5478_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5477_;
            }
            9 => {
                if v_isShared_5488_ == 0 {
                    v___x_5490_ = v___x_5487_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5491_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5491_, 0, v_a_5485_);
                    v___x_5490_ = v_reuseFailAlloc_5491_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5490_;
            }
            11 => {
                if v_isShared_5496_ == 0 {
                    v___x_5498_ = v___x_5495_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5499_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5499_, 0, v_a_5493_);
                    v___x_5498_ = v_reuseFailAlloc_5499_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5498_;
            }
            13 => {
                if v_isShared_5504_ == 0 {
                    v___x_5506_ = v___x_5503_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5507_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5507_, 0, v_a_5501_);
                    v___x_5506_ = v_reuseFailAlloc_5507_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_5506_;
            }
            15 => {
                v___x_5514_ = (crate::leanh::lean_unbox(v_a_5510_) as u8);
                crate::leanh::lean_dec(v_a_5510_);
                if v___x_5514_ == 0 {
                    crate::leanh::lean_del_object(v___x_5512_);
                    crate::leanh::lean_dec(v_recursorName_5381_);
                    v___y_5423_ = v___y_5385_;
                    v___y_5424_ = v___y_5386_;
                    v___y_5425_ = v___y_5387_;
                    v___y_5426_ = v___y_5388_;
                    state = 2;
                    continue;
                } else {
                    v___x_5515_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3), core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3_once), _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3);
                    v___x_5516_ = l_Lean_MessageData_ofName(v_recursorName_5381_);
                    v___x_5517_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5517_, 0, v___x_5515_);
                    crate::leanh::lean_ctor_set(v___x_5517_, 1, v___x_5516_);
                    v___x_5518_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5), core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5_once), _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5);
                    v___x_5519_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5519_, 0, v___x_5517_);
                    crate::leanh::lean_ctor_set(v___x_5519_, 1, v___x_5518_);
                    if v_isShared_5513_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_5512_, 1);
                        crate::leanh::lean_ctor_set(v___x_5512_, 0, v___x_5519_);
                        v___x_5521_ = v___x_5512_;
                        state = 16;
                        continue;
                    } else {
                        v_reuseFailAlloc_5531_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5531_, 0, v___x_5519_);
                        v___x_5521_ = v_reuseFailAlloc_5531_;
                        state = 16;
                        continue;
                    }
                }
            }
            16 => {
                crate::leanh::lean_inc(v_mvarId_5378_);
                v___x_5522_ = l_Lean_Meta_throwTacticEx___redArg(
                    v___x_5399_,
                    v_mvarId_5378_,
                    v___x_5521_,
                    v___y_5385_,
                    v___y_5386_,
                    v___y_5387_,
                    v___y_5388_,
                );
                if crate::leanh::lean_obj_tag(v___x_5522_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_5522_, 1);
                    v___y_5423_ = v___y_5385_;
                    v___y_5424_ = v___y_5386_;
                    v___y_5425_ = v___y_5387_;
                    v___y_5426_ = v___y_5388_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_a_5418_);
                    crate::leanh::lean_dec_ref(v_givenNames_5380_);
                    crate::leanh::lean_dec(v_majorFVarId_5379_);
                    crate::leanh::lean_dec(v_mvarId_5378_);
                    crate::leanh::lean_dec_ref(v_a_5376_);
                    v_a_5523_ = crate::leanh::lean_ctor_get(v___x_5522_, 0);
                    v_isSharedCheck_5530_ = (!crate::leanh::lean_is_exclusive(v___x_5522_)) as u8;
                    if v_isSharedCheck_5530_ == 0 {
                        v___x_5525_ = v___x_5522_;
                        v_isShared_5526_ = v_isSharedCheck_5530_;
                        state = 17;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5523_);
                        crate::leanh::lean_dec(v___x_5522_);
                        v___x_5525_ = crate::leanh::lean_box(0);
                        v_isShared_5526_ = v_isSharedCheck_5530_;
                        state = 17;
                        continue;
                    }
                }
            }
            17 => {
                if v_isShared_5526_ == 0 {
                    v___x_5528_ = v___x_5525_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_5529_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5529_, 0, v_a_5523_);
                    v___x_5528_ = v_reuseFailAlloc_5529_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_5528_;
            }
            19 => {
                if v_isShared_5536_ == 0 {
                    v___x_5538_ = v___x_5535_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_5539_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5539_, 0, v_a_5533_);
                    v___x_5538_ = v_reuseFailAlloc_5539_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_5538_;
            }
            21 => {
                if v_isShared_5544_ == 0 {
                    v___x_5546_ = v___x_5543_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_5547_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5547_, 0, v_a_5541_);
                    v___x_5546_ = v_reuseFailAlloc_5547_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_5546_;
            }
            23 => {
                if v_isShared_5552_ == 0 {
                    v___x_5554_ = v___x_5551_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_5555_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5555_, 0, v_a_5549_);
                    v___x_5554_ = v_reuseFailAlloc_5555_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_5554_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___boxed(
    mut v_a_5557_: *mut crate::leanh::LeanObject,
    mut v_val_5558_: *mut crate::leanh::LeanObject,
    mut v_mvarId_5559_: *mut crate::leanh::LeanObject,
    mut v_majorFVarId_5560_: *mut crate::leanh::LeanObject,
    mut v_givenNames_5561_: *mut crate::leanh::LeanObject,
    mut v_recursorName_5562_: *mut crate::leanh::LeanObject,
    mut v_x_5563_: *mut crate::leanh::LeanObject,
    mut v_x_5564_: *mut crate::leanh::LeanObject,
    mut v_x_5565_: *mut crate::leanh::LeanObject,
    mut v___y_5566_: *mut crate::leanh::LeanObject,
    mut v___y_5567_: *mut crate::leanh::LeanObject,
    mut v___y_5568_: *mut crate::leanh::LeanObject,
    mut v___y_5569_: *mut crate::leanh::LeanObject,
    mut v___y_5570_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5571_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4(v_a_5557_, v_val_5558_, v_mvarId_5559_, v_majorFVarId_5560_, v_givenNames_5561_, v_recursorName_5562_, v_x_5563_, v_x_5564_, v_x_5565_, v___y_5566_, v___y_5567_, v___y_5568_, v___y_5569_);
    crate::leanh::lean_dec(v___y_5569_);
    crate::leanh::lean_dec_ref(v___y_5568_);
    crate::leanh::lean_dec(v___y_5567_);
    crate::leanh::lean_dec_ref(v___y_5566_);
    return v_res_5571_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4(
    mut v_val_5572_: *mut crate::leanh::LeanObject,
    mut v_mvarId_5573_: *mut crate::leanh::LeanObject,
    mut v_a_5574_: *mut crate::leanh::LeanObject,
    mut v_majorFVarId_5575_: *mut crate::leanh::LeanObject,
    mut v_givenNames_5576_: *mut crate::leanh::LeanObject,
    mut v_recursorName_5577_: *mut crate::leanh::LeanObject,
    mut v_x_5578_: *mut crate::leanh::LeanObject,
    mut v_x_5579_: *mut crate::leanh::LeanObject,
    mut v_x_5580_: *mut crate::leanh::LeanObject,
    mut v___y_5581_: *mut crate::leanh::LeanObject,
    mut v___y_5582_: *mut crate::leanh::LeanObject,
    mut v___y_5583_: *mut crate::leanh::LeanObject,
    mut v___y_5584_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fn_5586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_5587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_depElim_5592_: u8 = 0;
    let mut v_paramsPos_5593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5603_: usize = 0;
    let mut v___y_5604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5609_: usize = 0;
    let mut v___x_5610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cls_5617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5623_: usize = 0;
    let mut v___x_5624_: usize = 0;
    let mut v___x_5625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5627_: u8 = 0;
    let mut v___x_5628_: u8 = 0;
    let mut v___x_5629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5645_: u8 = 0;
    let mut v___x_5646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_5653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_5654_: u8 = 0;
    let mut v_fst_5655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5659_: u8 = 0;
    let mut v_inheritedTraceOptions_5660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5662_: u8 = 0;
    let mut v___x_5663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5671_: u8 = 0;
    let mut v___x_5673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5675_: u8 = 0;
    let mut v_reuseFailAlloc_5676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5677_: u8 = 0;
    let mut v_unused_5678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5680_: u8 = 0;
    let mut v_a_5681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5684_: u8 = 0;
    let mut v___x_5686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5688_: u8 = 0;
    let mut v_a_5689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5692_: u8 = 0;
    let mut v___x_5694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5696_: u8 = 0;
    let mut v_a_5697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5700_: u8 = 0;
    let mut v___x_5702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5704_: u8 = 0;
    let mut v___x_5705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5709_: u8 = 0;
    let mut v___x_5710_: u8 = 0;
    let mut v___x_5711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5722_: u8 = 0;
    let mut v___x_5724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5726_: u8 = 0;
    let mut v_reuseFailAlloc_5727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5728_: u8 = 0;
    let mut v_a_5729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5732_: u8 = 0;
    let mut v___x_5734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5736_: u8 = 0;
    let mut v_a_5737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5740_: u8 = 0;
    let mut v___x_5742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5744_: u8 = 0;
    let mut v_a_5745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5748_: u8 = 0;
    let mut v___x_5750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5752_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5578_) == 5 {
                    v_fn_5586_ = crate::leanh::lean_ctor_get(v_x_5578_, 0);
                    crate::leanh::lean_inc_ref(v_fn_5586_);
                    v_arg_5587_ = crate::leanh::lean_ctor_get(v_x_5578_, 1);
                    crate::leanh::lean_inc_ref(v_arg_5587_);
                    crate::leanh::lean_dec_ref_known(v_x_5578_, 2);
                    v___x_5588_ = lean_array_set(v_x_5579_, v_x_5580_, v_arg_5587_);
                    v___x_5589_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_5590_ = lean_nat_sub(v_x_5580_, v___x_5589_);
                    v___x_5591_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4(v_a_5574_, v_val_5572_, v_mvarId_5573_, v_majorFVarId_5575_, v_givenNames_5576_, v_recursorName_5577_, v_fn_5586_, v___x_5588_, v___x_5590_, v___y_5581_, v___y_5582_, v___y_5583_, v___y_5584_);
                    return v___x_5591_;
                } else {
                    crate::leanh::lean_dec_ref(v_x_5578_);
                    v_depElim_5592_ = crate::leanh::lean_ctor_get_uint8(
                        v_a_5574_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                    );
                    v_paramsPos_5593_ = crate::leanh::lean_ctor_get(v_a_5574_, 5);
                    crate::leanh::lean_inc(v_paramsPos_5593_);
                    crate::leanh::lean_inc(v_mvarId_5573_);
                    crate::leanh::lean_inc_ref(v_val_5572_);
                    v___x_5594_ = l_List_forM___at___00Lean_MVarId_induction_spec__0(
                        v_x_5579_,
                        v_val_5572_,
                        v_mvarId_5573_,
                        v_paramsPos_5593_,
                        v___y_5581_,
                        v___y_5582_,
                        v___y_5583_,
                        v___y_5584_,
                    );
                    crate::leanh::lean_dec_ref(v_x_5579_);
                    if crate::leanh::lean_obj_tag(v___x_5594_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_5594_, 1);
                        v___x_5595_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1;
                        crate::leanh::lean_inc_ref(v_a_5574_);
                        crate::leanh::lean_inc(v_mvarId_5573_);
                        v___x_5613_ = l_Lean_Meta_getMajorTypeIndices(
                            v_mvarId_5573_,
                            v___x_5595_,
                            v_a_5574_,
                            v_val_5572_,
                            v___y_5581_,
                            v___y_5582_,
                            v___y_5583_,
                            v___y_5584_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_5613_) == 0 {
                            v_a_5614_ = crate::leanh::lean_ctor_get(v___x_5613_, 0);
                            crate::leanh::lean_inc(v_a_5614_);
                            crate::leanh::lean_dec_ref_known(v___x_5613_, 1);
                            crate::leanh::lean_inc(v_mvarId_5573_);
                            v___x_5615_ = l_Lean_MVarId_getType(
                                v_mvarId_5573_,
                                v___y_5581_,
                                v___y_5582_,
                                v___y_5583_,
                                v___y_5584_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_5615_) == 0 {
                                v_a_5616_ = crate::leanh::lean_ctor_get(v___x_5615_, 0);
                                crate::leanh::lean_inc(v_a_5616_);
                                crate::leanh::lean_dec_ref_known(v___x_5615_, 1);
                                v_cls_5617_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2;
                                if v_depElim_5592_ == 0 {
                                    crate::leanh::lean_inc(v_majorFVarId_5575_);
                                    v___x_5705_ = l_Lean_exprDependsOn___at___00Lean_Meta_getMajorTypeIndices_spec__2___redArg(v_a_5616_, v_majorFVarId_5575_, v___y_5582_);
                                    v_a_5706_ = crate::leanh::lean_ctor_get(v___x_5705_, 0);
                                    v_isSharedCheck_5728_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_5705_)) as u8;
                                    if v_isSharedCheck_5728_ == 0 {
                                        v___x_5708_ = v___x_5705_;
                                        v_isShared_5709_ = v_isSharedCheck_5728_;
                                        state = 15;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_5706_);
                                        crate::leanh::lean_dec(v___x_5705_);
                                        v___x_5708_ = crate::leanh::lean_box(0);
                                        v_isShared_5709_ = v_isSharedCheck_5728_;
                                        state = 15;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_5616_);
                                    crate::leanh::lean_dec(v_recursorName_5577_);
                                    v___y_5619_ = v___y_5581_;
                                    v___y_5620_ = v___y_5582_;
                                    v___y_5621_ = v___y_5583_;
                                    v___y_5622_ = v___y_5584_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_5614_);
                                crate::leanh::lean_dec(v_recursorName_5577_);
                                crate::leanh::lean_dec_ref(v_givenNames_5576_);
                                crate::leanh::lean_dec(v_majorFVarId_5575_);
                                crate::leanh::lean_dec_ref(v_a_5574_);
                                crate::leanh::lean_dec(v_mvarId_5573_);
                                v_a_5729_ = crate::leanh::lean_ctor_get(v___x_5615_, 0);
                                v_isSharedCheck_5736_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5615_)) as u8;
                                if v_isSharedCheck_5736_ == 0 {
                                    v___x_5731_ = v___x_5615_;
                                    v_isShared_5732_ = v_isSharedCheck_5736_;
                                    state = 19;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5729_);
                                    crate::leanh::lean_dec(v___x_5615_);
                                    v___x_5731_ = crate::leanh::lean_box(0);
                                    v_isShared_5732_ = v_isSharedCheck_5736_;
                                    state = 19;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_recursorName_5577_);
                            crate::leanh::lean_dec_ref(v_givenNames_5576_);
                            crate::leanh::lean_dec(v_majorFVarId_5575_);
                            crate::leanh::lean_dec_ref(v_a_5574_);
                            crate::leanh::lean_dec(v_mvarId_5573_);
                            v_a_5737_ = crate::leanh::lean_ctor_get(v___x_5613_, 0);
                            v_isSharedCheck_5744_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5613_)) as u8;
                            if v_isSharedCheck_5744_ == 0 {
                                v___x_5739_ = v___x_5613_;
                                v_isShared_5740_ = v_isSharedCheck_5744_;
                                state = 21;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5737_);
                                crate::leanh::lean_dec(v___x_5613_);
                                v___x_5739_ = crate::leanh::lean_box(0);
                                v_isShared_5740_ = v_isSharedCheck_5744_;
                                state = 21;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_recursorName_5577_);
                        crate::leanh::lean_dec_ref(v_givenNames_5576_);
                        crate::leanh::lean_dec(v_majorFVarId_5575_);
                        crate::leanh::lean_dec_ref(v_a_5574_);
                        crate::leanh::lean_dec(v_mvarId_5573_);
                        crate::leanh::lean_dec_ref(v_val_5572_);
                        v_a_5745_ = crate::leanh::lean_ctor_get(v___x_5594_, 0);
                        v_isSharedCheck_5752_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5594_)) as u8;
                        if v_isSharedCheck_5752_ == 0 {
                            v___x_5747_ = v___x_5594_;
                            v_isShared_5748_ = v_isSharedCheck_5752_;
                            state = 23;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5745_);
                            crate::leanh::lean_dec(v___x_5594_);
                            v___x_5747_ = crate::leanh::lean_box(0);
                            v_isShared_5748_ = v_isSharedCheck_5752_;
                            state = 23;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_sz_5609_ = lean_array_size(v___y_5604_);
                v___x_5610_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__3(v_sz_5609_, v___y_5603_, v___y_5604_);
                v___f_5611_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___lam__0___boxed
                        as *mut core::ffi::c_void,
                    14,
                    9,
                );
                crate::leanh::lean_closure_set(v___f_5611_, 0, v___y_5597_);
                crate::leanh::lean_closure_set(v___f_5611_, 1, v___x_5595_);
                crate::leanh::lean_closure_set(v___f_5611_, 2, v___y_5601_);
                crate::leanh::lean_closure_set(v___f_5611_, 3, v_a_5574_);
                crate::leanh::lean_closure_set(v___f_5611_, 4, v___x_5610_);
                crate::leanh::lean_closure_set(v___f_5611_, 5, v_givenNames_5576_);
                crate::leanh::lean_closure_set(v___f_5611_, 6, v___y_5600_);
                crate::leanh::lean_closure_set(v___f_5611_, 7, v___y_5599_);
                crate::leanh::lean_closure_set(v___f_5611_, 8, v___y_5598_);
                v___x_5612_ =
                    l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(
                        v___y_5602_,
                        v___f_5611_,
                        v___y_5605_,
                        v___y_5606_,
                        v___y_5607_,
                        v___y_5608_,
                    );
                return v___x_5612_;
            }
            2 => {
                v_sz_5623_ = lean_array_size(v_a_5614_);
                v___x_5624_ = 0usize;
                crate::leanh::lean_inc(v_a_5614_);
                v___x_5625_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_induction_spec__1(v_sz_5623_, v___x_5624_, v_a_5614_);
                crate::leanh::lean_inc(v_majorFVarId_5575_);
                v___x_5626_ = lean_array_push(v___x_5625_, v_majorFVarId_5575_);
                v___x_5627_ = 1;
                v___x_5628_ = 0;
                v___x_5629_ = l_Lean_MVarId_revert(
                    v_mvarId_5573_,
                    v___x_5626_,
                    v___x_5627_,
                    v___x_5628_,
                    v___y_5619_,
                    v___y_5620_,
                    v___y_5621_,
                    v___y_5622_,
                );
                if crate::leanh::lean_obj_tag(v___x_5629_) == 0 {
                    v_a_5630_ = crate::leanh::lean_ctor_get(v___x_5629_, 0);
                    crate::leanh::lean_inc(v_a_5630_);
                    crate::leanh::lean_dec_ref_known(v___x_5629_, 1);
                    v_fst_5631_ = crate::leanh::lean_ctor_get(v_a_5630_, 0);
                    crate::leanh::lean_inc(v_fst_5631_);
                    v_snd_5632_ = crate::leanh::lean_ctor_get(v_a_5630_, 1);
                    crate::leanh::lean_inc(v_snd_5632_);
                    crate::leanh::lean_dec(v_a_5630_);
                    v___x_5633_ = lean_array_get_size(v_a_5614_);
                    v___x_5634_ = crate::leanh::lean_box(0);
                    v___x_5635_ = l_Lean_Meta_introNCore(
                        v_snd_5632_,
                        v___x_5633_,
                        v___x_5634_,
                        v___x_5628_,
                        v___x_5627_,
                        v___y_5619_,
                        v___y_5620_,
                        v___y_5621_,
                        v___y_5622_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5635_) == 0 {
                        v_a_5636_ = crate::leanh::lean_ctor_get(v___x_5635_, 0);
                        crate::leanh::lean_inc(v_a_5636_);
                        crate::leanh::lean_dec_ref_known(v___x_5635_, 1);
                        v_fst_5637_ = crate::leanh::lean_ctor_get(v_a_5636_, 0);
                        crate::leanh::lean_inc(v_fst_5637_);
                        v_snd_5638_ = crate::leanh::lean_ctor_get(v_a_5636_, 1);
                        crate::leanh::lean_inc(v_snd_5638_);
                        crate::leanh::lean_dec(v_a_5636_);
                        v___x_5639_ = l_Lean_Meta_intro1Core(
                            v_snd_5638_,
                            v___x_5627_,
                            v___y_5619_,
                            v___y_5620_,
                            v___y_5621_,
                            v___y_5622_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_5639_) == 0 {
                            v_a_5640_ = crate::leanh::lean_ctor_get(v___x_5639_, 0);
                            crate::leanh::lean_inc(v_a_5640_);
                            crate::leanh::lean_dec_ref_known(v___x_5639_, 1);
                            v_fst_5641_ = crate::leanh::lean_ctor_get(v_a_5640_, 0);
                            v_snd_5642_ = crate::leanh::lean_ctor_get(v_a_5640_, 1);
                            v_isSharedCheck_5680_ =
                                (!crate::leanh::lean_is_exclusive(v_a_5640_)) as u8;
                            if v_isSharedCheck_5680_ == 0 {
                                v___x_5644_ = v_a_5640_;
                                v_isShared_5645_ = v_isSharedCheck_5680_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_snd_5642_);
                                crate::leanh::lean_inc(v_fst_5641_);
                                crate::leanh::lean_dec(v_a_5640_);
                                v___x_5644_ = crate::leanh::lean_box(0);
                                v_isShared_5645_ = v_isSharedCheck_5680_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_fst_5637_);
                            crate::leanh::lean_dec(v_fst_5631_);
                            crate::leanh::lean_dec(v_a_5614_);
                            crate::leanh::lean_dec_ref(v_givenNames_5576_);
                            crate::leanh::lean_dec(v_majorFVarId_5575_);
                            crate::leanh::lean_dec_ref(v_a_5574_);
                            v_a_5681_ = crate::leanh::lean_ctor_get(v___x_5639_, 0);
                            v_isSharedCheck_5688_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5639_)) as u8;
                            if v_isSharedCheck_5688_ == 0 {
                                v___x_5683_ = v___x_5639_;
                                v_isShared_5684_ = v_isSharedCheck_5688_;
                                state = 9;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5681_);
                                crate::leanh::lean_dec(v___x_5639_);
                                v___x_5683_ = crate::leanh::lean_box(0);
                                v_isShared_5684_ = v_isSharedCheck_5688_;
                                state = 9;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_fst_5631_);
                        crate::leanh::lean_dec(v_a_5614_);
                        crate::leanh::lean_dec_ref(v_givenNames_5576_);
                        crate::leanh::lean_dec(v_majorFVarId_5575_);
                        crate::leanh::lean_dec_ref(v_a_5574_);
                        v_a_5689_ = crate::leanh::lean_ctor_get(v___x_5635_, 0);
                        v_isSharedCheck_5696_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5635_)) as u8;
                        if v_isSharedCheck_5696_ == 0 {
                            v___x_5691_ = v___x_5635_;
                            v_isShared_5692_ = v_isSharedCheck_5696_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5689_);
                            crate::leanh::lean_dec(v___x_5635_);
                            v___x_5691_ = crate::leanh::lean_box(0);
                            v_isShared_5692_ = v_isSharedCheck_5696_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_5614_);
                    crate::leanh::lean_dec_ref(v_givenNames_5576_);
                    crate::leanh::lean_dec(v_majorFVarId_5575_);
                    crate::leanh::lean_dec_ref(v_a_5574_);
                    v_a_5697_ = crate::leanh::lean_ctor_get(v___x_5629_, 0);
                    v_isSharedCheck_5704_ = (!crate::leanh::lean_is_exclusive(v___x_5629_)) as u8;
                    if v_isSharedCheck_5704_ == 0 {
                        v___x_5699_ = v___x_5629_;
                        v_isShared_5700_ = v_isSharedCheck_5704_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5697_);
                        crate::leanh::lean_dec(v___x_5629_);
                        v___x_5699_ = crate::leanh::lean_box(0);
                        v_isShared_5700_ = v_isSharedCheck_5704_;
                        state = 13;
                        continue;
                    }
                }
            }
            3 => {
                v___x_5646_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v_fst_5641_);
                v___x_5647_ = l_Lean_mkFVar(v_fst_5641_);
                crate::leanh::lean_inc_ref(v___x_5647_);
                v___x_5648_ =
                    l_Lean_Meta_FVarSubst_insert(v___x_5646_, v_majorFVarId_5575_, v___x_5647_);
                v___x_5649_ = crate::leanh::lean_unsigned_to_nat(0);
                if v_isShared_5645_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5644_, 1, v___x_5649_);
                    crate::leanh::lean_ctor_set(v___x_5644_, 0, v___x_5648_);
                    v___x_5651_ = v___x_5644_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5679_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5679_, 0, v___x_5648_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5679_, 1, v___x_5649_);
                    v___x_5651_ = v_reuseFailAlloc_5679_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5652_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_induction_spec__2(v_fst_5637_, v_a_5614_, v_sz_5623_, v___x_5624_, v___x_5651_);
                crate::leanh::lean_dec(v_a_5614_);
                v_options_5653_ = crate::leanh::lean_ctor_get(v___y_5621_, 2);
                v_hasTrace_5654_ = crate::leanh::lean_ctor_get_uint8(
                    v_options_5653_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                if v_hasTrace_5654_ == 0 {
                    v_fst_5655_ = crate::leanh::lean_ctor_get(v___x_5652_, 0);
                    crate::leanh::lean_inc(v_fst_5655_);
                    crate::leanh::lean_dec_ref(v___x_5652_);
                    crate::leanh::lean_inc(v_snd_5642_);
                    v___y_5597_ = v_snd_5642_;
                    v___y_5598_ = v_fst_5655_;
                    v___y_5599_ = v___x_5647_;
                    v___y_5600_ = v_fst_5631_;
                    v___y_5601_ = v_fst_5641_;
                    v___y_5602_ = v_snd_5642_;
                    v___y_5603_ = v___x_5624_;
                    v___y_5604_ = v_fst_5637_;
                    v___y_5605_ = v___y_5619_;
                    v___y_5606_ = v___y_5620_;
                    v___y_5607_ = v___y_5621_;
                    v___y_5608_ = v___y_5622_;
                    state = 1;
                    continue;
                } else {
                    v_fst_5656_ = crate::leanh::lean_ctor_get(v___x_5652_, 0);
                    v_isSharedCheck_5677_ = (!crate::leanh::lean_is_exclusive(v___x_5652_)) as u8;
                    if v_isSharedCheck_5677_ == 0 {
                        v_unused_5678_ = crate::leanh::lean_ctor_get(v___x_5652_, 1);
                        crate::leanh::lean_dec(v_unused_5678_);
                        v___x_5658_ = v___x_5652_;
                        v_isShared_5659_ = v_isSharedCheck_5677_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fst_5656_);
                        crate::leanh::lean_dec(v___x_5652_);
                        v___x_5658_ = crate::leanh::lean_box(0);
                        v_isShared_5659_ = v_isSharedCheck_5677_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v_inheritedTraceOptions_5660_ = crate::leanh::lean_ctor_get(v___y_5621_, 13);
                v___x_5661_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5_once), _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__5);
                v___x_5662_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                    v_inheritedTraceOptions_5660_,
                    v_options_5653_,
                    v___x_5661_,
                );
                if v___x_5662_ == 0 {
                    crate::leanh::lean_del_object(v___x_5658_);
                    crate::leanh::lean_inc(v_snd_5642_);
                    v___y_5597_ = v_snd_5642_;
                    v___y_5598_ = v_fst_5656_;
                    v___y_5599_ = v___x_5647_;
                    v___y_5600_ = v_fst_5631_;
                    v___y_5601_ = v_fst_5641_;
                    v___y_5602_ = v_snd_5642_;
                    v___y_5603_ = v___x_5624_;
                    v___y_5604_ = v_fst_5637_;
                    v___y_5605_ = v___y_5619_;
                    v___y_5606_ = v___y_5620_;
                    v___y_5607_ = v___y_5621_;
                    v___y_5608_ = v___y_5622_;
                    state = 1;
                    continue;
                } else {
                    v___x_5663_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1), core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1_once), _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__1);
                    crate::leanh::lean_inc(v_snd_5642_);
                    v___x_5664_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5664_, 0, v_snd_5642_);
                    if v_isShared_5659_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_5658_, 7);
                        crate::leanh::lean_ctor_set(v___x_5658_, 1, v___x_5664_);
                        crate::leanh::lean_ctor_set(v___x_5658_, 0, v___x_5663_);
                        v___x_5666_ = v___x_5658_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_5676_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5676_, 0, v___x_5663_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5676_, 1, v___x_5664_);
                        v___x_5666_ = v_reuseFailAlloc_5676_;
                        state = 6;
                        continue;
                    }
                }
            }
            6 => {
                v___x_5667_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v_cls_5617_, v___x_5666_, v___y_5619_, v___y_5620_, v___y_5621_, v___y_5622_);
                if crate::leanh::lean_obj_tag(v___x_5667_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_5667_, 1);
                    crate::leanh::lean_inc(v_snd_5642_);
                    v___y_5597_ = v_snd_5642_;
                    v___y_5598_ = v_fst_5656_;
                    v___y_5599_ = v___x_5647_;
                    v___y_5600_ = v_fst_5631_;
                    v___y_5601_ = v_fst_5641_;
                    v___y_5602_ = v_snd_5642_;
                    v___y_5603_ = v___x_5624_;
                    v___y_5604_ = v_fst_5637_;
                    v___y_5605_ = v___y_5619_;
                    v___y_5606_ = v___y_5620_;
                    v___y_5607_ = v___y_5621_;
                    v___y_5608_ = v___y_5622_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_fst_5656_);
                    crate::leanh::lean_dec_ref(v___x_5647_);
                    crate::leanh::lean_dec(v_snd_5642_);
                    crate::leanh::lean_dec(v_fst_5641_);
                    crate::leanh::lean_dec(v_fst_5637_);
                    crate::leanh::lean_dec(v_fst_5631_);
                    crate::leanh::lean_dec_ref(v_givenNames_5576_);
                    crate::leanh::lean_dec_ref(v_a_5574_);
                    v_a_5668_ = crate::leanh::lean_ctor_get(v___x_5667_, 0);
                    v_isSharedCheck_5675_ = (!crate::leanh::lean_is_exclusive(v___x_5667_)) as u8;
                    if v_isSharedCheck_5675_ == 0 {
                        v___x_5670_ = v___x_5667_;
                        v_isShared_5671_ = v_isSharedCheck_5675_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5668_);
                        crate::leanh::lean_dec(v___x_5667_);
                        v___x_5670_ = crate::leanh::lean_box(0);
                        v_isShared_5671_ = v_isSharedCheck_5675_;
                        state = 7;
                        continue;
                    }
                }
            }
            7 => {
                if v_isShared_5671_ == 0 {
                    v___x_5673_ = v___x_5670_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5674_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5674_, 0, v_a_5668_);
                    v___x_5673_ = v_reuseFailAlloc_5674_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5673_;
            }
            9 => {
                if v_isShared_5684_ == 0 {
                    v___x_5686_ = v___x_5683_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5687_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5687_, 0, v_a_5681_);
                    v___x_5686_ = v_reuseFailAlloc_5687_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5686_;
            }
            11 => {
                if v_isShared_5692_ == 0 {
                    v___x_5694_ = v___x_5691_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5695_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5695_, 0, v_a_5689_);
                    v___x_5694_ = v_reuseFailAlloc_5695_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5694_;
            }
            13 => {
                if v_isShared_5700_ == 0 {
                    v___x_5702_ = v___x_5699_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5703_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5703_, 0, v_a_5697_);
                    v___x_5702_ = v_reuseFailAlloc_5703_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_5702_;
            }
            15 => {
                v___x_5710_ = (crate::leanh::lean_unbox(v_a_5706_) as u8);
                crate::leanh::lean_dec(v_a_5706_);
                if v___x_5710_ == 0 {
                    crate::leanh::lean_del_object(v___x_5708_);
                    crate::leanh::lean_dec(v_recursorName_5577_);
                    v___y_5619_ = v___y_5581_;
                    v___y_5620_ = v___y_5582_;
                    v___y_5621_ = v___y_5583_;
                    v___y_5622_ = v___y_5584_;
                    state = 2;
                    continue;
                } else {
                    v___x_5711_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3), core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3_once), _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__3);
                    v___x_5712_ = l_Lean_MessageData_ofName(v_recursorName_5577_);
                    v___x_5713_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5713_, 0, v___x_5711_);
                    crate::leanh::lean_ctor_set(v___x_5713_, 1, v___x_5712_);
                    v___x_5714_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5), core::ptr::addr_of_mut!(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5_once), _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4_spec__4___closed__5);
                    v___x_5715_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5715_, 0, v___x_5713_);
                    crate::leanh::lean_ctor_set(v___x_5715_, 1, v___x_5714_);
                    if v_isShared_5709_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_5708_, 1);
                        crate::leanh::lean_ctor_set(v___x_5708_, 0, v___x_5715_);
                        v___x_5717_ = v___x_5708_;
                        state = 16;
                        continue;
                    } else {
                        v_reuseFailAlloc_5727_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5727_, 0, v___x_5715_);
                        v___x_5717_ = v_reuseFailAlloc_5727_;
                        state = 16;
                        continue;
                    }
                }
            }
            16 => {
                crate::leanh::lean_inc(v_mvarId_5573_);
                v___x_5718_ = l_Lean_Meta_throwTacticEx___redArg(
                    v___x_5595_,
                    v_mvarId_5573_,
                    v___x_5717_,
                    v___y_5581_,
                    v___y_5582_,
                    v___y_5583_,
                    v___y_5584_,
                );
                if crate::leanh::lean_obj_tag(v___x_5718_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_5718_, 1);
                    v___y_5619_ = v___y_5581_;
                    v___y_5620_ = v___y_5582_;
                    v___y_5621_ = v___y_5583_;
                    v___y_5622_ = v___y_5584_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_a_5614_);
                    crate::leanh::lean_dec_ref(v_givenNames_5576_);
                    crate::leanh::lean_dec(v_majorFVarId_5575_);
                    crate::leanh::lean_dec_ref(v_a_5574_);
                    crate::leanh::lean_dec(v_mvarId_5573_);
                    v_a_5719_ = crate::leanh::lean_ctor_get(v___x_5718_, 0);
                    v_isSharedCheck_5726_ = (!crate::leanh::lean_is_exclusive(v___x_5718_)) as u8;
                    if v_isSharedCheck_5726_ == 0 {
                        v___x_5721_ = v___x_5718_;
                        v_isShared_5722_ = v_isSharedCheck_5726_;
                        state = 17;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5719_);
                        crate::leanh::lean_dec(v___x_5718_);
                        v___x_5721_ = crate::leanh::lean_box(0);
                        v_isShared_5722_ = v_isSharedCheck_5726_;
                        state = 17;
                        continue;
                    }
                }
            }
            17 => {
                if v_isShared_5722_ == 0 {
                    v___x_5724_ = v___x_5721_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_5725_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5725_, 0, v_a_5719_);
                    v___x_5724_ = v_reuseFailAlloc_5725_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_5724_;
            }
            19 => {
                if v_isShared_5732_ == 0 {
                    v___x_5734_ = v___x_5731_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_5735_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5735_, 0, v_a_5729_);
                    v___x_5734_ = v_reuseFailAlloc_5735_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_5734_;
            }
            21 => {
                if v_isShared_5740_ == 0 {
                    v___x_5742_ = v___x_5739_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_5743_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5743_, 0, v_a_5737_);
                    v___x_5742_ = v_reuseFailAlloc_5743_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_5742_;
            }
            23 => {
                if v_isShared_5748_ == 0 {
                    v___x_5750_ = v___x_5747_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_5751_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5751_, 0, v_a_5745_);
                    v___x_5750_ = v_reuseFailAlloc_5751_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_5750_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4___boxed(
    mut v_val_5753_: *mut crate::leanh::LeanObject,
    mut v_mvarId_5754_: *mut crate::leanh::LeanObject,
    mut v_a_5755_: *mut crate::leanh::LeanObject,
    mut v_majorFVarId_5756_: *mut crate::leanh::LeanObject,
    mut v_givenNames_5757_: *mut crate::leanh::LeanObject,
    mut v_recursorName_5758_: *mut crate::leanh::LeanObject,
    mut v_x_5759_: *mut crate::leanh::LeanObject,
    mut v_x_5760_: *mut crate::leanh::LeanObject,
    mut v_x_5761_: *mut crate::leanh::LeanObject,
    mut v___y_5762_: *mut crate::leanh::LeanObject,
    mut v___y_5763_: *mut crate::leanh::LeanObject,
    mut v___y_5764_: *mut crate::leanh::LeanObject,
    mut v___y_5765_: *mut crate::leanh::LeanObject,
    mut v___y_5766_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5767_ = l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4(
        v_val_5753_,
        v_mvarId_5754_,
        v_a_5755_,
        v_majorFVarId_5756_,
        v_givenNames_5757_,
        v_recursorName_5758_,
        v_x_5759_,
        v_x_5760_,
        v_x_5761_,
        v___y_5762_,
        v___y_5763_,
        v___y_5764_,
        v___y_5765_,
    );
    crate::leanh::lean_dec(v___y_5765_);
    crate::leanh::lean_dec_ref(v___y_5764_);
    crate::leanh::lean_dec(v___y_5763_);
    crate::leanh::lean_dec_ref(v___y_5762_);
    crate::leanh::lean_dec(v_x_5761_);
    return v_res_5767_;
}
pub unsafe fn _init_l_Lean_MVarId_induction___lam__0___closed__1() -> *mut crate::leanh::LeanObject
{
    let mut v___x_5769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5769_ = l_Lean_MVarId_induction___lam__0___closed__0;
    v___x_5770_ = l_Lean_stringToMessageData(v___x_5769_);
    return v___x_5770_;
}
pub unsafe fn l_Lean_MVarId_induction___lam__0(
    mut v___x_5771_: *mut crate::leanh::LeanObject,
    mut v_mvarId_5772_: *mut crate::leanh::LeanObject,
    mut v_majorFVarId_5773_: *mut crate::leanh::LeanObject,
    mut v_recursorName_5774_: *mut crate::leanh::LeanObject,
    mut v_givenNames_5775_: *mut crate::leanh::LeanObject,
    mut v_cls_5776_: *mut crate::leanh::LeanObject,
    mut v___y_5777_: *mut crate::leanh::LeanObject,
    mut v___y_5778_: *mut crate::leanh::LeanObject,
    mut v___y_5779_: *mut crate::leanh::LeanObject,
    mut v___y_5780_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_5783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeName_5794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_5799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_5800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5809_: u8 = 0;
    let mut v___x_5811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5813_: u8 = 0;
    let mut v_a_5814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5817_: u8 = 0;
    let mut v___x_5819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5821_: u8 = 0;
    let mut v_a_5822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5825_: u8 = 0;
    let mut v___x_5827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5829_: u8 = 0;
    let mut v_a_5830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5833_: u8 = 0;
    let mut v___x_5835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5837_: u8 = 0;
    let mut v_options_5838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_5839_: u8 = 0;
    let mut v_inheritedTraceOptions_5840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5843_: u8 = 0;
    let mut v___x_5844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5851_: u8 = 0;
    let mut v___x_5853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5855_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_5838_ = crate::leanh::lean_ctor_get(v___y_5779_, 2);
                v_hasTrace_5839_ = crate::leanh::lean_ctor_get_uint8(
                    v_options_5838_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                if v_hasTrace_5839_ == 0 {
                    crate::leanh::lean_dec(v_cls_5776_);
                    v___y_5783_ = v___y_5777_;
                    v___y_5784_ = v___y_5778_;
                    v___y_5785_ = v___y_5779_;
                    v___y_5786_ = v___y_5780_;
                    state = 1;
                    continue;
                } else {
                    v_inheritedTraceOptions_5840_ = crate::leanh::lean_ctor_get(v___y_5779_, 13);
                    v___x_5841_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__4;
                    crate::leanh::lean_inc(v_cls_5776_);
                    v___x_5842_ = l_Lean_Name_append(v___x_5841_, v_cls_5776_);
                    v___x_5843_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_5840_,
                        v_options_5838_,
                        v___x_5842_,
                    );
                    crate::leanh::lean_dec(v___x_5842_);
                    if v___x_5843_ == 0 {
                        crate::leanh::lean_dec(v_cls_5776_);
                        v___y_5783_ = v___y_5777_;
                        v___y_5784_ = v___y_5778_;
                        v___y_5785_ = v___y_5779_;
                        v___y_5786_ = v___y_5780_;
                        state = 1;
                        continue;
                    } else {
                        v___x_5844_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_MVarId_induction___lam__0___closed__1),
                            core::ptr::addr_of_mut!(
                                l_Lean_MVarId_induction___lam__0___closed__1_once
                            ),
                            _init_l_Lean_MVarId_induction___lam__0___closed__1,
                        );
                        crate::leanh::lean_inc(v_mvarId_5772_);
                        v___x_5845_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5845_, 0, v_mvarId_5772_);
                        v___x_5846_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5846_, 0, v___x_5844_);
                        crate::leanh::lean_ctor_set(v___x_5846_, 1, v___x_5845_);
                        v___x_5847_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_spec__1(v_cls_5776_, v___x_5846_, v___y_5777_, v___y_5778_, v___y_5779_, v___y_5780_);
                        if crate::leanh::lean_obj_tag(v___x_5847_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_5847_, 1);
                            v___y_5783_ = v___y_5777_;
                            v___y_5784_ = v___y_5778_;
                            v___y_5785_ = v___y_5779_;
                            v___y_5786_ = v___y_5780_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_givenNames_5775_);
                            crate::leanh::lean_dec(v_recursorName_5774_);
                            crate::leanh::lean_dec(v_majorFVarId_5773_);
                            crate::leanh::lean_dec(v_mvarId_5772_);
                            crate::leanh::lean_dec_ref(v___x_5771_);
                            v_a_5848_ = crate::leanh::lean_ctor_get(v___x_5847_, 0);
                            v_isSharedCheck_5855_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5847_)) as u8;
                            if v_isSharedCheck_5855_ == 0 {
                                v___x_5850_ = v___x_5847_;
                                v_isShared_5851_ = v_isSharedCheck_5855_;
                                state = 10;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5848_);
                                crate::leanh::lean_dec(v___x_5847_);
                                v___x_5850_ = crate::leanh::lean_box(0);
                                v_isShared_5851_ = v_isSharedCheck_5855_;
                                state = 10;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_5787_ = l_Lean_Name_mkStr1(v___x_5771_);
                crate::leanh::lean_inc(v___x_5787_);
                crate::leanh::lean_inc(v_mvarId_5772_);
                v___x_5788_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_5772_,
                    v___x_5787_,
                    v___y_5783_,
                    v___y_5784_,
                    v___y_5785_,
                    v___y_5786_,
                );
                if crate::leanh::lean_obj_tag(v___x_5788_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_5788_, 1);
                    crate::leanh::lean_inc(v_majorFVarId_5773_);
                    v___x_5789_ = l_Lean_FVarId_getDecl___redArg(
                        v_majorFVarId_5773_,
                        v___y_5783_,
                        v___y_5785_,
                        v___y_5786_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5789_) == 0 {
                        v_a_5790_ = crate::leanh::lean_ctor_get(v___x_5789_, 0);
                        crate::leanh::lean_inc(v_a_5790_);
                        crate::leanh::lean_dec_ref_known(v___x_5789_, 1);
                        v___x_5791_ = crate::leanh::lean_box(0);
                        crate::leanh::lean_inc(v_recursorName_5774_);
                        v___x_5792_ = l_Lean_Meta_mkRecursorInfo(
                            v_recursorName_5774_,
                            v___x_5791_,
                            v___y_5783_,
                            v___y_5784_,
                            v___y_5785_,
                            v___y_5786_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_5792_) == 0 {
                            v_a_5793_ = crate::leanh::lean_ctor_get(v___x_5792_, 0);
                            crate::leanh::lean_inc(v_a_5793_);
                            crate::leanh::lean_dec_ref_known(v___x_5792_, 1);
                            v_typeName_5794_ = crate::leanh::lean_ctor_get(v_a_5793_, 1);
                            v___x_5795_ = l_Lean_LocalDecl_type(v_a_5790_);
                            crate::leanh::lean_dec(v_a_5790_);
                            crate::leanh::lean_inc_ref(v___x_5795_);
                            v___x_5796_ = l_Lean_Meta_whnfUntil(
                                v___x_5795_,
                                v_typeName_5794_,
                                v___y_5783_,
                                v___y_5784_,
                                v___y_5785_,
                                v___y_5786_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_5796_) == 0 {
                                v_a_5797_ = crate::leanh::lean_ctor_get(v___x_5796_, 0);
                                crate::leanh::lean_inc(v_a_5797_);
                                crate::leanh::lean_dec_ref_known(v___x_5796_, 1);
                                if crate::leanh::lean_obj_tag(v_a_5797_) == 1 {
                                    crate::leanh::lean_dec_ref(v___x_5795_);
                                    crate::leanh::lean_dec(v___x_5787_);
                                    v_val_5798_ = crate::leanh::lean_ctor_get(v_a_5797_, 0);
                                    crate::leanh::lean_inc_n(v_val_5798_, 2);
                                    crate::leanh::lean_dec_ref_known(v_a_5797_, 1);
                                    v_dummy_5799_ = crate::leanh::lean_obj_once(
                                        core::ptr::addr_of_mut!(
                                            l_Lean_Meta_getMajorTypeIndices___closed__0
                                        ),
                                        core::ptr::addr_of_mut!(
                                            l_Lean_Meta_getMajorTypeIndices___closed__0_once
                                        ),
                                        _init_l_Lean_Meta_getMajorTypeIndices___closed__0,
                                    );
                                    v_nargs_5800_ = l_Lean_Expr_getAppNumArgs(v_val_5798_);
                                    crate::leanh::lean_inc(v_nargs_5800_);
                                    v___x_5801_ = lean_mk_array(v_nargs_5800_, v_dummy_5799_);
                                    v___x_5802_ = crate::leanh::lean_unsigned_to_nat(1);
                                    v___x_5803_ = lean_nat_sub(v_nargs_5800_, v___x_5802_);
                                    crate::leanh::lean_dec(v_nargs_5800_);
                                    v___x_5804_ = l_Lean_Expr_withAppAux___at___00Lean_MVarId_induction_spec__4(v_val_5798_, v_mvarId_5772_, v_a_5793_, v_majorFVarId_5773_, v_givenNames_5775_, v_recursorName_5774_, v_val_5798_, v___x_5801_, v___x_5803_, v___y_5783_, v___y_5784_, v___y_5785_, v___y_5786_);
                                    crate::leanh::lean_dec(v___x_5803_);
                                    return v___x_5804_;
                                } else {
                                    crate::leanh::lean_dec(v_a_5797_);
                                    crate::leanh::lean_dec(v_a_5793_);
                                    crate::leanh::lean_dec_ref(v_givenNames_5775_);
                                    crate::leanh::lean_dec(v_recursorName_5774_);
                                    crate::leanh::lean_dec(v_majorFVarId_5773_);
                                    v___x_5805_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___redArg(v___x_5787_, v_mvarId_5772_, v___x_5795_, v___y_5783_, v___y_5784_, v___y_5785_, v___y_5786_);
                                    return v___x_5805_;
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v___x_5795_);
                                crate::leanh::lean_dec(v_a_5793_);
                                crate::leanh::lean_dec(v___x_5787_);
                                crate::leanh::lean_dec_ref(v_givenNames_5775_);
                                crate::leanh::lean_dec(v_recursorName_5774_);
                                crate::leanh::lean_dec(v_majorFVarId_5773_);
                                crate::leanh::lean_dec(v_mvarId_5772_);
                                v_a_5806_ = crate::leanh::lean_ctor_get(v___x_5796_, 0);
                                v_isSharedCheck_5813_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5796_)) as u8;
                                if v_isSharedCheck_5813_ == 0 {
                                    v___x_5808_ = v___x_5796_;
                                    v_isShared_5809_ = v_isSharedCheck_5813_;
                                    state = 2;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5806_);
                                    crate::leanh::lean_dec(v___x_5796_);
                                    v___x_5808_ = crate::leanh::lean_box(0);
                                    v_isShared_5809_ = v_isSharedCheck_5813_;
                                    state = 2;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_5790_);
                            crate::leanh::lean_dec(v___x_5787_);
                            crate::leanh::lean_dec_ref(v_givenNames_5775_);
                            crate::leanh::lean_dec(v_recursorName_5774_);
                            crate::leanh::lean_dec(v_majorFVarId_5773_);
                            crate::leanh::lean_dec(v_mvarId_5772_);
                            v_a_5814_ = crate::leanh::lean_ctor_get(v___x_5792_, 0);
                            v_isSharedCheck_5821_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5792_)) as u8;
                            if v_isSharedCheck_5821_ == 0 {
                                v___x_5816_ = v___x_5792_;
                                v_isShared_5817_ = v_isSharedCheck_5821_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5814_);
                                crate::leanh::lean_dec(v___x_5792_);
                                v___x_5816_ = crate::leanh::lean_box(0);
                                v_isShared_5817_ = v_isSharedCheck_5821_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_5787_);
                        crate::leanh::lean_dec_ref(v_givenNames_5775_);
                        crate::leanh::lean_dec(v_recursorName_5774_);
                        crate::leanh::lean_dec(v_majorFVarId_5773_);
                        crate::leanh::lean_dec(v_mvarId_5772_);
                        v_a_5822_ = crate::leanh::lean_ctor_get(v___x_5789_, 0);
                        v_isSharedCheck_5829_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5789_)) as u8;
                        if v_isSharedCheck_5829_ == 0 {
                            v___x_5824_ = v___x_5789_;
                            v_isShared_5825_ = v_isSharedCheck_5829_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5822_);
                            crate::leanh::lean_dec(v___x_5789_);
                            v___x_5824_ = crate::leanh::lean_box(0);
                            v_isShared_5825_ = v_isSharedCheck_5829_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_5787_);
                    crate::leanh::lean_dec_ref(v_givenNames_5775_);
                    crate::leanh::lean_dec(v_recursorName_5774_);
                    crate::leanh::lean_dec(v_majorFVarId_5773_);
                    crate::leanh::lean_dec(v_mvarId_5772_);
                    v_a_5830_ = crate::leanh::lean_ctor_get(v___x_5788_, 0);
                    v_isSharedCheck_5837_ = (!crate::leanh::lean_is_exclusive(v___x_5788_)) as u8;
                    if v_isSharedCheck_5837_ == 0 {
                        v___x_5832_ = v___x_5788_;
                        v_isShared_5833_ = v_isSharedCheck_5837_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5830_);
                        crate::leanh::lean_dec(v___x_5788_);
                        v___x_5832_ = crate::leanh::lean_box(0);
                        v_isShared_5833_ = v_isSharedCheck_5837_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_5809_ == 0 {
                    v___x_5811_ = v___x_5808_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5812_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5812_, 0, v_a_5806_);
                    v___x_5811_ = v_reuseFailAlloc_5812_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5811_;
            }
            4 => {
                if v_isShared_5817_ == 0 {
                    v___x_5819_ = v___x_5816_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5820_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5820_, 0, v_a_5814_);
                    v___x_5819_ = v_reuseFailAlloc_5820_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5819_;
            }
            6 => {
                if v_isShared_5825_ == 0 {
                    v___x_5827_ = v___x_5824_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5828_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5828_, 0, v_a_5822_);
                    v___x_5827_ = v_reuseFailAlloc_5828_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5827_;
            }
            8 => {
                if v_isShared_5833_ == 0 {
                    v___x_5835_ = v___x_5832_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5836_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5836_, 0, v_a_5830_);
                    v___x_5835_ = v_reuseFailAlloc_5836_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5835_;
            }
            10 => {
                if v_isShared_5851_ == 0 {
                    v___x_5853_ = v___x_5850_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5854_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5854_, 0, v_a_5848_);
                    v___x_5853_ = v_reuseFailAlloc_5854_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_5853_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_induction___lam__0___boxed(
    mut v___x_5856_: *mut crate::leanh::LeanObject,
    mut v_mvarId_5857_: *mut crate::leanh::LeanObject,
    mut v_majorFVarId_5858_: *mut crate::leanh::LeanObject,
    mut v_recursorName_5859_: *mut crate::leanh::LeanObject,
    mut v_givenNames_5860_: *mut crate::leanh::LeanObject,
    mut v_cls_5861_: *mut crate::leanh::LeanObject,
    mut v___y_5862_: *mut crate::leanh::LeanObject,
    mut v___y_5863_: *mut crate::leanh::LeanObject,
    mut v___y_5864_: *mut crate::leanh::LeanObject,
    mut v___y_5865_: *mut crate::leanh::LeanObject,
    mut v___y_5866_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5867_ = l_Lean_MVarId_induction___lam__0(
        v___x_5856_,
        v_mvarId_5857_,
        v_majorFVarId_5858_,
        v_recursorName_5859_,
        v_givenNames_5860_,
        v_cls_5861_,
        v___y_5862_,
        v___y_5863_,
        v___y_5864_,
        v___y_5865_,
    );
    crate::leanh::lean_dec(v___y_5865_);
    crate::leanh::lean_dec_ref(v___y_5864_);
    crate::leanh::lean_dec(v___y_5863_);
    crate::leanh::lean_dec_ref(v___y_5862_);
    return v_res_5867_;
}
pub unsafe fn l_Lean_MVarId_induction(
    mut v_mvarId_5868_: *mut crate::leanh::LeanObject,
    mut v_majorFVarId_5869_: *mut crate::leanh::LeanObject,
    mut v_recursorName_5870_: *mut crate::leanh::LeanObject,
    mut v_givenNames_5871_: *mut crate::leanh::LeanObject,
    mut v_a_5872_: *mut crate::leanh::LeanObject,
    mut v_a_5873_: *mut crate::leanh::LeanObject,
    mut v_a_5874_: *mut crate::leanh::LeanObject,
    mut v_a_5875_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cls_5878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5877_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__0;
    v_cls_5878_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2;
    crate::leanh::lean_inc(v_mvarId_5868_);
    v___f_5879_ = crate::leanh::lean_alloc_closure(
        l_Lean_MVarId_induction___lam__0___boxed as *mut core::ffi::c_void,
        11,
        6,
    );
    crate::leanh::lean_closure_set(v___f_5879_, 0, v___x_5877_);
    crate::leanh::lean_closure_set(v___f_5879_, 1, v_mvarId_5868_);
    crate::leanh::lean_closure_set(v___f_5879_, 2, v_majorFVarId_5869_);
    crate::leanh::lean_closure_set(v___f_5879_, 3, v_recursorName_5870_);
    crate::leanh::lean_closure_set(v___f_5879_, 4, v_givenNames_5871_);
    crate::leanh::lean_closure_set(v___f_5879_, 5, v_cls_5878_);
    v___x_5880_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_induction_spec__3___redArg(
        v_mvarId_5868_,
        v___f_5879_,
        v_a_5872_,
        v_a_5873_,
        v_a_5874_,
        v_a_5875_,
    );
    return v___x_5880_;
}
pub unsafe fn l_Lean_MVarId_induction___boxed(
    mut v_mvarId_5881_: *mut crate::leanh::LeanObject,
    mut v_majorFVarId_5882_: *mut crate::leanh::LeanObject,
    mut v_recursorName_5883_: *mut crate::leanh::LeanObject,
    mut v_givenNames_5884_: *mut crate::leanh::LeanObject,
    mut v_a_5885_: *mut crate::leanh::LeanObject,
    mut v_a_5886_: *mut crate::leanh::LeanObject,
    mut v_a_5887_: *mut crate::leanh::LeanObject,
    mut v_a_5888_: *mut crate::leanh::LeanObject,
    mut v_a_5889_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5890_ = l_Lean_MVarId_induction(
        v_mvarId_5881_,
        v_majorFVarId_5882_,
        v_recursorName_5883_,
        v_givenNames_5884_,
        v_a_5885_,
        v_a_5886_,
        v_a_5887_,
        v_a_5888_,
    );
    crate::leanh::lean_dec(v_a_5888_);
    crate::leanh::lean_dec_ref(v_a_5887_);
    crate::leanh::lean_dec(v_a_5886_);
    crate::leanh::lean_dec_ref(v_a_5885_);
    return v_res_5890_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5938_ = crate::leanh::lean_unsigned_to_nat(2221195325);
    v___x_5939_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_;
    v___x_5940_ = l_Lean_Name_num___override(v___x_5939_, v___x_5938_);
    return v___x_5940_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5942_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_;
    v___x_5943_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_);
    v___x_5944_ = l_Lean_Name_str___override(v___x_5943_, v___x_5942_);
    return v___x_5944_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5946_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_;
    v___x_5947_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_);
    v___x_5948_ = l_Lean_Name_str___override(v___x_5947_, v___x_5946_);
    return v___x_5948_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5949_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_5950_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_);
    v___x_5951_ = l_Lean_Name_num___override(v___x_5950_, v___x_5949_);
    return v___x_5951_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5954_: u8 = 0;
    let mut v___x_5955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5953_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___closed__2;
    v___x_5954_ = 0;
    v___x_5955_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_);
    v___x_5956_ = l_Lean_registerTraceClass(v___x_5953_, v___x_5954_, v___x_5955_);
    return v___x_5956_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2____boxed(
    mut v_a_5957_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5958_ = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_();
    return v_res_5958_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Induction(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_RecursorInfo(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_SynthInstance(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Revert(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Intro(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_FVarSubst(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_WHNF(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Induction_2221195325____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Induction(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Induction(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_RecursorInfo(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_SynthInstance(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Revert(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Intro(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_FVarSubst(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_WHNF(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Induction(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Induction(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Induction(builtin);
}
