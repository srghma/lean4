// Lean compiler output
// Module: Lean.Elab.Tactic.Do.ProofMode.Pure
// Imports: Lean.Elab.Tactic.Do.ProofMode.MGoal Lean.Elab.Tactic.Meta Lean.Elab.Tactic.Do.ProofMode.Basic Lean.Elab.Tactic.Do.ProofMode.Focus Lean.Meta.Tactic.Rfl
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_mkStr2, l_Lean_Name_mkStr6, l_Lean_SourceInfo_fromRef,
    l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind, l_Lean_Syntax_node1,
};
use crate::r#gen::Lean::CoreM::l_Lean_Exception_isRuntime;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    l_Lean_Elab_Tactic_replaceMainGoal___redArg, l_Lean_Elab_Tactic_tacticElabAttribute,
};
use crate::r#gen::Lean::Elab::Tactic::Do::ProofMode::Basic::{
    initialize_Lean_Elab_Tactic_Do_ProofMode_Basic,
    l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg,
    runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Basic,
};
use crate::r#gen::Lean::Elab::Tactic::Do::ProofMode::Focus::{
    initialize_Lean_Elab_Tactic_Do_ProofMode_Focus,
    l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_restGoal,
    l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_rewriteHyps,
    l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo,
    runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Focus,
};
use crate::r#gen::Lean::Elab::Tactic::Do::ProofMode::MGoal::{
    initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal, l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr,
    l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21,
    l_Lean_Elab_Tactic_Do_ProofMode_TypeList_length,
    l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo,
    l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___boxed,
    l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName,
    runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal,
};
use crate::r#gen::Lean::Elab::Tactic::Meta::{
    initialize_Lean_Elab_Tactic_Meta, l_Lean_Elab_runTactic,
    runtime_initialize_Lean_Elab_Tactic_Meta,
};
use crate::r#gen::Lean::Exception::l_Lean_Exception_isInterrupt;
use crate::r#gen::Lean::Expr::{
    l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux, l_Lean_Expr_appArg_x21,
    l_Lean_Expr_appFn_x21, l_Lean_Expr_getAppFn, l_Lean_Expr_getAppNumArgs, l_Lean_Expr_isAppOf,
    l_Lean_Expr_isAppOfArity, l_Lean_Expr_isConstOf, l_Lean_Expr_mvarId_x21,
    l_Lean_Expr_sort___override, l_Lean_instBEqMVarId_beq, l_Lean_instHashableMVarId_hash,
    l_Lean_instInhabitedExpr, l_Lean_mkApp3, l_Lean_mkApp4, l_Lean_mkApp6, l_Lean_mkApp7,
    l_Lean_mkConst, l_Lean_mkSort,
};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Message::{l_Lean_MessageData_ofExpr, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp, l_Lean_MVarId_setType___redArg,
    l_Lean_Meta_instantiateMVarsIfMVarApp___redArg, l_Lean_Meta_mkFreshExprMVar,
    l_Lean_Meta_mkFreshExprMVar___boxed, l_Lean_Meta_mkFreshLevelMVar,
    l_Lean_Meta_mkFreshLevelMVar___boxed, l_Lean_Meta_mkLambdaFVars,
    l_Lean_Meta_mkLambdaFVars___boxed, l_Lean_Meta_withLocalDeclD___redArg,
};
use crate::r#gen::Lean::Meta::SynthInstance::{
    l_Lean_Meta_synthInstance, l_Lean_Meta_synthInstance___boxed,
};
use crate::r#gen::Lean::Meta::Tactic::Rfl::{
    initialize_Lean_Meta_Tactic_Rfl, l_Lean_MVarId_applyRfl,
    runtime_initialize_Lean_Meta_Tactic_Rfl,
};
use crate::r#gen::Lean::Meta::Tactic::Util::{
    l_Lean_MVarId_getTag, l_Lean_MVarId_getType, l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar,
};
use crate::r#gen::Lean::Util::Trace::l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go;
use crate::ffi::lean_mk_array;
use crate::ffi::lean_array_fset;
use crate::ffi::{
    lean_uint64_to_usize, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right,
};
use crate::ffi::{
    lean_usize_add, lean_usize_dec_le, lean_usize_sub, lean_usize_to_nat,
};
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_size,
    lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_lt, lean_nat_sub,
};
use crate::ffi::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__2___closed__0_value:
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
    m_data: [80, 117, 114, 101, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__2___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__2___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__2___closed__1_value:
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
    m_data: [116, 104, 109, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__2___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__2___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__0_value:
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
    m_data: [83, 116, 100, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__1_value:
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
    m_data: [68, 111, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__2_value:
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
    m_data: [83, 80, 114, 101, 100, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__3_value:
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__4_value:
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
    m_data: [73, 115, 80, 117, 114, 101, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__4_value
) as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__5_value_aux_0:
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
            l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__5_value_aux_1:
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
            l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__5_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        7300584325018775040 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__5_value_aux_2:
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
            l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__5_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        13332341187416043682 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__5_value_aux_3:
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
            l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__5_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__3_value
        ) as *mut crate::leanh::LeanObject,
        18104247681175793831 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__5_value:
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
            l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__5_value_aux_3
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__4_value
        ) as *mut crate::leanh::LeanObject,
        18273640022974733293 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__5_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___closed__0_value:
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
    m_fun: l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___closed__1_value:
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
    m_fun: l_Lean_Meta_mkFreshLevelMVar___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___lam__1___closed__0_value:
    crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [98, 105, 110, 100, 101, 114, 73, 100, 101, 110, 116, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___lam__1___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___lam__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___closed__0_value:
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
    m_data: [76, 101, 97, 110, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___closed__1_value:
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
    m_data: [80, 97, 114, 115, 101, 114, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___closed__2_value:
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
    m_data: [109, 112, 117, 114, 101, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___closed__3_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___closed__3_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___closed__3_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___closed__3_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___closed__3_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__3_value
        ) as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___closed__3_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___closed__3_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___closed__2_value)
            as *mut crate::leanh::LeanObject,
        11776213983848966243 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPure__1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPure__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPure__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPure__1___closed__1_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [80, 114, 111, 111, 102, 77, 111, 100, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPure__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPure__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPure__1___closed__2_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [101, 108, 97, 98, 77, 80, 117, 114, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPure__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPure__1___closed__2_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPure__1___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPure__1___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPure__1___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPure__1___closed__0_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPure__1___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPure__1___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__3_value) as *mut crate::leanh::LeanObject,12733524109236233889 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPure__1___closed__3_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPure__1___closed__3_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__1_value) as *mut crate::leanh::LeanObject,11384710337598098789 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPure__1___closed__3_value_aux_4: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPure__1___closed__3_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPure__1___closed__1_value) as *mut crate::leanh::LeanObject,5427134421608450815 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPure__1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPure__1___closed__3_value_aux_4) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPure__1___closed__2_value) as *mut crate::leanh::LeanObject,5369621593861005361 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPure__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPure__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___redArg___lam__0___closed__0_value:
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___redArg___lam__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___redArg___lam__0___closed__0_value
) as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro_spec__0___redArg___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro_spec__0___redArg___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro_spec__0___redArg___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__1_value) as *mut crate::leanh::LeanObject,7300584325018775040 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro_spec__0___redArg___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro_spec__0___redArg___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__2_value) as *mut crate::leanh::LeanObject,13332341187416043682 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro_spec__0___redArg___closed__0_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro_spec__0___redArg___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__3_value) as *mut crate::leanh::LeanObject,18104247681175793831 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro_spec__0___redArg___closed__0_value_aux_4: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro_spec__0___redArg___closed__0_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__2___closed__0_value) as *mut crate::leanh::LeanObject,8898716429925661309 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro_spec__0___redArg___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro_spec__0___redArg___closed__0_value_aux_4) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___redArg___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,8489233108392429046 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___closed__0_value:
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
    m_data: [109, 112, 117, 114, 101, 73, 110, 116, 114, 111, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___closed__1_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___closed__1_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__3_value
        ) as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___closed__0_value)
            as *mut crate::leanh::LeanObject,
        14584075201508774244 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro__1___closed__0_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [101, 108, 97, 98, 77, 80, 117, 114, 101, 73, 110, 116, 114, 111, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPure__1___closed__0_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__3_value) as *mut crate::leanh::LeanObject,12733524109236233889 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro__1___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__1_value) as *mut crate::leanh::LeanObject,11384710337598098789 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro__1___closed__1_value_aux_4: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro__1___closed__1_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPure__1___closed__1_value) as *mut crate::leanh::LeanObject,5427134421608450815 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro__1___closed__1_value_aux_4) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro__1___closed__0_value) as *mut crate::leanh::LeanObject,13685130571082086932 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [85, 76, 105, 102, 116, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___closed__1_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [100, 111, 119, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___closed__1_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___closed__0_value) as *mut crate::leanh::LeanObject,4110003850811318798 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___closed__1_value) as *mut crate::leanh::LeanObject,16526823145974595592 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___closed__3_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [112, 117, 114, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___closed__3_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__1_value) as *mut crate::leanh::LeanObject,7300584325018775040 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__2_value) as *mut crate::leanh::LeanObject,13332341187416043682 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___closed__4_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___closed__3_value) as *mut crate::leanh::LeanObject,7100147834070349651 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1___closed__1_value:
    crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 1,
    m_capacity: 1,
    m_length: 0,
    m_data: [0],
};
static mut l_Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1___closed__2_value:
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
static mut l_Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_applyRflAndAndIntro___closed__0_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
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
static mut l_Lean_MVarId_applyRflAndAndIntro___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_applyRflAndAndIntro___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_applyRflAndAndIntro___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_MVarId_applyRflAndAndIntro___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11870096045526947150 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_applyRflAndAndIntro___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_applyRflAndAndIntro___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_applyRflAndAndIntro___closed__2_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
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
static mut l_Lean_MVarId_applyRflAndAndIntro___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_applyRflAndAndIntro___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_applyRflAndAndIntro___closed__3_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_MVarId_applyRflAndAndIntro___closed__2_value)
                as *mut crate::leanh::LeanObject,
            9743492140944907313 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_applyRflAndAndIntro___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_applyRflAndAndIntro___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_MVarId_applyRflAndAndIntro___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_MVarId_applyRflAndAndIntro___closed__2_value)
                as *mut crate::leanh::LeanObject,
            9743492140944907313 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_MVarId_applyRflAndAndIntro___closed__4_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_MVarId_applyRflAndAndIntro___closed__4_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(
                l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___redArg___lam__0___closed__0_value
            ) as *mut crate::leanh::LeanObject,
            11695081953491693114 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_applyRflAndAndIntro___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_applyRflAndAndIntro___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_MVarId_applyRflAndAndIntro___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_applyRflAndAndIntro___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static l_Lean_MVarId_applyRflAndAndIntro___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_MVarId_applyRflAndAndIntro___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11870096045526947150 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_MVarId_applyRflAndAndIntro___closed__6_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_MVarId_applyRflAndAndIntro___closed__6_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(
                l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___redArg___lam__0___closed__0_value
            ) as *mut crate::leanh::LeanObject,
            18067798339771668657 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_applyRflAndAndIntro___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_applyRflAndAndIntro___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_MVarId_applyRflAndAndIntro___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_applyRflAndAndIntro___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_MVarId_applyRflAndAndIntro___closed__8_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [115, 112, 101, 99, 0],
    };
static mut l_Lean_MVarId_applyRflAndAndIntro___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_applyRflAndAndIntro___closed__8_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_MVarId_applyRflAndAndIntro___closed__9_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPure__1___closed__0_value) as *mut crate::leanh::LeanObject,12843180897352504333 as *mut crate::leanh::LeanObject] };
static l_Lean_MVarId_applyRflAndAndIntro___closed__9_value_aux_1: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_MVarId_applyRflAndAndIntro___closed__9_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(
                l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__3_value
            ) as *mut crate::leanh::LeanObject,
            17186385980065365684 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_MVarId_applyRflAndAndIntro___closed__9_value_aux_2: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_MVarId_applyRflAndAndIntro___closed__9_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(
                l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__1_value
            ) as *mut crate::leanh::LeanObject,
            6272605754531080404 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_MVarId_applyRflAndAndIntro___closed__9_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_MVarId_applyRflAndAndIntro___closed__9_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_MVarId_applyRflAndAndIntro___closed__8_value)
                as *mut crate::leanh::LeanObject,
            17629337176996777627 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_applyRflAndAndIntro___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_applyRflAndAndIntro___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_applyRflAndAndIntro___closed__10_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
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
static mut l_Lean_MVarId_applyRflAndAndIntro___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_applyRflAndAndIntro___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_applyRflAndAndIntro___closed__11_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_MVarId_applyRflAndAndIntro___closed__10_value)
                as *mut crate::leanh::LeanObject,
            14231257465488249300 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_applyRflAndAndIntro___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_applyRflAndAndIntro___closed__11_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_MVarId_applyRflAndAndIntro___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_applyRflAndAndIntro___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_MVarId_applyRflAndAndIntro___closed__13_value: crate::leanh::LeanStringObject<
    12,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [112, 117, 114, 101, 32, 80, 114, 111, 112, 58, 32, 0],
};
static mut l_Lean_MVarId_applyRflAndAndIntro___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_applyRflAndAndIntro___closed__13_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_MVarId_applyRflAndAndIntro___closed__14_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_applyRflAndAndIntro___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro_spec__0___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__1___closed__0_value:
    crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [100, 105, 115, 99, 104, 97, 114, 103, 101, 100, 58, 32, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__1___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__1___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__1___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__1___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__1___closed__2_value:
    crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [100, 105, 115, 99, 104, 97, 114, 103, 101, 63, 32, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__1___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__1___closed__2_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__1___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__1___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___closed__0_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_MVarId_applyRflAndAndIntro___closed__9_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___closed__1_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_MVarId_applyRflAndAndIntro___closed__9_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___closed__2_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        112, 117, 114, 101, 82, 102, 108, 65, 110, 100, 65, 110, 100, 73, 110, 116, 114, 111, 58,
        32, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__1___closed__0_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        116, 97, 99, 116, 105, 99, 84, 114, 105, 118, 105, 97, 108, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__1___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__1___closed__0_value
) as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__1___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__1___closed__1_value_aux_1:
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
            l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__1___closed__1_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__1___closed__1_value_aux_2:
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
            l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__1___closed__1_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__3_value
        ) as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__1___closed__1_value:
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
            l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__1___closed__1_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__1___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        2766452847008772443 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__1___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__1___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__1___closed__2_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [116, 114, 105, 118, 105, 97, 108, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__1___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__1___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__1___closed__3_value:
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__1___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__1___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__1___closed__4_value:
    crate::leanh::LeanCtorObject<7> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7
            + 0) as u16,
        other: 7,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__1___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__1___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___closed__0_value:
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
    m_fun: l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__0(
    mut v___y_2581_: *mut crate::leanh::LeanObject,
    mut v___y_2582_: *mut crate::leanh::LeanObject,
    mut v___y_2583_: *mut crate::leanh::LeanObject,
    mut v___y_2584_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lctx_2586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lctx_2586_ = crate::leanh::lean_ctor_get(v___y_2581_, 2);
    crate::leanh::lean_inc_ref(v_lctx_2586_);
    v___x_2587_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2587_, 0, v_lctx_2586_);
    return v___x_2587_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__0___boxed(
    mut v___y_2588_: *mut crate::leanh::LeanObject,
    mut v___y_2589_: *mut crate::leanh::LeanObject,
    mut v___y_2590_: *mut crate::leanh::LeanObject,
    mut v___y_2591_: *mut crate::leanh::LeanObject,
    mut v___y_2592_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2593_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__0(
        v___y_2588_,
        v___y_2589_,
        v___y_2590_,
        v___y_2591_,
    );
    crate::leanh::lean_dec(v___y_2591_);
    crate::leanh::lean_dec_ref(v___y_2590_);
    crate::leanh::lean_dec(v___y_2589_);
    crate::leanh::lean_dec_ref(v___y_2588_);
    return v_res_2593_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__1(
    mut v_name_2594_: *mut crate::leanh::LeanObject,
    mut v___y_2595_: *mut crate::leanh::LeanObject,
    mut v___y_2596_: *mut crate::leanh::LeanObject,
    mut v___y_2597_: *mut crate::leanh::LeanObject,
    mut v___y_2598_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2600_ =
        l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName(v_name_2594_, v___y_2597_, v___y_2598_);
    return v___x_2600_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__1___boxed(
    mut v_name_2601_: *mut crate::leanh::LeanObject,
    mut v___y_2602_: *mut crate::leanh::LeanObject,
    mut v___y_2603_: *mut crate::leanh::LeanObject,
    mut v___y_2604_: *mut crate::leanh::LeanObject,
    mut v___y_2605_: *mut crate::leanh::LeanObject,
    mut v___y_2606_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2607_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__1(
        v_name_2601_,
        v___y_2602_,
        v___y_2603_,
        v___y_2604_,
        v___y_2605_,
    );
    crate::leanh::lean_dec(v___y_2605_);
    crate::leanh::lean_dec_ref(v___y_2604_);
    crate::leanh::lean_dec(v___y_2603_);
    crate::leanh::lean_dec_ref(v___y_2602_);
    return v_res_2607_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__2(
    mut v_fst_2610_: *mut crate::leanh::LeanObject,
    mut v___x_2611_: *mut crate::leanh::LeanObject,
    mut v___x_2612_: *mut crate::leanh::LeanObject,
    mut v___x_2613_: *mut crate::leanh::LeanObject,
    mut v___x_2614_: *mut crate::leanh::LeanObject,
    mut v___x_2615_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3s_2616_: *mut crate::leanh::LeanObject,
    mut v_hyp_2617_: *mut crate::leanh::LeanObject,
    mut v_00_u03c6_2618_: *mut crate::leanh::LeanObject,
    mut v_inst_2619_: *mut crate::leanh::LeanObject,
    mut v_u_2620_: *mut crate::leanh::LeanObject,
    mut v_fst_2621_: *mut crate::leanh::LeanObject,
    mut v_toPure_2622_: *mut crate::leanh::LeanObject,
    mut v_prf_2623_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_u_2624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_00_u03c3s_2625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hyps_2626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_2627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2630_: u8 = 0;
    let mut v___x_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_prf_2635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_goal_2638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2643_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_u_2624_ = crate::leanh::lean_ctor_get(v_fst_2610_, 0);
                v_00_u03c3s_2625_ = crate::leanh::lean_ctor_get(v_fst_2610_, 1);
                v_hyps_2626_ = crate::leanh::lean_ctor_get(v_fst_2610_, 2);
                v_target_2627_ = crate::leanh::lean_ctor_get(v_fst_2610_, 3);
                v_isSharedCheck_2643_ = (!crate::leanh::lean_is_exclusive(v_fst_2610_)) as u8;
                if v_isSharedCheck_2643_ == 0 {
                    v___x_2629_ = v_fst_2610_;
                    v_isShared_2630_ = v_isSharedCheck_2643_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_target_2627_);
                    crate::leanh::lean_inc(v_hyps_2626_);
                    crate::leanh::lean_inc(v_00_u03c3s_2625_);
                    crate::leanh::lean_inc(v_u_2624_);
                    crate::leanh::lean_dec(v_fst_2610_);
                    v___x_2629_ = crate::leanh::lean_box(0);
                    v_isShared_2630_ = v_isSharedCheck_2643_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2631_ =
                    l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__2___closed__0;
                v___x_2632_ =
                    l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__2___closed__1;
                v___x_2633_ = l_Lean_Name_mkStr6(
                    v___x_2611_,
                    v___x_2612_,
                    v___x_2613_,
                    v___x_2614_,
                    v___x_2631_,
                    v___x_2632_,
                );
                v___x_2634_ = l_Lean_mkConst(v___x_2633_, v___x_2615_);
                crate::leanh::lean_inc_ref(v_target_2627_);
                crate::leanh::lean_inc_ref(v_hyp_2617_);
                crate::leanh::lean_inc_ref(v_hyps_2626_);
                crate::leanh::lean_inc_ref(v_00_u03c3s_2616_);
                v_prf_2635_ = l_Lean_mkApp7(
                    v___x_2634_,
                    v_00_u03c3s_2616_,
                    v_hyps_2626_,
                    v_hyp_2617_,
                    v_target_2627_,
                    v_00_u03c6_2618_,
                    v_inst_2619_,
                    v_prf_2623_,
                );
                v___x_2636_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(
                    v_u_2620_,
                    v_00_u03c3s_2616_,
                    v_hyps_2626_,
                    v_hyp_2617_,
                );
                if v_isShared_2630_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2629_, 2, v___x_2636_);
                    v_goal_2638_ = v___x_2629_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2642_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2642_, 0, v_u_2624_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2642_, 1, v_00_u03c3s_2625_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2642_, 2, v___x_2636_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2642_, 3, v_target_2627_);
                    v_goal_2638_ = v_reuseFailAlloc_2642_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2639_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2639_, 0, v_goal_2638_);
                crate::leanh::lean_ctor_set(v___x_2639_, 1, v_prf_2635_);
                v___x_2640_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2640_, 0, v_fst_2621_);
                crate::leanh::lean_ctor_set(v___x_2640_, 1, v___x_2639_);
                v___x_2641_ = crate::leanh::lean_apply_2(
                    v_toPure_2622_,
                    crate::leanh::lean_box(0),
                    v___x_2640_,
                );
                return v___x_2641_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__3(
    mut v___x_2644_: *mut crate::leanh::LeanObject,
    mut v___x_2645_: *mut crate::leanh::LeanObject,
    mut v___x_2646_: *mut crate::leanh::LeanObject,
    mut v___x_2647_: *mut crate::leanh::LeanObject,
    mut v___x_2648_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3s_2649_: *mut crate::leanh::LeanObject,
    mut v_hyp_2650_: *mut crate::leanh::LeanObject,
    mut v_00_u03c6_2651_: *mut crate::leanh::LeanObject,
    mut v_inst_2652_: *mut crate::leanh::LeanObject,
    mut v_u_2653_: *mut crate::leanh::LeanObject,
    mut v_toPure_2654_: *mut crate::leanh::LeanObject,
    mut v_h_2655_: *mut crate::leanh::LeanObject,
    mut v___x_2656_: u8,
    mut v_inst_2657_: *mut crate::leanh::LeanObject,
    mut v_toBind_2658_: *mut crate::leanh::LeanObject,
    mut v_____x_2659_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_snd_2660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: u8 = 0;
    let mut v___x_2669_: u8 = 0;
    let mut v___x_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_snd_2660_ = crate::leanh::lean_ctor_get(v_____x_2659_, 1);
    crate::leanh::lean_inc(v_snd_2660_);
    v_fst_2661_ = crate::leanh::lean_ctor_get(v_____x_2659_, 0);
    crate::leanh::lean_inc(v_fst_2661_);
    crate::leanh::lean_dec_ref(v_____x_2659_);
    v_fst_2662_ = crate::leanh::lean_ctor_get(v_snd_2660_, 0);
    crate::leanh::lean_inc(v_fst_2662_);
    v_snd_2663_ = crate::leanh::lean_ctor_get(v_snd_2660_, 1);
    crate::leanh::lean_inc(v_snd_2663_);
    crate::leanh::lean_dec(v_snd_2660_);
    v___f_2664_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__2 as *mut core::ffi::c_void,
        14,
        13,
    );
    crate::leanh::lean_closure_set(v___f_2664_, 0, v_fst_2662_);
    crate::leanh::lean_closure_set(v___f_2664_, 1, v___x_2644_);
    crate::leanh::lean_closure_set(v___f_2664_, 2, v___x_2645_);
    crate::leanh::lean_closure_set(v___f_2664_, 3, v___x_2646_);
    crate::leanh::lean_closure_set(v___f_2664_, 4, v___x_2647_);
    crate::leanh::lean_closure_set(v___f_2664_, 5, v___x_2648_);
    crate::leanh::lean_closure_set(v___f_2664_, 6, v_00_u03c3s_2649_);
    crate::leanh::lean_closure_set(v___f_2664_, 7, v_hyp_2650_);
    crate::leanh::lean_closure_set(v___f_2664_, 8, v_00_u03c6_2651_);
    crate::leanh::lean_closure_set(v___f_2664_, 9, v_inst_2652_);
    crate::leanh::lean_closure_set(v___f_2664_, 10, v_u_2653_);
    crate::leanh::lean_closure_set(v___f_2664_, 11, v_fst_2661_);
    crate::leanh::lean_closure_set(v___f_2664_, 12, v_toPure_2654_);
    v___x_2665_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_2666_ = lean_mk_empty_array_with_capacity(v___x_2665_);
    v___x_2667_ = lean_array_push(v___x_2666_, v_h_2655_);
    v___x_2668_ = 1;
    v___x_2669_ = 1;
    v___x_2670_ = crate::leanh::lean_box((v___x_2656_) as usize);
    v___x_2671_ = crate::leanh::lean_box((v___x_2668_) as usize);
    v___x_2672_ = crate::leanh::lean_box((v___x_2656_) as usize);
    v___x_2673_ = crate::leanh::lean_box((v___x_2668_) as usize);
    v___x_2674_ = crate::leanh::lean_box((v___x_2669_) as usize);
    v___x_2675_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_mkLambdaFVars___boxed as *mut core::ffi::c_void,
        12,
        7,
    );
    crate::leanh::lean_closure_set(v___x_2675_, 0, v___x_2667_);
    crate::leanh::lean_closure_set(v___x_2675_, 1, v_snd_2663_);
    crate::leanh::lean_closure_set(v___x_2675_, 2, v___x_2670_);
    crate::leanh::lean_closure_set(v___x_2675_, 3, v___x_2671_);
    crate::leanh::lean_closure_set(v___x_2675_, 4, v___x_2672_);
    crate::leanh::lean_closure_set(v___x_2675_, 5, v___x_2673_);
    crate::leanh::lean_closure_set(v___x_2675_, 6, v___x_2674_);
    v___x_2676_ = crate::leanh::lean_apply_2(v_inst_2657_, crate::leanh::lean_box(0), v___x_2675_);
    v___x_2677_ = crate::leanh::lean_apply_4(
        v_toBind_2658_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2676_,
        v___f_2664_,
    );
    return v___x_2677_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__3___boxed(
    mut v___x_2678_: *mut crate::leanh::LeanObject,
    mut v___x_2679_: *mut crate::leanh::LeanObject,
    mut v___x_2680_: *mut crate::leanh::LeanObject,
    mut v___x_2681_: *mut crate::leanh::LeanObject,
    mut v___x_2682_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3s_2683_: *mut crate::leanh::LeanObject,
    mut v_hyp_2684_: *mut crate::leanh::LeanObject,
    mut v_00_u03c6_2685_: *mut crate::leanh::LeanObject,
    mut v_inst_2686_: *mut crate::leanh::LeanObject,
    mut v_u_2687_: *mut crate::leanh::LeanObject,
    mut v_toPure_2688_: *mut crate::leanh::LeanObject,
    mut v_h_2689_: *mut crate::leanh::LeanObject,
    mut v___x_2690_: *mut crate::leanh::LeanObject,
    mut v_inst_2691_: *mut crate::leanh::LeanObject,
    mut v_toBind_2692_: *mut crate::leanh::LeanObject,
    mut v_____x_2693_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_486__boxed_2694_: u8 = 0;
    let mut v_res_2695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_486__boxed_2694_ = (crate::leanh::lean_unbox(v___x_2690_) as u8);
    v_res_2695_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__3(
        v___x_2678_,
        v___x_2679_,
        v___x_2680_,
        v___x_2681_,
        v___x_2682_,
        v_00_u03c3s_2683_,
        v_hyp_2684_,
        v_00_u03c6_2685_,
        v_inst_2686_,
        v_u_2687_,
        v_toPure_2688_,
        v_h_2689_,
        v___x_486__boxed_2694_,
        v_inst_2691_,
        v_toBind_2692_,
        v_____x_2693_,
    );
    return v_res_2695_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__4(
    mut v_k_2696_: *mut crate::leanh::LeanObject,
    mut v_00_u03c6_2697_: *mut crate::leanh::LeanObject,
    mut v_h_2698_: *mut crate::leanh::LeanObject,
    mut v_toBind_2699_: *mut crate::leanh::LeanObject,
    mut v___f_2700_: *mut crate::leanh::LeanObject,
    mut v_____r_2701_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2702_ = crate::leanh::lean_apply_2(v_k_2696_, v_00_u03c6_2697_, v_h_2698_);
    v___x_2703_ = crate::leanh::lean_apply_4(
        v_toBind_2699_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2702_,
        v___f_2700_,
    );
    return v___x_2703_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__5(
    mut v_00_u03c6_2704_: *mut crate::leanh::LeanObject,
    mut v___x_2705_: *mut crate::leanh::LeanObject,
    mut v___x_2706_: *mut crate::leanh::LeanObject,
    mut v___x_2707_: *mut crate::leanh::LeanObject,
    mut v___x_2708_: *mut crate::leanh::LeanObject,
    mut v___x_2709_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3s_2710_: *mut crate::leanh::LeanObject,
    mut v_hyp_2711_: *mut crate::leanh::LeanObject,
    mut v_inst_2712_: *mut crate::leanh::LeanObject,
    mut v_u_2713_: *mut crate::leanh::LeanObject,
    mut v_toPure_2714_: *mut crate::leanh::LeanObject,
    mut v_h_2715_: *mut crate::leanh::LeanObject,
    mut v_inst_2716_: *mut crate::leanh::LeanObject,
    mut v_toBind_2717_: *mut crate::leanh::LeanObject,
    mut v_k_2718_: *mut crate::leanh::LeanObject,
    mut v_snd_2719_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2720_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: u8 = 0;
    let mut v___x_2723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref_n(v_00_u03c6_2704_, 2);
    v___x_2721_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2721_, 0, v_00_u03c6_2704_);
    v___x_2722_ = 0;
    v___x_2723_ = crate::leanh::lean_box((v___x_2722_) as usize);
    crate::leanh::lean_inc_n(v_toBind_2717_, 2);
    crate::leanh::lean_inc(v_inst_2716_);
    crate::leanh::lean_inc_ref_n(v_h_2715_, 2);
    v___f_2724_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__3___boxed
            as *mut core::ffi::c_void,
        16,
        15,
    );
    crate::leanh::lean_closure_set(v___f_2724_, 0, v___x_2705_);
    crate::leanh::lean_closure_set(v___f_2724_, 1, v___x_2706_);
    crate::leanh::lean_closure_set(v___f_2724_, 2, v___x_2707_);
    crate::leanh::lean_closure_set(v___f_2724_, 3, v___x_2708_);
    crate::leanh::lean_closure_set(v___f_2724_, 4, v___x_2709_);
    crate::leanh::lean_closure_set(v___f_2724_, 5, v_00_u03c3s_2710_);
    crate::leanh::lean_closure_set(v___f_2724_, 6, v_hyp_2711_);
    crate::leanh::lean_closure_set(v___f_2724_, 7, v_00_u03c6_2704_);
    crate::leanh::lean_closure_set(v___f_2724_, 8, v_inst_2712_);
    crate::leanh::lean_closure_set(v___f_2724_, 9, v_u_2713_);
    crate::leanh::lean_closure_set(v___f_2724_, 10, v_toPure_2714_);
    crate::leanh::lean_closure_set(v___f_2724_, 11, v_h_2715_);
    crate::leanh::lean_closure_set(v___f_2724_, 12, v___x_2723_);
    crate::leanh::lean_closure_set(v___f_2724_, 13, v_inst_2716_);
    crate::leanh::lean_closure_set(v___f_2724_, 14, v_toBind_2717_);
    v___f_2725_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__4 as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___f_2725_, 0, v_k_2718_);
    crate::leanh::lean_closure_set(v___f_2725_, 1, v_00_u03c6_2704_);
    crate::leanh::lean_closure_set(v___f_2725_, 2, v_h_2715_);
    crate::leanh::lean_closure_set(v___f_2725_, 3, v_toBind_2717_);
    crate::leanh::lean_closure_set(v___f_2725_, 4, v___f_2724_);
    v___x_2726_ = crate::leanh::lean_box((v___x_2722_) as usize);
    v___x_2727_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___boxed as *mut core::ffi::c_void,
        10,
        5,
    );
    crate::leanh::lean_closure_set(v___x_2727_, 0, v_snd_2719_);
    crate::leanh::lean_closure_set(v___x_2727_, 1, v_____do__lift_2720_);
    crate::leanh::lean_closure_set(v___x_2727_, 2, v_h_2715_);
    crate::leanh::lean_closure_set(v___x_2727_, 3, v___x_2721_);
    crate::leanh::lean_closure_set(v___x_2727_, 4, v___x_2726_);
    v___x_2728_ = crate::leanh::lean_apply_2(v_inst_2716_, crate::leanh::lean_box(0), v___x_2727_);
    v___x_2729_ = crate::leanh::lean_apply_4(
        v_toBind_2717_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2728_,
        v___f_2725_,
    );
    return v___x_2729_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__5___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_00_u03c6_2730_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v___x_2731_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v___x_2732_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v___x_2733_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v___x_2734_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___x_2735_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_00_u03c3s_2736_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_hyp_2737_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_inst_2738_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_u_2739_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_toPure_2740_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_h_2741_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_inst_2742_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_toBind_2743_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_k_2744_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_snd_2745_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_____do__lift_2746_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_res_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2747_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__5(
        v_00_u03c6_2730_,
        v___x_2731_,
        v___x_2732_,
        v___x_2733_,
        v___x_2734_,
        v___x_2735_,
        v_00_u03c3s_2736_,
        v_hyp_2737_,
        v_inst_2738_,
        v_u_2739_,
        v_toPure_2740_,
        v_h_2741_,
        v_inst_2742_,
        v_toBind_2743_,
        v_k_2744_,
        v_snd_2745_,
        v_____do__lift_2746_,
    );
    return v_res_2747_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__6(
    mut v_00_u03c6_2748_: *mut crate::leanh::LeanObject,
    mut v___x_2749_: *mut crate::leanh::LeanObject,
    mut v___x_2750_: *mut crate::leanh::LeanObject,
    mut v___x_2751_: *mut crate::leanh::LeanObject,
    mut v___x_2752_: *mut crate::leanh::LeanObject,
    mut v___x_2753_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3s_2754_: *mut crate::leanh::LeanObject,
    mut v_hyp_2755_: *mut crate::leanh::LeanObject,
    mut v_inst_2756_: *mut crate::leanh::LeanObject,
    mut v_u_2757_: *mut crate::leanh::LeanObject,
    mut v_toPure_2758_: *mut crate::leanh::LeanObject,
    mut v_inst_2759_: *mut crate::leanh::LeanObject,
    mut v_toBind_2760_: *mut crate::leanh::LeanObject,
    mut v_k_2761_: *mut crate::leanh::LeanObject,
    mut v_snd_2762_: *mut crate::leanh::LeanObject,
    mut v___f_2763_: *mut crate::leanh::LeanObject,
    mut v_h_2764_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_toBind_2760_);
    crate::leanh::lean_inc(v_inst_2759_);
    v___f_2765_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__5___boxed
            as *mut core::ffi::c_void,
        17,
        16,
    );
    crate::leanh::lean_closure_set(v___f_2765_, 0, v_00_u03c6_2748_);
    crate::leanh::lean_closure_set(v___f_2765_, 1, v___x_2749_);
    crate::leanh::lean_closure_set(v___f_2765_, 2, v___x_2750_);
    crate::leanh::lean_closure_set(v___f_2765_, 3, v___x_2751_);
    crate::leanh::lean_closure_set(v___f_2765_, 4, v___x_2752_);
    crate::leanh::lean_closure_set(v___f_2765_, 5, v___x_2753_);
    crate::leanh::lean_closure_set(v___f_2765_, 6, v_00_u03c3s_2754_);
    crate::leanh::lean_closure_set(v___f_2765_, 7, v_hyp_2755_);
    crate::leanh::lean_closure_set(v___f_2765_, 8, v_inst_2756_);
    crate::leanh::lean_closure_set(v___f_2765_, 9, v_u_2757_);
    crate::leanh::lean_closure_set(v___f_2765_, 10, v_toPure_2758_);
    crate::leanh::lean_closure_set(v___f_2765_, 11, v_h_2764_);
    crate::leanh::lean_closure_set(v___f_2765_, 12, v_inst_2759_);
    crate::leanh::lean_closure_set(v___f_2765_, 13, v_toBind_2760_);
    crate::leanh::lean_closure_set(v___f_2765_, 14, v_k_2761_);
    crate::leanh::lean_closure_set(v___f_2765_, 15, v_snd_2762_);
    v___x_2766_ = crate::leanh::lean_apply_2(v_inst_2759_, crate::leanh::lean_box(0), v___f_2763_);
    v___x_2767_ = crate::leanh::lean_apply_4(
        v_toBind_2760_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2766_,
        v___f_2765_,
    );
    return v___x_2767_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__6___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_00_u03c6_2768_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v___x_2769_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v___x_2770_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v___x_2771_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v___x_2772_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___x_2773_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_00_u03c3s_2774_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_hyp_2775_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_inst_2776_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_u_2777_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_toPure_2778_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_inst_2779_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_toBind_2780_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_k_2781_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_snd_2782_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___f_2783_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_h_2784_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_res_2785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2785_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__6(
        v_00_u03c6_2768_,
        v___x_2769_,
        v___x_2770_,
        v___x_2771_,
        v___x_2772_,
        v___x_2773_,
        v_00_u03c3s_2774_,
        v_hyp_2775_,
        v_inst_2776_,
        v_u_2777_,
        v_toPure_2778_,
        v_inst_2779_,
        v_toBind_2780_,
        v_k_2781_,
        v_snd_2782_,
        v___f_2783_,
        v_h_2784_,
    );
    return v_res_2785_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__7(
    mut v_00_u03c6_2786_: *mut crate::leanh::LeanObject,
    mut v___x_2787_: *mut crate::leanh::LeanObject,
    mut v___x_2788_: *mut crate::leanh::LeanObject,
    mut v___x_2789_: *mut crate::leanh::LeanObject,
    mut v___x_2790_: *mut crate::leanh::LeanObject,
    mut v___x_2791_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3s_2792_: *mut crate::leanh::LeanObject,
    mut v_hyp_2793_: *mut crate::leanh::LeanObject,
    mut v_inst_2794_: *mut crate::leanh::LeanObject,
    mut v_u_2795_: *mut crate::leanh::LeanObject,
    mut v_toPure_2796_: *mut crate::leanh::LeanObject,
    mut v_inst_2797_: *mut crate::leanh::LeanObject,
    mut v_toBind_2798_: *mut crate::leanh::LeanObject,
    mut v_k_2799_: *mut crate::leanh::LeanObject,
    mut v___f_2800_: *mut crate::leanh::LeanObject,
    mut v_inst_2801_: *mut crate::leanh::LeanObject,
    mut v_inst_2802_: *mut crate::leanh::LeanObject,
    mut v_____x_2803_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_2804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_2804_ = crate::leanh::lean_ctor_get(v_____x_2803_, 0);
    crate::leanh::lean_inc(v_fst_2804_);
    v_snd_2805_ = crate::leanh::lean_ctor_get(v_____x_2803_, 1);
    crate::leanh::lean_inc(v_snd_2805_);
    crate::leanh::lean_dec_ref(v_____x_2803_);
    crate::leanh::lean_inc_ref(v_00_u03c6_2786_);
    v___f_2806_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__6___boxed
            as *mut core::ffi::c_void,
        17,
        16,
    );
    crate::leanh::lean_closure_set(v___f_2806_, 0, v_00_u03c6_2786_);
    crate::leanh::lean_closure_set(v___f_2806_, 1, v___x_2787_);
    crate::leanh::lean_closure_set(v___f_2806_, 2, v___x_2788_);
    crate::leanh::lean_closure_set(v___f_2806_, 3, v___x_2789_);
    crate::leanh::lean_closure_set(v___f_2806_, 4, v___x_2790_);
    crate::leanh::lean_closure_set(v___f_2806_, 5, v___x_2791_);
    crate::leanh::lean_closure_set(v___f_2806_, 6, v_00_u03c3s_2792_);
    crate::leanh::lean_closure_set(v___f_2806_, 7, v_hyp_2793_);
    crate::leanh::lean_closure_set(v___f_2806_, 8, v_inst_2794_);
    crate::leanh::lean_closure_set(v___f_2806_, 9, v_u_2795_);
    crate::leanh::lean_closure_set(v___f_2806_, 10, v_toPure_2796_);
    crate::leanh::lean_closure_set(v___f_2806_, 11, v_inst_2797_);
    crate::leanh::lean_closure_set(v___f_2806_, 12, v_toBind_2798_);
    crate::leanh::lean_closure_set(v___f_2806_, 13, v_k_2799_);
    crate::leanh::lean_closure_set(v___f_2806_, 14, v_snd_2805_);
    crate::leanh::lean_closure_set(v___f_2806_, 15, v___f_2800_);
    v___x_2807_ = l_Lean_Meta_withLocalDeclD___redArg(
        v_inst_2801_,
        v_inst_2802_,
        v_fst_2804_,
        v_00_u03c6_2786_,
        v___f_2806_,
    );
    return v___x_2807_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__7___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_00_u03c6_2808_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v___x_2809_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v___x_2810_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v___x_2811_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v___x_2812_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___x_2813_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_00_u03c3s_2814_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_hyp_2815_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_inst_2816_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_u_2817_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_toPure_2818_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_inst_2819_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_toBind_2820_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_k_2821_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___f_2822_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_inst_2823_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_inst_2824_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_____x_2825_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_res_2826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2826_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__7(
        v_00_u03c6_2808_,
        v___x_2809_,
        v___x_2810_,
        v___x_2811_,
        v___x_2812_,
        v___x_2813_,
        v_00_u03c3s_2814_,
        v_hyp_2815_,
        v_inst_2816_,
        v_u_2817_,
        v_toPure_2818_,
        v_inst_2819_,
        v_toBind_2820_,
        v_k_2821_,
        v___f_2822_,
        v_inst_2823_,
        v_inst_2824_,
        v_____x_2825_,
    );
    return v_res_2826_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__8(
    mut v_00_u03c6_2827_: *mut crate::leanh::LeanObject,
    mut v___x_2828_: *mut crate::leanh::LeanObject,
    mut v___x_2829_: *mut crate::leanh::LeanObject,
    mut v___x_2830_: *mut crate::leanh::LeanObject,
    mut v___x_2831_: *mut crate::leanh::LeanObject,
    mut v___x_2832_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3s_2833_: *mut crate::leanh::LeanObject,
    mut v_hyp_2834_: *mut crate::leanh::LeanObject,
    mut v_u_2835_: *mut crate::leanh::LeanObject,
    mut v_toPure_2836_: *mut crate::leanh::LeanObject,
    mut v_inst_2837_: *mut crate::leanh::LeanObject,
    mut v_toBind_2838_: *mut crate::leanh::LeanObject,
    mut v_k_2839_: *mut crate::leanh::LeanObject,
    mut v___f_2840_: *mut crate::leanh::LeanObject,
    mut v_inst_2841_: *mut crate::leanh::LeanObject,
    mut v_inst_2842_: *mut crate::leanh::LeanObject,
    mut v___f_2843_: *mut crate::leanh::LeanObject,
    mut v_inst_2844_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_toBind_2838_);
    crate::leanh::lean_inc(v_inst_2837_);
    v___f_2845_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__7___boxed
            as *mut core::ffi::c_void,
        18,
        17,
    );
    crate::leanh::lean_closure_set(v___f_2845_, 0, v_00_u03c6_2827_);
    crate::leanh::lean_closure_set(v___f_2845_, 1, v___x_2828_);
    crate::leanh::lean_closure_set(v___f_2845_, 2, v___x_2829_);
    crate::leanh::lean_closure_set(v___f_2845_, 3, v___x_2830_);
    crate::leanh::lean_closure_set(v___f_2845_, 4, v___x_2831_);
    crate::leanh::lean_closure_set(v___f_2845_, 5, v___x_2832_);
    crate::leanh::lean_closure_set(v___f_2845_, 6, v_00_u03c3s_2833_);
    crate::leanh::lean_closure_set(v___f_2845_, 7, v_hyp_2834_);
    crate::leanh::lean_closure_set(v___f_2845_, 8, v_inst_2844_);
    crate::leanh::lean_closure_set(v___f_2845_, 9, v_u_2835_);
    crate::leanh::lean_closure_set(v___f_2845_, 10, v_toPure_2836_);
    crate::leanh::lean_closure_set(v___f_2845_, 11, v_inst_2837_);
    crate::leanh::lean_closure_set(v___f_2845_, 12, v_toBind_2838_);
    crate::leanh::lean_closure_set(v___f_2845_, 13, v_k_2839_);
    crate::leanh::lean_closure_set(v___f_2845_, 14, v___f_2840_);
    crate::leanh::lean_closure_set(v___f_2845_, 15, v_inst_2841_);
    crate::leanh::lean_closure_set(v___f_2845_, 16, v_inst_2842_);
    v___x_2846_ = crate::leanh::lean_apply_2(v_inst_2837_, crate::leanh::lean_box(0), v___f_2843_);
    v___x_2847_ = crate::leanh::lean_apply_4(
        v_toBind_2838_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2846_,
        v___f_2845_,
    );
    return v___x_2847_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__8___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_00_u03c6_2848_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v___x_2849_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v___x_2850_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v___x_2851_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v___x_2852_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___x_2853_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_00_u03c3s_2854_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_hyp_2855_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_u_2856_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_toPure_2857_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_inst_2858_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_toBind_2859_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_k_2860_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___f_2861_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_inst_2862_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_inst_2863_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___f_2864_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_inst_2865_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_res_2866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2866_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__8(
        v_00_u03c6_2848_,
        v___x_2849_,
        v___x_2850_,
        v___x_2851_,
        v___x_2852_,
        v___x_2853_,
        v_00_u03c3s_2854_,
        v_hyp_2855_,
        v_u_2856_,
        v_toPure_2857_,
        v_inst_2858_,
        v_toBind_2859_,
        v_k_2860_,
        v___f_2861_,
        v_inst_2862_,
        v_inst_2863_,
        v___f_2864_,
        v_inst_2865_,
    );
    return v_res_2866_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9(
    mut v_u_2878_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3s_2879_: *mut crate::leanh::LeanObject,
    mut v_hyp_2880_: *mut crate::leanh::LeanObject,
    mut v_toPure_2881_: *mut crate::leanh::LeanObject,
    mut v_inst_2882_: *mut crate::leanh::LeanObject,
    mut v_toBind_2883_: *mut crate::leanh::LeanObject,
    mut v_k_2884_: *mut crate::leanh::LeanObject,
    mut v___f_2885_: *mut crate::leanh::LeanObject,
    mut v_inst_2886_: *mut crate::leanh::LeanObject,
    mut v_inst_2887_: *mut crate::leanh::LeanObject,
    mut v___f_2888_: *mut crate::leanh::LeanObject,
    mut v_00_u03c6_2889_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2890_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__0;
    v___x_2891_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__1;
    v___x_2892_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__2;
    v___x_2893_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__3;
    v___x_2894_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__5;
    v___x_2895_ = crate::leanh::lean_box(0);
    crate::leanh::lean_inc(v_u_2878_);
    v___x_2896_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2896_, 0, v_u_2878_);
    crate::leanh::lean_ctor_set(v___x_2896_, 1, v___x_2895_);
    crate::leanh::lean_inc(v_toBind_2883_);
    crate::leanh::lean_inc(v_inst_2882_);
    crate::leanh::lean_inc_ref(v_hyp_2880_);
    crate::leanh::lean_inc_ref(v_00_u03c3s_2879_);
    crate::leanh::lean_inc_ref(v___x_2896_);
    crate::leanh::lean_inc_ref(v_00_u03c6_2889_);
    v___f_2897_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__8___boxed
            as *mut core::ffi::c_void,
        18,
        17,
    );
    crate::leanh::lean_closure_set(v___f_2897_, 0, v_00_u03c6_2889_);
    crate::leanh::lean_closure_set(v___f_2897_, 1, v___x_2890_);
    crate::leanh::lean_closure_set(v___f_2897_, 2, v___x_2891_);
    crate::leanh::lean_closure_set(v___f_2897_, 3, v___x_2892_);
    crate::leanh::lean_closure_set(v___f_2897_, 4, v___x_2893_);
    crate::leanh::lean_closure_set(v___f_2897_, 5, v___x_2896_);
    crate::leanh::lean_closure_set(v___f_2897_, 6, v_00_u03c3s_2879_);
    crate::leanh::lean_closure_set(v___f_2897_, 7, v_hyp_2880_);
    crate::leanh::lean_closure_set(v___f_2897_, 8, v_u_2878_);
    crate::leanh::lean_closure_set(v___f_2897_, 9, v_toPure_2881_);
    crate::leanh::lean_closure_set(v___f_2897_, 10, v_inst_2882_);
    crate::leanh::lean_closure_set(v___f_2897_, 11, v_toBind_2883_);
    crate::leanh::lean_closure_set(v___f_2897_, 12, v_k_2884_);
    crate::leanh::lean_closure_set(v___f_2897_, 13, v___f_2885_);
    crate::leanh::lean_closure_set(v___f_2897_, 14, v_inst_2886_);
    crate::leanh::lean_closure_set(v___f_2897_, 15, v_inst_2887_);
    crate::leanh::lean_closure_set(v___f_2897_, 16, v___f_2888_);
    v___x_2898_ = l_Lean_mkConst(v___x_2894_, v___x_2896_);
    v___x_2899_ = l_Lean_mkApp3(
        v___x_2898_,
        v_00_u03c3s_2879_,
        v_hyp_2880_,
        v_00_u03c6_2889_,
    );
    v___x_2900_ = crate::leanh::lean_box(0);
    v___x_2901_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_synthInstance___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_2901_, 0, v___x_2899_);
    crate::leanh::lean_closure_set(v___x_2901_, 1, v___x_2900_);
    v___x_2902_ = crate::leanh::lean_apply_2(v_inst_2882_, crate::leanh::lean_box(0), v___x_2901_);
    v___x_2903_ = crate::leanh::lean_apply_4(
        v_toBind_2883_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2902_,
        v___f_2897_,
    );
    return v___x_2903_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2904_ = crate::leanh::lean_box(0);
    v___x_2905_ = l_Lean_mkSort(v___x_2904_);
    return v___x_2905_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2906_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__0_once
        ),
        _init_l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__0,
    );
    v___x_2907_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2907_, 0, v___x_2906_);
    return v___x_2907_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: u8 = 0;
    let mut v___x_2910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2908_ = crate::leanh::lean_box(0);
    v___x_2909_ = 0;
    v___x_2910_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__1_once
        ),
        _init_l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__1,
    );
    v___x_2911_ = crate::leanh::lean_box((v___x_2909_) as usize);
    v___x_2912_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_mkFreshExprMVar___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    crate::leanh::lean_closure_set(v___x_2912_, 0, v___x_2910_);
    crate::leanh::lean_closure_set(v___x_2912_, 1, v___x_2911_);
    crate::leanh::lean_closure_set(v___x_2912_, 2, v___x_2908_);
    return v___x_2912_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10(
    mut v_00_u03c3s_2913_: *mut crate::leanh::LeanObject,
    mut v_hyp_2914_: *mut crate::leanh::LeanObject,
    mut v_toPure_2915_: *mut crate::leanh::LeanObject,
    mut v_inst_2916_: *mut crate::leanh::LeanObject,
    mut v_toBind_2917_: *mut crate::leanh::LeanObject,
    mut v_k_2918_: *mut crate::leanh::LeanObject,
    mut v___f_2919_: *mut crate::leanh::LeanObject,
    mut v_inst_2920_: *mut crate::leanh::LeanObject,
    mut v_inst_2921_: *mut crate::leanh::LeanObject,
    mut v___f_2922_: *mut crate::leanh::LeanObject,
    mut v_u_2923_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_toBind_2917_);
    crate::leanh::lean_inc(v_inst_2916_);
    v___f_2924_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9 as *mut core::ffi::c_void,
        12,
        11,
    );
    crate::leanh::lean_closure_set(v___f_2924_, 0, v_u_2923_);
    crate::leanh::lean_closure_set(v___f_2924_, 1, v_00_u03c3s_2913_);
    crate::leanh::lean_closure_set(v___f_2924_, 2, v_hyp_2914_);
    crate::leanh::lean_closure_set(v___f_2924_, 3, v_toPure_2915_);
    crate::leanh::lean_closure_set(v___f_2924_, 4, v_inst_2916_);
    crate::leanh::lean_closure_set(v___f_2924_, 5, v_toBind_2917_);
    crate::leanh::lean_closure_set(v___f_2924_, 6, v_k_2918_);
    crate::leanh::lean_closure_set(v___f_2924_, 7, v___f_2919_);
    crate::leanh::lean_closure_set(v___f_2924_, 8, v_inst_2920_);
    crate::leanh::lean_closure_set(v___f_2924_, 9, v_inst_2921_);
    crate::leanh::lean_closure_set(v___f_2924_, 10, v___f_2922_);
    v___x_2925_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__2_once
        ),
        _init_l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__2,
    );
    v___x_2926_ = crate::leanh::lean_apply_2(v_inst_2916_, crate::leanh::lean_box(0), v___x_2925_);
    v___x_2927_ = crate::leanh::lean_apply_4(
        v_toBind_2917_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2926_,
        v___f_2924_,
    );
    return v___x_2927_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg(
    mut v_inst_2930_: *mut crate::leanh::LeanObject,
    mut v_inst_2931_: *mut crate::leanh::LeanObject,
    mut v_inst_2932_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3s_2933_: *mut crate::leanh::LeanObject,
    mut v_hyp_2934_: *mut crate::leanh::LeanObject,
    mut v_name_2935_: *mut crate::leanh::LeanObject,
    mut v_k_2936_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2937_ = crate::leanh::lean_ctor_get(v_inst_2930_, 0);
    v_toBind_2938_ = crate::leanh::lean_ctor_get(v_inst_2930_, 1);
    crate::leanh::lean_inc_n(v_toBind_2938_, 2);
    v_toPure_2939_ = crate::leanh::lean_ctor_get(v_toApplicative_2937_, 1);
    crate::leanh::lean_inc(v_toPure_2939_);
    v___f_2940_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___closed__0;
    v___f_2941_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__1___boxed
            as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2941_, 0, v_name_2935_);
    v___x_2942_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___closed__1;
    crate::leanh::lean_inc(v_inst_2932_);
    v___x_2943_ = crate::leanh::lean_apply_2(v_inst_2932_, crate::leanh::lean_box(0), v___x_2942_);
    v___f_2944_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10 as *mut core::ffi::c_void,
        11,
        10,
    );
    crate::leanh::lean_closure_set(v___f_2944_, 0, v_00_u03c3s_2933_);
    crate::leanh::lean_closure_set(v___f_2944_, 1, v_hyp_2934_);
    crate::leanh::lean_closure_set(v___f_2944_, 2, v_toPure_2939_);
    crate::leanh::lean_closure_set(v___f_2944_, 3, v_inst_2932_);
    crate::leanh::lean_closure_set(v___f_2944_, 4, v_toBind_2938_);
    crate::leanh::lean_closure_set(v___f_2944_, 5, v_k_2936_);
    crate::leanh::lean_closure_set(v___f_2944_, 6, v___f_2940_);
    crate::leanh::lean_closure_set(v___f_2944_, 7, v_inst_2931_);
    crate::leanh::lean_closure_set(v___f_2944_, 8, v_inst_2930_);
    crate::leanh::lean_closure_set(v___f_2944_, 9, v___f_2941_);
    v___x_2945_ = crate::leanh::lean_apply_4(
        v_toBind_2938_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2943_,
        v___f_2944_,
    );
    return v___x_2945_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mPureCore(
    mut v_m_2946_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2947_: *mut crate::leanh::LeanObject,
    mut v_inst_2948_: *mut crate::leanh::LeanObject,
    mut v_inst_2949_: *mut crate::leanh::LeanObject,
    mut v_inst_2950_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3s_2951_: *mut crate::leanh::LeanObject,
    mut v_hyp_2952_: *mut crate::leanh::LeanObject,
    mut v_name_2953_: *mut crate::leanh::LeanObject,
    mut v_k_2954_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2955_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg(
        v_inst_2948_,
        v_inst_2949_,
        v_inst_2950_,
        v_00_u03c3s_2951_,
        v_hyp_2952_,
        v_name_2953_,
        v_k_2954_,
    );
    return v___x_2955_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2956_ = crate::leanh::lean_box(0);
    v___x_2957_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_2958_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2958_, 0, v___x_2957_);
    crate::leanh::lean_ctor_set(v___x_2958_, 1, v___x_2956_);
    return v___x_2958_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__0___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2960_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__0___redArg___closed__0);
    v___x_2961_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2961_, 0, v___x_2960_);
    return v___x_2961_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__0___redArg___boxed(
    mut v___y_2962_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2963_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__0___redArg();
    return v_res_2963_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__0(
    mut v_00_u03b1_2964_: *mut crate::leanh::LeanObject,
    mut v___y_2965_: *mut crate::leanh::LeanObject,
    mut v___y_2966_: *mut crate::leanh::LeanObject,
    mut v___y_2967_: *mut crate::leanh::LeanObject,
    mut v___y_2968_: *mut crate::leanh::LeanObject,
    mut v___y_2969_: *mut crate::leanh::LeanObject,
    mut v___y_2970_: *mut crate::leanh::LeanObject,
    mut v___y_2971_: *mut crate::leanh::LeanObject,
    mut v___y_2972_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2974_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__0___redArg();
    return v___x_2974_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__0___boxed(
    mut v_00_u03b1_2975_: *mut crate::leanh::LeanObject,
    mut v___y_2976_: *mut crate::leanh::LeanObject,
    mut v___y_2977_: *mut crate::leanh::LeanObject,
    mut v___y_2978_: *mut crate::leanh::LeanObject,
    mut v___y_2979_: *mut crate::leanh::LeanObject,
    mut v___y_2980_: *mut crate::leanh::LeanObject,
    mut v___y_2981_: *mut crate::leanh::LeanObject,
    mut v___y_2982_: *mut crate::leanh::LeanObject,
    mut v___y_2983_: *mut crate::leanh::LeanObject,
    mut v___y_2984_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2985_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__0(
            v_00_u03b1_2975_,
            v___y_2976_,
            v___y_2977_,
            v___y_2978_,
            v___y_2979_,
            v___y_2980_,
            v___y_2981_,
            v___y_2982_,
            v___y_2983_,
        );
    crate::leanh::lean_dec(v___y_2983_);
    crate::leanh::lean_dec_ref(v___y_2982_);
    crate::leanh::lean_dec(v___y_2981_);
    crate::leanh::lean_dec_ref(v___y_2980_);
    crate::leanh::lean_dec(v___y_2979_);
    crate::leanh::lean_dec_ref(v___y_2978_);
    crate::leanh::lean_dec(v___y_2977_);
    crate::leanh::lean_dec_ref(v___y_2976_);
    return v_res_2985_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__3___redArg___lam__0(
    mut v_x_2986_: *mut crate::leanh::LeanObject,
    mut v___y_2987_: *mut crate::leanh::LeanObject,
    mut v___y_2988_: *mut crate::leanh::LeanObject,
    mut v___y_2989_: *mut crate::leanh::LeanObject,
    mut v___y_2990_: *mut crate::leanh::LeanObject,
    mut v___y_2991_: *mut crate::leanh::LeanObject,
    mut v___y_2992_: *mut crate::leanh::LeanObject,
    mut v___y_2993_: *mut crate::leanh::LeanObject,
    mut v___y_2994_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_2990_);
    crate::leanh::lean_inc_ref(v___y_2989_);
    crate::leanh::lean_inc(v___y_2988_);
    crate::leanh::lean_inc_ref(v___y_2987_);
    v___x_2996_ = crate::leanh::lean_apply_9(
        v_x_2986_,
        v___y_2987_,
        v___y_2988_,
        v___y_2989_,
        v___y_2990_,
        v___y_2991_,
        v___y_2992_,
        v___y_2993_,
        v___y_2994_,
        crate::leanh::lean_box(0),
    );
    return v___x_2996_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__3___redArg___lam__0___boxed(
    mut v_x_2997_: *mut crate::leanh::LeanObject,
    mut v___y_2998_: *mut crate::leanh::LeanObject,
    mut v___y_2999_: *mut crate::leanh::LeanObject,
    mut v___y_3000_: *mut crate::leanh::LeanObject,
    mut v___y_3001_: *mut crate::leanh::LeanObject,
    mut v___y_3002_: *mut crate::leanh::LeanObject,
    mut v___y_3003_: *mut crate::leanh::LeanObject,
    mut v___y_3004_: *mut crate::leanh::LeanObject,
    mut v___y_3005_: *mut crate::leanh::LeanObject,
    mut v___y_3006_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3007_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__3___redArg___lam__0(v_x_2997_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_);
    crate::leanh::lean_dec(v___y_3001_);
    crate::leanh::lean_dec_ref(v___y_3000_);
    crate::leanh::lean_dec(v___y_2999_);
    crate::leanh::lean_dec_ref(v___y_2998_);
    return v_res_3007_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__3___redArg(
    mut v_mvarId_3008_: *mut crate::leanh::LeanObject,
    mut v_x_3009_: *mut crate::leanh::LeanObject,
    mut v___y_3010_: *mut crate::leanh::LeanObject,
    mut v___y_3011_: *mut crate::leanh::LeanObject,
    mut v___y_3012_: *mut crate::leanh::LeanObject,
    mut v___y_3013_: *mut crate::leanh::LeanObject,
    mut v___y_3014_: *mut crate::leanh::LeanObject,
    mut v___y_3015_: *mut crate::leanh::LeanObject,
    mut v___y_3016_: *mut crate::leanh::LeanObject,
    mut v___y_3017_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3024_: u8 = 0;
    let mut v___x_3026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3028_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_3013_);
                crate::leanh::lean_inc_ref(v___y_3012_);
                crate::leanh::lean_inc(v___y_3011_);
                crate::leanh::lean_inc_ref(v___y_3010_);
                v___f_3019_ = crate::leanh::lean_alloc_closure(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__3___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 5);
                crate::leanh::lean_closure_set(v___f_3019_, 0, v_x_3009_);
                crate::leanh::lean_closure_set(v___f_3019_, 1, v___y_3010_);
                crate::leanh::lean_closure_set(v___f_3019_, 2, v___y_3011_);
                crate::leanh::lean_closure_set(v___f_3019_, 3, v___y_3012_);
                crate::leanh::lean_closure_set(v___f_3019_, 4, v___y_3013_);
                v___x_3020_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    crate::leanh::lean_box(0),
                    v_mvarId_3008_,
                    v___f_3019_,
                    v___y_3014_,
                    v___y_3015_,
                    v___y_3016_,
                    v___y_3017_,
                );
                if crate::leanh::lean_obj_tag(v___x_3020_) == 0 {
                    return v___x_3020_;
                } else {
                    v_a_3021_ = crate::leanh::lean_ctor_get(v___x_3020_, 0);
                    v_isSharedCheck_3028_ = (!crate::leanh::lean_is_exclusive(v___x_3020_)) as u8;
                    if v_isSharedCheck_3028_ == 0 {
                        v___x_3023_ = v___x_3020_;
                        v_isShared_3024_ = v_isSharedCheck_3028_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3021_);
                        crate::leanh::lean_dec(v___x_3020_);
                        v___x_3023_ = crate::leanh::lean_box(0);
                        v_isShared_3024_ = v_isSharedCheck_3028_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3024_ == 0 {
                    v___x_3026_ = v___x_3023_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3027_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3027_, 0, v_a_3021_);
                    v___x_3026_ = v_reuseFailAlloc_3027_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3026_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__3___redArg___boxed(
    mut v_mvarId_3029_: *mut crate::leanh::LeanObject,
    mut v_x_3030_: *mut crate::leanh::LeanObject,
    mut v___y_3031_: *mut crate::leanh::LeanObject,
    mut v___y_3032_: *mut crate::leanh::LeanObject,
    mut v___y_3033_: *mut crate::leanh::LeanObject,
    mut v___y_3034_: *mut crate::leanh::LeanObject,
    mut v___y_3035_: *mut crate::leanh::LeanObject,
    mut v___y_3036_: *mut crate::leanh::LeanObject,
    mut v___y_3037_: *mut crate::leanh::LeanObject,
    mut v___y_3038_: *mut crate::leanh::LeanObject,
    mut v___y_3039_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3040_ =
        l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__3___redArg(
            v_mvarId_3029_,
            v_x_3030_,
            v___y_3031_,
            v___y_3032_,
            v___y_3033_,
            v___y_3034_,
            v___y_3035_,
            v___y_3036_,
            v___y_3037_,
            v___y_3038_,
        );
    crate::leanh::lean_dec(v___y_3038_);
    crate::leanh::lean_dec_ref(v___y_3037_);
    crate::leanh::lean_dec(v___y_3036_);
    crate::leanh::lean_dec_ref(v___y_3035_);
    crate::leanh::lean_dec(v___y_3034_);
    crate::leanh::lean_dec_ref(v___y_3033_);
    crate::leanh::lean_dec(v___y_3032_);
    crate::leanh::lean_dec_ref(v___y_3031_);
    return v_res_3040_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__3(
    mut v_00_u03b1_3041_: *mut crate::leanh::LeanObject,
    mut v_mvarId_3042_: *mut crate::leanh::LeanObject,
    mut v_x_3043_: *mut crate::leanh::LeanObject,
    mut v___y_3044_: *mut crate::leanh::LeanObject,
    mut v___y_3045_: *mut crate::leanh::LeanObject,
    mut v___y_3046_: *mut crate::leanh::LeanObject,
    mut v___y_3047_: *mut crate::leanh::LeanObject,
    mut v___y_3048_: *mut crate::leanh::LeanObject,
    mut v___y_3049_: *mut crate::leanh::LeanObject,
    mut v___y_3050_: *mut crate::leanh::LeanObject,
    mut v___y_3051_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3053_ =
        l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__3___redArg(
            v_mvarId_3042_,
            v_x_3043_,
            v___y_3044_,
            v___y_3045_,
            v___y_3046_,
            v___y_3047_,
            v___y_3048_,
            v___y_3049_,
            v___y_3050_,
            v___y_3051_,
        );
    return v___x_3053_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__3___boxed(
    mut v_00_u03b1_3054_: *mut crate::leanh::LeanObject,
    mut v_mvarId_3055_: *mut crate::leanh::LeanObject,
    mut v_x_3056_: *mut crate::leanh::LeanObject,
    mut v___y_3057_: *mut crate::leanh::LeanObject,
    mut v___y_3058_: *mut crate::leanh::LeanObject,
    mut v___y_3059_: *mut crate::leanh::LeanObject,
    mut v___y_3060_: *mut crate::leanh::LeanObject,
    mut v___y_3061_: *mut crate::leanh::LeanObject,
    mut v___y_3062_: *mut crate::leanh::LeanObject,
    mut v___y_3063_: *mut crate::leanh::LeanObject,
    mut v___y_3064_: *mut crate::leanh::LeanObject,
    mut v___y_3065_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3066_ =
        l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__3(
            v_00_u03b1_3054_,
            v_mvarId_3055_,
            v_x_3056_,
            v___y_3057_,
            v___y_3058_,
            v___y_3059_,
            v___y_3060_,
            v___y_3061_,
            v___y_3062_,
            v___y_3063_,
            v___y_3064_,
        );
    crate::leanh::lean_dec(v___y_3064_);
    crate::leanh::lean_dec_ref(v___y_3063_);
    crate::leanh::lean_dec(v___y_3062_);
    crate::leanh::lean_dec_ref(v___y_3061_);
    crate::leanh::lean_dec(v___y_3060_);
    crate::leanh::lean_dec_ref(v___y_3059_);
    crate::leanh::lean_dec(v___y_3058_);
    crate::leanh::lean_dec_ref(v___y_3057_);
    return v_res_3066_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___lam__0(
    mut v_a_3067_: *mut crate::leanh::LeanObject,
    mut v_snd_3068_: *mut crate::leanh::LeanObject,
    mut v_x_3069_: *mut crate::leanh::LeanObject,
    mut v_x_3070_: *mut crate::leanh::LeanObject,
    mut v___y_3071_: *mut crate::leanh::LeanObject,
    mut v___y_3072_: *mut crate::leanh::LeanObject,
    mut v___y_3073_: *mut crate::leanh::LeanObject,
    mut v___y_3074_: *mut crate::leanh::LeanObject,
    mut v___y_3075_: *mut crate::leanh::LeanObject,
    mut v___y_3076_: *mut crate::leanh::LeanObject,
    mut v___y_3077_: *mut crate::leanh::LeanObject,
    mut v___y_3078_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3087_: u8 = 0;
    let mut v___x_3088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3093_: u8 = 0;
    let mut v_a_3094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3097_: u8 = 0;
    let mut v___x_3099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3101_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3080_ =
                    l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_restGoal(v_a_3067_, v_snd_3068_);
                crate::leanh::lean_inc_ref(v___x_3080_);
                v___x_3081_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v___x_3080_);
                v___x_3082_ = crate::leanh::lean_box(0);
                v___x_3083_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                    v___x_3081_,
                    v___x_3082_,
                    v___y_3075_,
                    v___y_3076_,
                    v___y_3077_,
                    v___y_3078_,
                );
                if crate::leanh::lean_obj_tag(v___x_3083_) == 0 {
                    v_a_3084_ = crate::leanh::lean_ctor_get(v___x_3083_, 0);
                    v_isSharedCheck_3093_ = (!crate::leanh::lean_is_exclusive(v___x_3083_)) as u8;
                    if v_isSharedCheck_3093_ == 0 {
                        v___x_3086_ = v___x_3083_;
                        v_isShared_3087_ = v_isSharedCheck_3093_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3084_);
                        crate::leanh::lean_dec(v___x_3083_);
                        v___x_3086_ = crate::leanh::lean_box(0);
                        v_isShared_3087_ = v_isSharedCheck_3093_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_3080_);
                    v_a_3094_ = crate::leanh::lean_ctor_get(v___x_3083_, 0);
                    v_isSharedCheck_3101_ = (!crate::leanh::lean_is_exclusive(v___x_3083_)) as u8;
                    if v_isSharedCheck_3101_ == 0 {
                        v___x_3096_ = v___x_3083_;
                        v_isShared_3097_ = v_isSharedCheck_3101_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3094_);
                        crate::leanh::lean_dec(v___x_3083_);
                        v___x_3096_ = crate::leanh::lean_box(0);
                        v_isShared_3097_ = v_isSharedCheck_3101_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_a_3084_);
                v___x_3088_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3088_, 0, v___x_3080_);
                crate::leanh::lean_ctor_set(v___x_3088_, 1, v_a_3084_);
                v___x_3089_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3089_, 0, v_a_3084_);
                crate::leanh::lean_ctor_set(v___x_3089_, 1, v___x_3088_);
                if v_isShared_3087_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3086_, 0, v___x_3089_);
                    v___x_3091_ = v___x_3086_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3092_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3092_, 0, v___x_3089_);
                    v___x_3091_ = v_reuseFailAlloc_3092_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3091_;
            }
            3 => {
                if v_isShared_3097_ == 0 {
                    v___x_3099_ = v___x_3096_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3100_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3100_, 0, v_a_3094_);
                    v___x_3099_ = v_reuseFailAlloc_3100_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3099_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___lam__0___boxed(
    mut v_a_3102_: *mut crate::leanh::LeanObject,
    mut v_snd_3103_: *mut crate::leanh::LeanObject,
    mut v_x_3104_: *mut crate::leanh::LeanObject,
    mut v_x_3105_: *mut crate::leanh::LeanObject,
    mut v___y_3106_: *mut crate::leanh::LeanObject,
    mut v___y_3107_: *mut crate::leanh::LeanObject,
    mut v___y_3108_: *mut crate::leanh::LeanObject,
    mut v___y_3109_: *mut crate::leanh::LeanObject,
    mut v___y_3110_: *mut crate::leanh::LeanObject,
    mut v___y_3111_: *mut crate::leanh::LeanObject,
    mut v___y_3112_: *mut crate::leanh::LeanObject,
    mut v___y_3113_: *mut crate::leanh::LeanObject,
    mut v___y_3114_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3115_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___lam__0(
        v_a_3102_,
        v_snd_3103_,
        v_x_3104_,
        v_x_3105_,
        v___y_3106_,
        v___y_3107_,
        v___y_3108_,
        v___y_3109_,
        v___y_3110_,
        v___y_3111_,
        v___y_3112_,
        v___y_3113_,
    );
    crate::leanh::lean_dec(v___y_3113_);
    crate::leanh::lean_dec_ref(v___y_3112_);
    crate::leanh::lean_dec(v___y_3111_);
    crate::leanh::lean_dec_ref(v___y_3110_);
    crate::leanh::lean_dec(v___y_3109_);
    crate::leanh::lean_dec_ref(v___y_3108_);
    crate::leanh::lean_dec(v___y_3107_);
    crate::leanh::lean_dec_ref(v___y_3106_);
    crate::leanh::lean_dec_ref(v_x_3105_);
    crate::leanh::lean_dec_ref(v_x_3104_);
    crate::leanh::lean_dec_ref(v_a_3102_);
    return v_res_3115_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1_spec__3___redArg___lam__0(
    mut v_k_3116_: *mut crate::leanh::LeanObject,
    mut v___y_3117_: *mut crate::leanh::LeanObject,
    mut v___y_3118_: *mut crate::leanh::LeanObject,
    mut v___y_3119_: *mut crate::leanh::LeanObject,
    mut v___y_3120_: *mut crate::leanh::LeanObject,
    mut v_b_3121_: *mut crate::leanh::LeanObject,
    mut v___y_3122_: *mut crate::leanh::LeanObject,
    mut v___y_3123_: *mut crate::leanh::LeanObject,
    mut v___y_3124_: *mut crate::leanh::LeanObject,
    mut v___y_3125_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_3125_);
    crate::leanh::lean_inc_ref(v___y_3124_);
    crate::leanh::lean_inc(v___y_3123_);
    crate::leanh::lean_inc_ref(v___y_3122_);
    crate::leanh::lean_inc(v___y_3120_);
    crate::leanh::lean_inc_ref(v___y_3119_);
    crate::leanh::lean_inc(v___y_3118_);
    crate::leanh::lean_inc_ref(v___y_3117_);
    v___x_3127_ = crate::leanh::lean_apply_10(
        v_k_3116_,
        v_b_3121_,
        v___y_3117_,
        v___y_3118_,
        v___y_3119_,
        v___y_3120_,
        v___y_3122_,
        v___y_3123_,
        v___y_3124_,
        v___y_3125_,
        crate::leanh::lean_box(0),
    );
    return v___x_3127_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1_spec__3___redArg___lam__0___boxed(
    mut v_k_3128_: *mut crate::leanh::LeanObject,
    mut v___y_3129_: *mut crate::leanh::LeanObject,
    mut v___y_3130_: *mut crate::leanh::LeanObject,
    mut v___y_3131_: *mut crate::leanh::LeanObject,
    mut v___y_3132_: *mut crate::leanh::LeanObject,
    mut v_b_3133_: *mut crate::leanh::LeanObject,
    mut v___y_3134_: *mut crate::leanh::LeanObject,
    mut v___y_3135_: *mut crate::leanh::LeanObject,
    mut v___y_3136_: *mut crate::leanh::LeanObject,
    mut v___y_3137_: *mut crate::leanh::LeanObject,
    mut v___y_3138_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3139_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1_spec__3___redArg___lam__0(v_k_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v_b_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_);
    crate::leanh::lean_dec(v___y_3137_);
    crate::leanh::lean_dec_ref(v___y_3136_);
    crate::leanh::lean_dec(v___y_3135_);
    crate::leanh::lean_dec_ref(v___y_3134_);
    crate::leanh::lean_dec(v___y_3132_);
    crate::leanh::lean_dec_ref(v___y_3131_);
    crate::leanh::lean_dec(v___y_3130_);
    crate::leanh::lean_dec_ref(v___y_3129_);
    return v_res_3139_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1_spec__3___redArg(
    mut v_name_3140_: *mut crate::leanh::LeanObject,
    mut v_bi_3141_: u8,
    mut v_type_3142_: *mut crate::leanh::LeanObject,
    mut v_k_3143_: *mut crate::leanh::LeanObject,
    mut v_kind_3144_: u8,
    mut v___y_3145_: *mut crate::leanh::LeanObject,
    mut v___y_3146_: *mut crate::leanh::LeanObject,
    mut v___y_3147_: *mut crate::leanh::LeanObject,
    mut v___y_3148_: *mut crate::leanh::LeanObject,
    mut v___y_3149_: *mut crate::leanh::LeanObject,
    mut v___y_3150_: *mut crate::leanh::LeanObject,
    mut v___y_3151_: *mut crate::leanh::LeanObject,
    mut v___y_3152_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3159_: u8 = 0;
    let mut v___x_3161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3163_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_3148_);
                crate::leanh::lean_inc_ref(v___y_3147_);
                crate::leanh::lean_inc(v___y_3146_);
                crate::leanh::lean_inc_ref(v___y_3145_);
                v___f_3154_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1_spec__3___redArg___lam__0___boxed as *mut core::ffi::c_void, 11, 5);
                crate::leanh::lean_closure_set(v___f_3154_, 0, v_k_3143_);
                crate::leanh::lean_closure_set(v___f_3154_, 1, v___y_3145_);
                crate::leanh::lean_closure_set(v___f_3154_, 2, v___y_3146_);
                crate::leanh::lean_closure_set(v___f_3154_, 3, v___y_3147_);
                crate::leanh::lean_closure_set(v___f_3154_, 4, v___y_3148_);
                v___x_3155_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(
                    crate::leanh::lean_box(0),
                    v_name_3140_,
                    v_bi_3141_,
                    v_type_3142_,
                    v___f_3154_,
                    v_kind_3144_,
                    v___y_3149_,
                    v___y_3150_,
                    v___y_3151_,
                    v___y_3152_,
                );
                if crate::leanh::lean_obj_tag(v___x_3155_) == 0 {
                    return v___x_3155_;
                } else {
                    v_a_3156_ = crate::leanh::lean_ctor_get(v___x_3155_, 0);
                    v_isSharedCheck_3163_ = (!crate::leanh::lean_is_exclusive(v___x_3155_)) as u8;
                    if v_isSharedCheck_3163_ == 0 {
                        v___x_3158_ = v___x_3155_;
                        v_isShared_3159_ = v_isSharedCheck_3163_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3156_);
                        crate::leanh::lean_dec(v___x_3155_);
                        v___x_3158_ = crate::leanh::lean_box(0);
                        v_isShared_3159_ = v_isSharedCheck_3163_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3159_ == 0 {
                    v___x_3161_ = v___x_3158_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3162_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3162_, 0, v_a_3156_);
                    v___x_3161_ = v_reuseFailAlloc_3162_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3161_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1_spec__3___redArg___boxed(
    mut v_name_3164_: *mut crate::leanh::LeanObject,
    mut v_bi_3165_: *mut crate::leanh::LeanObject,
    mut v_type_3166_: *mut crate::leanh::LeanObject,
    mut v_k_3167_: *mut crate::leanh::LeanObject,
    mut v_kind_3168_: *mut crate::leanh::LeanObject,
    mut v___y_3169_: *mut crate::leanh::LeanObject,
    mut v___y_3170_: *mut crate::leanh::LeanObject,
    mut v___y_3171_: *mut crate::leanh::LeanObject,
    mut v___y_3172_: *mut crate::leanh::LeanObject,
    mut v___y_3173_: *mut crate::leanh::LeanObject,
    mut v___y_3174_: *mut crate::leanh::LeanObject,
    mut v___y_3175_: *mut crate::leanh::LeanObject,
    mut v___y_3176_: *mut crate::leanh::LeanObject,
    mut v___y_3177_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_bi_boxed_3178_: u8 = 0;
    let mut v_kind_boxed_3179_: u8 = 0;
    let mut v_res_3180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_3178_ = (crate::leanh::lean_unbox(v_bi_3165_) as u8);
    v_kind_boxed_3179_ = (crate::leanh::lean_unbox(v_kind_3168_) as u8);
    v_res_3180_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1_spec__3___redArg(v_name_3164_, v_bi_boxed_3178_, v_type_3166_, v_k_3167_, v_kind_boxed_3179_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_);
    crate::leanh::lean_dec(v___y_3176_);
    crate::leanh::lean_dec_ref(v___y_3175_);
    crate::leanh::lean_dec(v___y_3174_);
    crate::leanh::lean_dec_ref(v___y_3173_);
    crate::leanh::lean_dec(v___y_3172_);
    crate::leanh::lean_dec_ref(v___y_3171_);
    crate::leanh::lean_dec(v___y_3170_);
    crate::leanh::lean_dec_ref(v___y_3169_);
    return v_res_3180_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1___redArg(
    mut v_name_3181_: *mut crate::leanh::LeanObject,
    mut v_type_3182_: *mut crate::leanh::LeanObject,
    mut v_k_3183_: *mut crate::leanh::LeanObject,
    mut v___y_3184_: *mut crate::leanh::LeanObject,
    mut v___y_3185_: *mut crate::leanh::LeanObject,
    mut v___y_3186_: *mut crate::leanh::LeanObject,
    mut v___y_3187_: *mut crate::leanh::LeanObject,
    mut v___y_3188_: *mut crate::leanh::LeanObject,
    mut v___y_3189_: *mut crate::leanh::LeanObject,
    mut v___y_3190_: *mut crate::leanh::LeanObject,
    mut v___y_3191_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3193_: u8 = 0;
    let mut v___x_3194_: u8 = 0;
    let mut v___x_3195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3193_ = 0;
    v___x_3194_ = 0;
    v___x_3195_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1_spec__3___redArg(v_name_3181_, v___x_3193_, v_type_3182_, v_k_3183_, v___x_3194_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_);
    return v___x_3195_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1___redArg___boxed(
    mut v_name_3196_: *mut crate::leanh::LeanObject,
    mut v_type_3197_: *mut crate::leanh::LeanObject,
    mut v_k_3198_: *mut crate::leanh::LeanObject,
    mut v___y_3199_: *mut crate::leanh::LeanObject,
    mut v___y_3200_: *mut crate::leanh::LeanObject,
    mut v___y_3201_: *mut crate::leanh::LeanObject,
    mut v___y_3202_: *mut crate::leanh::LeanObject,
    mut v___y_3203_: *mut crate::leanh::LeanObject,
    mut v___y_3204_: *mut crate::leanh::LeanObject,
    mut v___y_3205_: *mut crate::leanh::LeanObject,
    mut v___y_3206_: *mut crate::leanh::LeanObject,
    mut v___y_3207_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3208_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1___redArg(v_name_3196_, v_type_3197_, v_k_3198_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_);
    crate::leanh::lean_dec(v___y_3206_);
    crate::leanh::lean_dec_ref(v___y_3205_);
    crate::leanh::lean_dec(v___y_3204_);
    crate::leanh::lean_dec_ref(v___y_3203_);
    crate::leanh::lean_dec(v___y_3202_);
    crate::leanh::lean_dec_ref(v___y_3201_);
    crate::leanh::lean_dec(v___y_3200_);
    crate::leanh::lean_dec_ref(v___y_3199_);
    return v_res_3208_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1___redArg___lam__0(
    mut v_a_3209_: *mut crate::leanh::LeanObject,
    mut v_snd_3210_: *mut crate::leanh::LeanObject,
    mut v_k_3211_: *mut crate::leanh::LeanObject,
    mut v___x_3212_: *mut crate::leanh::LeanObject,
    mut v___x_3213_: *mut crate::leanh::LeanObject,
    mut v___x_3214_: *mut crate::leanh::LeanObject,
    mut v___x_3215_: *mut crate::leanh::LeanObject,
    mut v___x_3216_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3s_3217_: *mut crate::leanh::LeanObject,
    mut v_hyp_3218_: *mut crate::leanh::LeanObject,
    mut v_a_3219_: *mut crate::leanh::LeanObject,
    mut v_a_3220_: *mut crate::leanh::LeanObject,
    mut v_h_3221_: *mut crate::leanh::LeanObject,
    mut v___y_3222_: *mut crate::leanh::LeanObject,
    mut v___y_3223_: *mut crate::leanh::LeanObject,
    mut v___y_3224_: *mut crate::leanh::LeanObject,
    mut v___y_3225_: *mut crate::leanh::LeanObject,
    mut v___y_3226_: *mut crate::leanh::LeanObject,
    mut v___y_3227_: *mut crate::leanh::LeanObject,
    mut v___y_3228_: *mut crate::leanh::LeanObject,
    mut v___y_3229_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lctx_3231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3233_: u8 = 0;
    let mut v___x_3234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3241_: u8 = 0;
    let mut v_fst_3242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3246_: u8 = 0;
    let mut v___x_3247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: u8 = 0;
    let mut v___x_3251_: u8 = 0;
    let mut v___x_3252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3256_: u8 = 0;
    let mut v_u_3257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_00_u03c3s_3258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hyps_3259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_3260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3263_: u8 = 0;
    let mut v___x_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_prf_3268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_goal_3271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3282_: u8 = 0;
    let mut v_isSharedCheck_3283_: u8 = 0;
    let mut v_a_3284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3287_: u8 = 0;
    let mut v___x_3289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3291_: u8 = 0;
    let mut v_isSharedCheck_3292_: u8 = 0;
    let mut v_isSharedCheck_3293_: u8 = 0;
    let mut v_a_3294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3297_: u8 = 0;
    let mut v___x_3299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3301_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lctx_3231_ = crate::leanh::lean_ctor_get(v___y_3226_, 2);
                crate::leanh::lean_inc_ref(v_a_3209_);
                v___x_3232_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3232_, 0, v_a_3209_);
                v___x_3233_ = 0;
                crate::leanh::lean_inc_ref(v_h_3221_);
                crate::leanh::lean_inc_ref(v_lctx_3231_);
                v___x_3234_ = l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo(
                    v_snd_3210_,
                    v_lctx_3231_,
                    v_h_3221_,
                    v___x_3232_,
                    v___x_3233_,
                    v___y_3226_,
                    v___y_3227_,
                    v___y_3228_,
                    v___y_3229_,
                );
                if crate::leanh::lean_obj_tag(v___x_3234_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_3234_, 1);
                    crate::leanh::lean_inc(v___y_3229_);
                    crate::leanh::lean_inc_ref(v___y_3228_);
                    crate::leanh::lean_inc(v___y_3227_);
                    crate::leanh::lean_inc_ref(v___y_3226_);
                    crate::leanh::lean_inc(v___y_3225_);
                    crate::leanh::lean_inc_ref(v___y_3224_);
                    crate::leanh::lean_inc(v___y_3223_);
                    crate::leanh::lean_inc_ref(v___y_3222_);
                    crate::leanh::lean_inc_ref(v_h_3221_);
                    crate::leanh::lean_inc_ref(v_a_3209_);
                    v___x_3235_ = crate::leanh::lean_apply_11(
                        v_k_3211_,
                        v_a_3209_,
                        v_h_3221_,
                        v___y_3222_,
                        v___y_3223_,
                        v___y_3224_,
                        v___y_3225_,
                        v___y_3226_,
                        v___y_3227_,
                        v___y_3228_,
                        v___y_3229_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_3235_) == 0 {
                        v_a_3236_ = crate::leanh::lean_ctor_get(v___x_3235_, 0);
                        crate::leanh::lean_inc(v_a_3236_);
                        crate::leanh::lean_dec_ref_known(v___x_3235_, 1);
                        v_snd_3237_ = crate::leanh::lean_ctor_get(v_a_3236_, 1);
                        v_fst_3238_ = crate::leanh::lean_ctor_get(v_a_3236_, 0);
                        v_isSharedCheck_3293_ = (!crate::leanh::lean_is_exclusive(v_a_3236_)) as u8;
                        if v_isSharedCheck_3293_ == 0 {
                            v___x_3240_ = v_a_3236_;
                            v_isShared_3241_ = v_isSharedCheck_3293_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_3237_);
                            crate::leanh::lean_inc(v_fst_3238_);
                            crate::leanh::lean_dec(v_a_3236_);
                            v___x_3240_ = crate::leanh::lean_box(0);
                            v_isShared_3241_ = v_isSharedCheck_3293_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_h_3221_);
                        crate::leanh::lean_dec(v_a_3220_);
                        crate::leanh::lean_dec_ref(v_a_3219_);
                        crate::leanh::lean_dec_ref(v_hyp_3218_);
                        crate::leanh::lean_dec_ref(v_00_u03c3s_3217_);
                        crate::leanh::lean_dec(v___x_3216_);
                        crate::leanh::lean_dec_ref(v___x_3215_);
                        crate::leanh::lean_dec_ref(v___x_3214_);
                        crate::leanh::lean_dec_ref(v___x_3213_);
                        crate::leanh::lean_dec_ref(v___x_3212_);
                        crate::leanh::lean_dec_ref(v_a_3209_);
                        return v___x_3235_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_h_3221_);
                    crate::leanh::lean_dec(v_a_3220_);
                    crate::leanh::lean_dec_ref(v_a_3219_);
                    crate::leanh::lean_dec_ref(v_hyp_3218_);
                    crate::leanh::lean_dec_ref(v_00_u03c3s_3217_);
                    crate::leanh::lean_dec(v___x_3216_);
                    crate::leanh::lean_dec_ref(v___x_3215_);
                    crate::leanh::lean_dec_ref(v___x_3214_);
                    crate::leanh::lean_dec_ref(v___x_3213_);
                    crate::leanh::lean_dec_ref(v___x_3212_);
                    crate::leanh::lean_dec_ref(v_k_3211_);
                    crate::leanh::lean_dec_ref(v_a_3209_);
                    v_a_3294_ = crate::leanh::lean_ctor_get(v___x_3234_, 0);
                    v_isSharedCheck_3301_ = (!crate::leanh::lean_is_exclusive(v___x_3234_)) as u8;
                    if v_isSharedCheck_3301_ == 0 {
                        v___x_3296_ = v___x_3234_;
                        v_isShared_3297_ = v_isSharedCheck_3301_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3294_);
                        crate::leanh::lean_dec(v___x_3234_);
                        v___x_3296_ = crate::leanh::lean_box(0);
                        v_isShared_3297_ = v_isSharedCheck_3301_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_3242_ = crate::leanh::lean_ctor_get(v_snd_3237_, 0);
                v_snd_3243_ = crate::leanh::lean_ctor_get(v_snd_3237_, 1);
                v_isSharedCheck_3292_ = (!crate::leanh::lean_is_exclusive(v_snd_3237_)) as u8;
                if v_isSharedCheck_3292_ == 0 {
                    v___x_3245_ = v_snd_3237_;
                    v_isShared_3246_ = v_isSharedCheck_3292_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3243_);
                    crate::leanh::lean_inc(v_fst_3242_);
                    crate::leanh::lean_dec(v_snd_3237_);
                    v___x_3245_ = crate::leanh::lean_box(0);
                    v_isShared_3246_ = v_isSharedCheck_3292_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3247_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3248_ = lean_mk_empty_array_with_capacity(v___x_3247_);
                v___x_3249_ = lean_array_push(v___x_3248_, v_h_3221_);
                v___x_3250_ = 1;
                v___x_3251_ = 1;
                v___x_3252_ = l_Lean_Meta_mkLambdaFVars(
                    v___x_3249_,
                    v_snd_3243_,
                    v___x_3233_,
                    v___x_3250_,
                    v___x_3233_,
                    v___x_3250_,
                    v___x_3251_,
                    v___y_3226_,
                    v___y_3227_,
                    v___y_3228_,
                    v___y_3229_,
                );
                crate::leanh::lean_dec_ref(v___x_3249_);
                if crate::leanh::lean_obj_tag(v___x_3252_) == 0 {
                    v_a_3253_ = crate::leanh::lean_ctor_get(v___x_3252_, 0);
                    v_isSharedCheck_3283_ = (!crate::leanh::lean_is_exclusive(v___x_3252_)) as u8;
                    if v_isSharedCheck_3283_ == 0 {
                        v___x_3255_ = v___x_3252_;
                        v_isShared_3256_ = v_isSharedCheck_3283_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3253_);
                        crate::leanh::lean_dec(v___x_3252_);
                        v___x_3255_ = crate::leanh::lean_box(0);
                        v_isShared_3256_ = v_isSharedCheck_3283_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3245_);
                    crate::leanh::lean_dec(v_fst_3242_);
                    crate::leanh::lean_del_object(v___x_3240_);
                    crate::leanh::lean_dec(v_fst_3238_);
                    crate::leanh::lean_dec(v_a_3220_);
                    crate::leanh::lean_dec_ref(v_a_3219_);
                    crate::leanh::lean_dec_ref(v_hyp_3218_);
                    crate::leanh::lean_dec_ref(v_00_u03c3s_3217_);
                    crate::leanh::lean_dec(v___x_3216_);
                    crate::leanh::lean_dec_ref(v___x_3215_);
                    crate::leanh::lean_dec_ref(v___x_3214_);
                    crate::leanh::lean_dec_ref(v___x_3213_);
                    crate::leanh::lean_dec_ref(v___x_3212_);
                    crate::leanh::lean_dec_ref(v_a_3209_);
                    v_a_3284_ = crate::leanh::lean_ctor_get(v___x_3252_, 0);
                    v_isSharedCheck_3291_ = (!crate::leanh::lean_is_exclusive(v___x_3252_)) as u8;
                    if v_isSharedCheck_3291_ == 0 {
                        v___x_3286_ = v___x_3252_;
                        v_isShared_3287_ = v_isSharedCheck_3291_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3284_);
                        crate::leanh::lean_dec(v___x_3252_);
                        v___x_3286_ = crate::leanh::lean_box(0);
                        v_isShared_3287_ = v_isSharedCheck_3291_;
                        state = 9;
                        continue;
                    }
                }
            }
            3 => {
                v_u_3257_ = crate::leanh::lean_ctor_get(v_fst_3242_, 0);
                v_00_u03c3s_3258_ = crate::leanh::lean_ctor_get(v_fst_3242_, 1);
                v_hyps_3259_ = crate::leanh::lean_ctor_get(v_fst_3242_, 2);
                v_target_3260_ = crate::leanh::lean_ctor_get(v_fst_3242_, 3);
                v_isSharedCheck_3282_ = (!crate::leanh::lean_is_exclusive(v_fst_3242_)) as u8;
                if v_isSharedCheck_3282_ == 0 {
                    v___x_3262_ = v_fst_3242_;
                    v_isShared_3263_ = v_isSharedCheck_3282_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_target_3260_);
                    crate::leanh::lean_inc(v_hyps_3259_);
                    crate::leanh::lean_inc(v_00_u03c3s_3258_);
                    crate::leanh::lean_inc(v_u_3257_);
                    crate::leanh::lean_dec(v_fst_3242_);
                    v___x_3262_ = crate::leanh::lean_box(0);
                    v_isShared_3263_ = v_isSharedCheck_3282_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3264_ =
                    l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__2___closed__0;
                v___x_3265_ =
                    l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__2___closed__1;
                v___x_3266_ = l_Lean_Name_mkStr6(
                    v___x_3212_,
                    v___x_3213_,
                    v___x_3214_,
                    v___x_3215_,
                    v___x_3264_,
                    v___x_3265_,
                );
                v___x_3267_ = l_Lean_mkConst(v___x_3266_, v___x_3216_);
                crate::leanh::lean_inc_ref(v_target_3260_);
                crate::leanh::lean_inc_ref(v_hyp_3218_);
                crate::leanh::lean_inc_ref(v_hyps_3259_);
                crate::leanh::lean_inc_ref(v_00_u03c3s_3217_);
                v_prf_3268_ = l_Lean_mkApp7(
                    v___x_3267_,
                    v_00_u03c3s_3217_,
                    v_hyps_3259_,
                    v_hyp_3218_,
                    v_target_3260_,
                    v_a_3209_,
                    v_a_3219_,
                    v_a_3253_,
                );
                v___x_3269_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(
                    v_a_3220_,
                    v_00_u03c3s_3217_,
                    v_hyps_3259_,
                    v_hyp_3218_,
                );
                if v_isShared_3263_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3262_, 2, v___x_3269_);
                    v_goal_3271_ = v___x_3262_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3281_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3281_, 0, v_u_3257_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3281_, 1, v_00_u03c3s_3258_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3281_, 2, v___x_3269_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3281_, 3, v_target_3260_);
                    v_goal_3271_ = v_reuseFailAlloc_3281_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_3246_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3245_, 1, v_prf_3268_);
                    crate::leanh::lean_ctor_set(v___x_3245_, 0, v_goal_3271_);
                    v___x_3273_ = v___x_3245_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3280_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3280_, 0, v_goal_3271_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3280_, 1, v_prf_3268_);
                    v___x_3273_ = v_reuseFailAlloc_3280_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_3241_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3240_, 1, v___x_3273_);
                    v___x_3275_ = v___x_3240_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3279_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3279_, 0, v_fst_3238_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3279_, 1, v___x_3273_);
                    v___x_3275_ = v_reuseFailAlloc_3279_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_3256_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3255_, 0, v___x_3275_);
                    v___x_3277_ = v___x_3255_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3278_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3278_, 0, v___x_3275_);
                    v___x_3277_ = v_reuseFailAlloc_3278_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3277_;
            }
            9 => {
                if v_isShared_3287_ == 0 {
                    v___x_3289_ = v___x_3286_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3290_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3290_, 0, v_a_3284_);
                    v___x_3289_ = v_reuseFailAlloc_3290_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3289_;
            }
            11 => {
                if v_isShared_3297_ == 0 {
                    v___x_3299_ = v___x_3296_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3300_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3300_, 0, v_a_3294_);
                    v___x_3299_ = v_reuseFailAlloc_3300_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3299_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1___redArg___lam__0___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3302_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_snd_3303_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_k_3304_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v___x_3305_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v___x_3306_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___x_3307_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___x_3308_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___x_3309_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_00_u03c3s_3310_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_hyp_3311_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_a_3312_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_a_3313_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_h_3314_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_3315_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_3316_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_3317_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_3318_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_3319_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___y_3320_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v___y_3321_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v___y_3322_: *mut crate::leanh::LeanObject = *_args.add(20);
    let mut v___y_3323_: *mut crate::leanh::LeanObject = *_args.add(21);
    let mut v_res_3324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3324_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1___redArg___lam__0(v_a_3302_, v_snd_3303_, v_k_3304_, v___x_3305_, v___x_3306_, v___x_3307_, v___x_3308_, v___x_3309_, v_00_u03c3s_3310_, v_hyp_3311_, v_a_3312_, v_a_3313_, v_h_3314_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_);
    crate::leanh::lean_dec(v___y_3322_);
    crate::leanh::lean_dec_ref(v___y_3321_);
    crate::leanh::lean_dec(v___y_3320_);
    crate::leanh::lean_dec_ref(v___y_3319_);
    crate::leanh::lean_dec(v___y_3318_);
    crate::leanh::lean_dec_ref(v___y_3317_);
    crate::leanh::lean_dec(v___y_3316_);
    crate::leanh::lean_dec_ref(v___y_3315_);
    return v_res_3324_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1___redArg(
    mut v_00_u03c3s_3325_: *mut crate::leanh::LeanObject,
    mut v_hyp_3326_: *mut crate::leanh::LeanObject,
    mut v_name_3327_: *mut crate::leanh::LeanObject,
    mut v_k_3328_: *mut crate::leanh::LeanObject,
    mut v___y_3329_: *mut crate::leanh::LeanObject,
    mut v___y_3330_: *mut crate::leanh::LeanObject,
    mut v___y_3331_: *mut crate::leanh::LeanObject,
    mut v___y_3332_: *mut crate::leanh::LeanObject,
    mut v___y_3333_: *mut crate::leanh::LeanObject,
    mut v___y_3334_: *mut crate::leanh::LeanObject,
    mut v___y_3335_: *mut crate::leanh::LeanObject,
    mut v___y_3336_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3341_: u8 = 0;
    let mut v___x_3342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3366_: u8 = 0;
    let mut v___x_3368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3370_: u8 = 0;
    let mut v_a_3371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3374_: u8 = 0;
    let mut v___x_3376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3378_: u8 = 0;
    let mut v_a_3379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3382_: u8 = 0;
    let mut v___x_3384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3386_: u8 = 0;
    let mut v_a_3387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3390_: u8 = 0;
    let mut v___x_3392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3394_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3338_ = l_Lean_Meta_mkFreshLevelMVar(
                    v___y_3333_,
                    v___y_3334_,
                    v___y_3335_,
                    v___y_3336_,
                );
                if crate::leanh::lean_obj_tag(v___x_3338_) == 0 {
                    v_a_3339_ = crate::leanh::lean_ctor_get(v___x_3338_, 0);
                    crate::leanh::lean_inc(v_a_3339_);
                    crate::leanh::lean_dec_ref_known(v___x_3338_, 1);
                    v___x_3340_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__1_once), _init_l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__1);
                    v___x_3341_ = 0;
                    v___x_3342_ = crate::leanh::lean_box(0);
                    v___x_3343_ = l_Lean_Meta_mkFreshExprMVar(
                        v___x_3340_,
                        v___x_3341_,
                        v___x_3342_,
                        v___y_3333_,
                        v___y_3334_,
                        v___y_3335_,
                        v___y_3336_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3343_) == 0 {
                        v_a_3344_ = crate::leanh::lean_ctor_get(v___x_3343_, 0);
                        crate::leanh::lean_inc_n(v_a_3344_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_3343_, 1);
                        v___x_3345_ =
                            l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__0;
                        v___x_3346_ =
                            l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__1;
                        v___x_3347_ =
                            l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__2;
                        v___x_3348_ =
                            l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__3;
                        v___x_3349_ =
                            l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__5;
                        v___x_3350_ = crate::leanh::lean_box(0);
                        crate::leanh::lean_inc(v_a_3339_);
                        v___x_3351_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3351_, 0, v_a_3339_);
                        crate::leanh::lean_ctor_set(v___x_3351_, 1, v___x_3350_);
                        crate::leanh::lean_inc_ref(v___x_3351_);
                        v___x_3352_ = l_Lean_mkConst(v___x_3349_, v___x_3351_);
                        crate::leanh::lean_inc_ref(v_hyp_3326_);
                        crate::leanh::lean_inc_ref(v_00_u03c3s_3325_);
                        v___x_3353_ =
                            l_Lean_mkApp3(v___x_3352_, v_00_u03c3s_3325_, v_hyp_3326_, v_a_3344_);
                        v___x_3354_ = crate::leanh::lean_box(0);
                        v___x_3355_ = l_Lean_Meta_synthInstance(
                            v___x_3353_,
                            v___x_3354_,
                            v___y_3333_,
                            v___y_3334_,
                            v___y_3335_,
                            v___y_3336_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3355_) == 0 {
                            v_a_3356_ = crate::leanh::lean_ctor_get(v___x_3355_, 0);
                            crate::leanh::lean_inc(v_a_3356_);
                            crate::leanh::lean_dec_ref_known(v___x_3355_, 1);
                            v___x_3357_ = l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName(
                                v_name_3327_,
                                v___y_3335_,
                                v___y_3336_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_3357_) == 0 {
                                v_a_3358_ = crate::leanh::lean_ctor_get(v___x_3357_, 0);
                                crate::leanh::lean_inc(v_a_3358_);
                                crate::leanh::lean_dec_ref_known(v___x_3357_, 1);
                                v_fst_3359_ = crate::leanh::lean_ctor_get(v_a_3358_, 0);
                                crate::leanh::lean_inc(v_fst_3359_);
                                v_snd_3360_ = crate::leanh::lean_ctor_get(v_a_3358_, 1);
                                crate::leanh::lean_inc(v_snd_3360_);
                                crate::leanh::lean_dec(v_a_3358_);
                                crate::leanh::lean_inc(v_a_3344_);
                                v___f_3361_ = crate::leanh::lean_alloc_closure(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 22, 12);
                                crate::leanh::lean_closure_set(v___f_3361_, 0, v_a_3344_);
                                crate::leanh::lean_closure_set(v___f_3361_, 1, v_snd_3360_);
                                crate::leanh::lean_closure_set(v___f_3361_, 2, v_k_3328_);
                                crate::leanh::lean_closure_set(v___f_3361_, 3, v___x_3345_);
                                crate::leanh::lean_closure_set(v___f_3361_, 4, v___x_3346_);
                                crate::leanh::lean_closure_set(v___f_3361_, 5, v___x_3347_);
                                crate::leanh::lean_closure_set(v___f_3361_, 6, v___x_3348_);
                                crate::leanh::lean_closure_set(v___f_3361_, 7, v___x_3351_);
                                crate::leanh::lean_closure_set(v___f_3361_, 8, v_00_u03c3s_3325_);
                                crate::leanh::lean_closure_set(v___f_3361_, 9, v_hyp_3326_);
                                crate::leanh::lean_closure_set(v___f_3361_, 10, v_a_3356_);
                                crate::leanh::lean_closure_set(v___f_3361_, 11, v_a_3339_);
                                v___x_3362_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1___redArg(v_fst_3359_, v_a_3344_, v___f_3361_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_);
                                return v___x_3362_;
                            } else {
                                crate::leanh::lean_dec(v_a_3356_);
                                crate::leanh::lean_dec_ref_known(v___x_3351_, 2);
                                crate::leanh::lean_dec(v_a_3344_);
                                crate::leanh::lean_dec(v_a_3339_);
                                crate::leanh::lean_dec_ref(v_k_3328_);
                                crate::leanh::lean_dec_ref(v_hyp_3326_);
                                crate::leanh::lean_dec_ref(v_00_u03c3s_3325_);
                                v_a_3363_ = crate::leanh::lean_ctor_get(v___x_3357_, 0);
                                v_isSharedCheck_3370_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3357_)) as u8;
                                if v_isSharedCheck_3370_ == 0 {
                                    v___x_3365_ = v___x_3357_;
                                    v_isShared_3366_ = v_isSharedCheck_3370_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3363_);
                                    crate::leanh::lean_dec(v___x_3357_);
                                    v___x_3365_ = crate::leanh::lean_box(0);
                                    v_isShared_3366_ = v_isSharedCheck_3370_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v___x_3351_, 2);
                            crate::leanh::lean_dec(v_a_3344_);
                            crate::leanh::lean_dec(v_a_3339_);
                            crate::leanh::lean_dec_ref(v_k_3328_);
                            crate::leanh::lean_dec(v_name_3327_);
                            crate::leanh::lean_dec_ref(v_hyp_3326_);
                            crate::leanh::lean_dec_ref(v_00_u03c3s_3325_);
                            v_a_3371_ = crate::leanh::lean_ctor_get(v___x_3355_, 0);
                            v_isSharedCheck_3378_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3355_)) as u8;
                            if v_isSharedCheck_3378_ == 0 {
                                v___x_3373_ = v___x_3355_;
                                v_isShared_3374_ = v_isSharedCheck_3378_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3371_);
                                crate::leanh::lean_dec(v___x_3355_);
                                v___x_3373_ = crate::leanh::lean_box(0);
                                v_isShared_3374_ = v_isSharedCheck_3378_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3339_);
                        crate::leanh::lean_dec_ref(v_k_3328_);
                        crate::leanh::lean_dec(v_name_3327_);
                        crate::leanh::lean_dec_ref(v_hyp_3326_);
                        crate::leanh::lean_dec_ref(v_00_u03c3s_3325_);
                        v_a_3379_ = crate::leanh::lean_ctor_get(v___x_3343_, 0);
                        v_isSharedCheck_3386_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3343_)) as u8;
                        if v_isSharedCheck_3386_ == 0 {
                            v___x_3381_ = v___x_3343_;
                            v_isShared_3382_ = v_isSharedCheck_3386_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3379_);
                            crate::leanh::lean_dec(v___x_3343_);
                            v___x_3381_ = crate::leanh::lean_box(0);
                            v_isShared_3382_ = v_isSharedCheck_3386_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_k_3328_);
                    crate::leanh::lean_dec(v_name_3327_);
                    crate::leanh::lean_dec_ref(v_hyp_3326_);
                    crate::leanh::lean_dec_ref(v_00_u03c3s_3325_);
                    v_a_3387_ = crate::leanh::lean_ctor_get(v___x_3338_, 0);
                    v_isSharedCheck_3394_ = (!crate::leanh::lean_is_exclusive(v___x_3338_)) as u8;
                    if v_isSharedCheck_3394_ == 0 {
                        v___x_3389_ = v___x_3338_;
                        v_isShared_3390_ = v_isSharedCheck_3394_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3387_);
                        crate::leanh::lean_dec(v___x_3338_);
                        v___x_3389_ = crate::leanh::lean_box(0);
                        v_isShared_3390_ = v_isSharedCheck_3394_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3366_ == 0 {
                    v___x_3368_ = v___x_3365_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3369_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3369_, 0, v_a_3363_);
                    v___x_3368_ = v_reuseFailAlloc_3369_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3368_;
            }
            3 => {
                if v_isShared_3374_ == 0 {
                    v___x_3376_ = v___x_3373_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3377_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3377_, 0, v_a_3371_);
                    v___x_3376_ = v_reuseFailAlloc_3377_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3376_;
            }
            5 => {
                if v_isShared_3382_ == 0 {
                    v___x_3384_ = v___x_3381_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3385_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3385_, 0, v_a_3379_);
                    v___x_3384_ = v_reuseFailAlloc_3385_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3384_;
            }
            7 => {
                if v_isShared_3390_ == 0 {
                    v___x_3392_ = v___x_3389_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3393_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3393_, 0, v_a_3387_);
                    v___x_3392_ = v_reuseFailAlloc_3393_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3392_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1___redArg___boxed(
    mut v_00_u03c3s_3395_: *mut crate::leanh::LeanObject,
    mut v_hyp_3396_: *mut crate::leanh::LeanObject,
    mut v_name_3397_: *mut crate::leanh::LeanObject,
    mut v_k_3398_: *mut crate::leanh::LeanObject,
    mut v___y_3399_: *mut crate::leanh::LeanObject,
    mut v___y_3400_: *mut crate::leanh::LeanObject,
    mut v___y_3401_: *mut crate::leanh::LeanObject,
    mut v___y_3402_: *mut crate::leanh::LeanObject,
    mut v___y_3403_: *mut crate::leanh::LeanObject,
    mut v___y_3404_: *mut crate::leanh::LeanObject,
    mut v___y_3405_: *mut crate::leanh::LeanObject,
    mut v___y_3406_: *mut crate::leanh::LeanObject,
    mut v___y_3407_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3408_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1___redArg(v_00_u03c3s_3395_, v_hyp_3396_, v_name_3397_, v_k_3398_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_, v___y_3404_, v___y_3405_, v___y_3406_);
    crate::leanh::lean_dec(v___y_3406_);
    crate::leanh::lean_dec_ref(v___y_3405_);
    crate::leanh::lean_dec(v___y_3404_);
    crate::leanh::lean_dec_ref(v___y_3403_);
    crate::leanh::lean_dec(v___y_3402_);
    crate::leanh::lean_dec_ref(v___y_3401_);
    crate::leanh::lean_dec(v___y_3400_);
    crate::leanh::lean_dec_ref(v___y_3399_);
    return v_res_3408_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6_spec__7_spec__8___redArg(
    mut v_x_3409_: *mut crate::leanh::LeanObject,
    mut v_x_3410_: *mut crate::leanh::LeanObject,
    mut v_x_3411_: *mut crate::leanh::LeanObject,
    mut v_x_3412_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_3413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3417_: u8 = 0;
    let mut v___x_3418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3419_: u8 = 0;
    let mut v___x_3420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_3425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: u8 = 0;
    let mut v___x_3428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3438_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_3413_ = crate::leanh::lean_ctor_get(v_x_3409_, 0);
                v_vs_3414_ = crate::leanh::lean_ctor_get(v_x_3409_, 1);
                v_isSharedCheck_3438_ = (!crate::leanh::lean_is_exclusive(v_x_3409_)) as u8;
                if v_isSharedCheck_3438_ == 0 {
                    v___x_3416_ = v_x_3409_;
                    v_isShared_3417_ = v_isSharedCheck_3438_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_3414_);
                    crate::leanh::lean_inc(v_ks_3413_);
                    crate::leanh::lean_dec(v_x_3409_);
                    v___x_3416_ = crate::leanh::lean_box(0);
                    v_isShared_3417_ = v_isSharedCheck_3438_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3418_ = lean_array_get_size(v_ks_3413_);
                v___x_3419_ = lean_nat_dec_lt(v_x_3410_, v___x_3418_);
                if v___x_3419_ == 0 {
                    crate::leanh::lean_dec(v_x_3410_);
                    v___x_3420_ = lean_array_push(v_ks_3413_, v_x_3411_);
                    v___x_3421_ = lean_array_push(v_vs_3414_, v_x_3412_);
                    if v_isShared_3417_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3416_, 1, v___x_3421_);
                        crate::leanh::lean_ctor_set(v___x_3416_, 0, v___x_3420_);
                        v___x_3423_ = v___x_3416_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3424_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3424_, 0, v___x_3420_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3424_, 1, v___x_3421_);
                        v___x_3423_ = v_reuseFailAlloc_3424_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_3425_ = lean_array_fget_borrowed(v_ks_3413_, v_x_3410_);
                    v___x_3426_ = l_Lean_instBEqMVarId_beq(v_x_3411_, v_k_x27_3425_);
                    if v___x_3426_ == 0 {
                        if v_isShared_3417_ == 0 {
                            v___x_3428_ = v___x_3416_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3432_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3432_, 0, v_ks_3413_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3432_, 1, v_vs_3414_);
                            v___x_3428_ = v_reuseFailAlloc_3432_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_3433_ = lean_array_fset(v_ks_3413_, v_x_3410_, v_x_3411_);
                        v___x_3434_ = lean_array_fset(v_vs_3414_, v_x_3410_, v_x_3412_);
                        crate::leanh::lean_dec(v_x_3410_);
                        if v_isShared_3417_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3416_, 1, v___x_3434_);
                            crate::leanh::lean_ctor_set(v___x_3416_, 0, v___x_3433_);
                            v___x_3436_ = v___x_3416_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_3437_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3437_, 0, v___x_3433_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3437_, 1, v___x_3434_);
                            v___x_3436_ = v_reuseFailAlloc_3437_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_3423_;
            }
            3 => {
                v___x_3429_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3430_ = lean_nat_add(v_x_3410_, v___x_3429_);
                crate::leanh::lean_dec(v_x_3410_);
                v_x_3409_ = v___x_3428_;
                v_x_3410_ = v___x_3430_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_3436_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6_spec__7___redArg(
    mut v_n_3439_: *mut crate::leanh::LeanObject,
    mut v_k_3440_: *mut crate::leanh::LeanObject,
    mut v_v_3441_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3442_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3443_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6_spec__7_spec__8___redArg(v_n_3439_, v___x_3442_, v_k_3440_, v_v_3441_);
    return v___x_3443_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6___redArg___closed__0()
-> usize {
    let mut v___x_3444_: usize = 0;
    let mut v___x_3445_: usize = 0;
    let mut v___x_3446_: usize = 0;
    v___x_3444_ = 5usize;
    v___x_3445_ = 1usize;
    v___x_3446_ = lean_usize_shift_left(v___x_3445_, v___x_3444_);
    return v___x_3446_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6___redArg___closed__1()
-> usize {
    let mut v___x_3447_: usize = 0;
    let mut v___x_3448_: usize = 0;
    let mut v___x_3449_: usize = 0;
    v___x_3447_ = 1usize;
    v___x_3448_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6___redArg___closed__0);
    v___x_3449_ = lean_usize_sub(v___x_3448_, v___x_3447_);
    return v___x_3449_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3450_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_3450_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6___redArg(
    mut v_x_3451_: *mut crate::leanh::LeanObject,
    mut v_x_3452_: usize,
    mut v_x_3453_: usize,
    mut v_x_3454_: *mut crate::leanh::LeanObject,
    mut v_x_3455_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_3456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: usize = 0;
    let mut v___x_3458_: usize = 0;
    let mut v___x_3459_: usize = 0;
    let mut v___x_3460_: usize = 0;
    let mut v_j_3461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: u8 = 0;
    let mut v___x_3465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3466_: u8 = 0;
    let mut v_v_3467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_3469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3480_: u8 = 0;
    let mut v___x_3481_: u8 = 0;
    let mut v___x_3482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3487_: u8 = 0;
    let mut v_node_3488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3491_: u8 = 0;
    let mut v___x_3492_: usize = 0;
    let mut v___x_3493_: usize = 0;
    let mut v___x_3494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3498_: u8 = 0;
    let mut v___x_3499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3500_: u8 = 0;
    let mut v_unused_3501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_3502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3506_: u8 = 0;
    let mut v___x_3508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_3509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3511_: u8 = 0;
    let mut v_ks_3512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3517_: usize = 0;
    let mut v___x_3518_: u8 = 0;
    let mut v___x_3519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3521_: u8 = 0;
    let mut v_reuseFailAlloc_3522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3523_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3451_) == 0 {
                    v_es_3456_ = crate::leanh::lean_ctor_get(v_x_3451_, 0);
                    v___x_3457_ = 5usize;
                    v___x_3458_ = 1usize;
                    v___x_3459_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6___redArg___closed__1);
                    v___x_3460_ = lean_usize_land(v_x_3452_, v___x_3459_);
                    v_j_3461_ = lean_usize_to_nat(v___x_3460_);
                    v___x_3462_ = lean_array_get_size(v_es_3456_);
                    v___x_3463_ = lean_nat_dec_lt(v_j_3461_, v___x_3462_);
                    if v___x_3463_ == 0 {
                        crate::leanh::lean_dec(v_j_3461_);
                        crate::leanh::lean_dec(v_x_3455_);
                        crate::leanh::lean_dec(v_x_3454_);
                        return v_x_3451_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_3456_);
                        v_isSharedCheck_3500_ = (!crate::leanh::lean_is_exclusive(v_x_3451_)) as u8;
                        if v_isSharedCheck_3500_ == 0 {
                            v_unused_3501_ = crate::leanh::lean_ctor_get(v_x_3451_, 0);
                            crate::leanh::lean_dec(v_unused_3501_);
                            v___x_3465_ = v_x_3451_;
                            v_isShared_3466_ = v_isSharedCheck_3500_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_3451_);
                            v___x_3465_ = crate::leanh::lean_box(0);
                            v_isShared_3466_ = v_isSharedCheck_3500_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_3502_ = crate::leanh::lean_ctor_get(v_x_3451_, 0);
                    v_vs_3503_ = crate::leanh::lean_ctor_get(v_x_3451_, 1);
                    v_isSharedCheck_3523_ = (!crate::leanh::lean_is_exclusive(v_x_3451_)) as u8;
                    if v_isSharedCheck_3523_ == 0 {
                        v___x_3505_ = v_x_3451_;
                        v_isShared_3506_ = v_isSharedCheck_3523_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_3503_);
                        crate::leanh::lean_inc(v_ks_3502_);
                        crate::leanh::lean_dec(v_x_3451_);
                        v___x_3505_ = crate::leanh::lean_box(0);
                        v_isShared_3506_ = v_isSharedCheck_3523_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_3467_ = lean_array_fget(v_es_3456_, v_j_3461_);
                v___x_3468_ = crate::leanh::lean_box(0);
                v_xs_x27_3469_ = lean_array_fset(v_es_3456_, v_j_3461_, v___x_3468_);
                match crate::leanh::lean_obj_tag(v_v_3467_) {
                    0 => {
                        v_key_3476_ = crate::leanh::lean_ctor_get(v_v_3467_, 0);
                        v_val_3477_ = crate::leanh::lean_ctor_get(v_v_3467_, 1);
                        v_isSharedCheck_3487_ = (!crate::leanh::lean_is_exclusive(v_v_3467_)) as u8;
                        if v_isSharedCheck_3487_ == 0 {
                            v___x_3479_ = v_v_3467_;
                            v_isShared_3480_ = v_isSharedCheck_3487_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_3477_);
                            crate::leanh::lean_inc(v_key_3476_);
                            crate::leanh::lean_dec(v_v_3467_);
                            v___x_3479_ = crate::leanh::lean_box(0);
                            v_isShared_3480_ = v_isSharedCheck_3487_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_3488_ = crate::leanh::lean_ctor_get(v_v_3467_, 0);
                        v_isSharedCheck_3498_ = (!crate::leanh::lean_is_exclusive(v_v_3467_)) as u8;
                        if v_isSharedCheck_3498_ == 0 {
                            v___x_3490_ = v_v_3467_;
                            v_isShared_3491_ = v_isSharedCheck_3498_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_3488_);
                            crate::leanh::lean_dec(v_v_3467_);
                            v___x_3490_ = crate::leanh::lean_box(0);
                            v_isShared_3491_ = v_isSharedCheck_3498_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_3499_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3499_, 0, v_x_3454_);
                        crate::leanh::lean_ctor_set(v___x_3499_, 1, v_x_3455_);
                        v___y_3471_ = v___x_3499_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3472_ = lean_array_fset(v_xs_x27_3469_, v_j_3461_, v___y_3471_);
                crate::leanh::lean_dec(v_j_3461_);
                if v_isShared_3466_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3465_, 0, v___x_3472_);
                    v___x_3474_ = v___x_3465_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3475_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3475_, 0, v___x_3472_);
                    v___x_3474_ = v_reuseFailAlloc_3475_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3474_;
            }
            4 => {
                v___x_3481_ = l_Lean_instBEqMVarId_beq(v_x_3454_, v_key_3476_);
                if v___x_3481_ == 0 {
                    crate::leanh::lean_del_object(v___x_3479_);
                    v___x_3482_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_3476_,
                        v_val_3477_,
                        v_x_3454_,
                        v_x_3455_,
                    );
                    v___x_3483_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3483_, 0, v___x_3482_);
                    v___y_3471_ = v___x_3483_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_3477_);
                    crate::leanh::lean_dec(v_key_3476_);
                    if v_isShared_3480_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3479_, 1, v_x_3455_);
                        crate::leanh::lean_ctor_set(v___x_3479_, 0, v_x_3454_);
                        v___x_3485_ = v___x_3479_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3486_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3486_, 0, v_x_3454_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3486_, 1, v_x_3455_);
                        v___x_3485_ = v_reuseFailAlloc_3486_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_3471_ = v___x_3485_;
                state = 2;
                continue;
            }
            6 => {
                v___x_3492_ = lean_usize_shift_right(v_x_3452_, v___x_3457_);
                v___x_3493_ = lean_usize_add(v_x_3453_, v___x_3458_);
                v___x_3494_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6___redArg(v_node_3488_, v___x_3492_, v___x_3493_, v_x_3454_, v_x_3455_);
                if v_isShared_3491_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3490_, 0, v___x_3494_);
                    v___x_3496_ = v___x_3490_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3497_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3497_, 0, v___x_3494_);
                    v___x_3496_ = v_reuseFailAlloc_3497_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_3471_ = v___x_3496_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_3506_ == 0 {
                    v___x_3508_ = v___x_3505_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3522_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3522_, 0, v_ks_3502_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3522_, 1, v_vs_3503_);
                    v___x_3508_ = v_reuseFailAlloc_3522_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_3509_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6_spec__7___redArg(v___x_3508_, v_x_3454_, v_x_3455_);
                v___x_3517_ = 7usize;
                v___x_3518_ = lean_usize_dec_le(v___x_3517_, v_x_3453_);
                if v___x_3518_ == 0 {
                    v___x_3519_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3509_);
                    v___x_3520_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_3521_ = lean_nat_dec_lt(v___x_3519_, v___x_3520_);
                    crate::leanh::lean_dec(v___x_3519_);
                    v___y_3511_ = v___x_3521_;
                    state = 10;
                    continue;
                } else {
                    v___y_3511_ = v___x_3518_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_3511_ == 0 {
                    v_ks_3512_ = crate::leanh::lean_ctor_get(v_newNode_3509_, 0);
                    crate::leanh::lean_inc_ref(v_ks_3512_);
                    v_vs_3513_ = crate::leanh::lean_ctor_get(v_newNode_3509_, 1);
                    crate::leanh::lean_inc_ref(v_vs_3513_);
                    crate::leanh::lean_dec_ref(v_newNode_3509_);
                    v___x_3514_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3515_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6___redArg___closed__2);
                    v___x_3516_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6_spec__8___redArg(v_x_3453_, v_ks_3512_, v_vs_3513_, v___x_3514_, v___x_3515_);
                    crate::leanh::lean_dec_ref(v_vs_3513_);
                    crate::leanh::lean_dec_ref(v_ks_3512_);
                    return v___x_3516_;
                } else {
                    return v_newNode_3509_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6_spec__8___redArg(
    mut v_depth_3524_: usize,
    mut v_keys_3525_: *mut crate::leanh::LeanObject,
    mut v_vals_3526_: *mut crate::leanh::LeanObject,
    mut v_i_3527_: *mut crate::leanh::LeanObject,
    mut v_entries_3528_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3530_: u8 = 0;
    let mut v_k_3531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3533_: u64 = 0;
    let mut v_h_3534_: usize = 0;
    let mut v___x_3535_: usize = 0;
    let mut v___x_3536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3537_: usize = 0;
    let mut v___x_3538_: usize = 0;
    let mut v___x_3539_: usize = 0;
    let mut v_h_3540_: usize = 0;
    let mut v___x_3541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3529_ = lean_array_get_size(v_keys_3525_);
                v___x_3530_ = lean_nat_dec_lt(v_i_3527_, v___x_3529_);
                if v___x_3530_ == 0 {
                    crate::leanh::lean_dec(v_i_3527_);
                    return v_entries_3528_;
                } else {
                    v_k_3531_ = lean_array_fget_borrowed(v_keys_3525_, v_i_3527_);
                    v_v_3532_ = lean_array_fget_borrowed(v_vals_3526_, v_i_3527_);
                    v___x_3533_ = l_Lean_instHashableMVarId_hash(v_k_3531_);
                    v_h_3534_ = lean_uint64_to_usize(v___x_3533_);
                    v___x_3535_ = 5usize;
                    v___x_3536_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3537_ = 1usize;
                    v___x_3538_ = lean_usize_sub(v_depth_3524_, v___x_3537_);
                    v___x_3539_ = lean_usize_mul(v___x_3535_, v___x_3538_);
                    v_h_3540_ = lean_usize_shift_right(v_h_3534_, v___x_3539_);
                    v___x_3541_ = lean_nat_add(v_i_3527_, v___x_3536_);
                    crate::leanh::lean_dec(v_i_3527_);
                    crate::leanh::lean_inc(v_v_3532_);
                    crate::leanh::lean_inc(v_k_3531_);
                    v___x_3542_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6___redArg(v_entries_3528_, v_h_3540_, v_depth_3524_, v_k_3531_, v_v_3532_);
                    v_i_3527_ = v___x_3541_;
                    v_entries_3528_ = v___x_3542_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6_spec__8___redArg___boxed(
    mut v_depth_3544_: *mut crate::leanh::LeanObject,
    mut v_keys_3545_: *mut crate::leanh::LeanObject,
    mut v_vals_3546_: *mut crate::leanh::LeanObject,
    mut v_i_3547_: *mut crate::leanh::LeanObject,
    mut v_entries_3548_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_3549_: usize = 0;
    let mut v_res_3550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_3549_ = crate::leanh::lean_unbox_usize(v_depth_3544_);
    crate::leanh::lean_dec(v_depth_3544_);
    v_res_3550_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6_spec__8___redArg(v_depth_boxed_3549_, v_keys_3545_, v_vals_3546_, v_i_3547_, v_entries_3548_);
    crate::leanh::lean_dec_ref(v_vals_3546_);
    crate::leanh::lean_dec_ref(v_keys_3545_);
    return v_res_3550_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6___redArg___boxed(
    mut v_x_3551_: *mut crate::leanh::LeanObject,
    mut v_x_3552_: *mut crate::leanh::LeanObject,
    mut v_x_3553_: *mut crate::leanh::LeanObject,
    mut v_x_3554_: *mut crate::leanh::LeanObject,
    mut v_x_3555_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_10390__boxed_3556_: usize = 0;
    let mut v_x_10391__boxed_3557_: usize = 0;
    let mut v_res_3558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_10390__boxed_3556_ = crate::leanh::lean_unbox_usize(v_x_3552_);
    crate::leanh::lean_dec(v_x_3552_);
    v_x_10391__boxed_3557_ = crate::leanh::lean_unbox_usize(v_x_3553_);
    crate::leanh::lean_dec(v_x_3553_);
    v_res_3558_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6___redArg(v_x_3551_, v_x_10390__boxed_3556_, v_x_10391__boxed_3557_, v_x_3554_, v_x_3555_);
    return v_res_3558_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3___redArg(
    mut v_x_3559_: *mut crate::leanh::LeanObject,
    mut v_x_3560_: *mut crate::leanh::LeanObject,
    mut v_x_3561_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3562_: u64 = 0;
    let mut v___x_3563_: usize = 0;
    let mut v___x_3564_: usize = 0;
    let mut v___x_3565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3562_ = l_Lean_instHashableMVarId_hash(v_x_3560_);
    v___x_3563_ = lean_uint64_to_usize(v___x_3562_);
    v___x_3564_ = 1usize;
    v___x_3565_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6___redArg(v_x_3559_, v___x_3563_, v___x_3564_, v_x_3560_, v_x_3561_);
    return v___x_3565_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2___redArg(
    mut v_mvarId_3566_: *mut crate::leanh::LeanObject,
    mut v_val_3567_: *mut crate::leanh::LeanObject,
    mut v___y_3568_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_3574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3578_: u8 = 0;
    let mut v_depth_3579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_3580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_3581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_3582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lDecls_3583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_3584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userNames_3585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_3586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_3587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_3588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3591_: u8 = 0;
    let mut v___x_3592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3602_: u8 = 0;
    let mut v_isSharedCheck_3603_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3570_ = lean_st_ref_take(v___y_3568_);
                v_mctx_3571_ = crate::leanh::lean_ctor_get(v___x_3570_, 0);
                v_cache_3572_ = crate::leanh::lean_ctor_get(v___x_3570_, 1);
                v_zetaDeltaFVarIds_3573_ = crate::leanh::lean_ctor_get(v___x_3570_, 2);
                v_postponed_3574_ = crate::leanh::lean_ctor_get(v___x_3570_, 3);
                v_diag_3575_ = crate::leanh::lean_ctor_get(v___x_3570_, 4);
                v_isSharedCheck_3603_ = (!crate::leanh::lean_is_exclusive(v___x_3570_)) as u8;
                if v_isSharedCheck_3603_ == 0 {
                    v___x_3577_ = v___x_3570_;
                    v_isShared_3578_ = v_isSharedCheck_3603_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_3575_);
                    crate::leanh::lean_inc(v_postponed_3574_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_3573_);
                    crate::leanh::lean_inc(v_cache_3572_);
                    crate::leanh::lean_inc(v_mctx_3571_);
                    crate::leanh::lean_dec(v___x_3570_);
                    v___x_3577_ = crate::leanh::lean_box(0);
                    v_isShared_3578_ = v_isSharedCheck_3603_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_3579_ = crate::leanh::lean_ctor_get(v_mctx_3571_, 0);
                v_levelAssignDepth_3580_ = crate::leanh::lean_ctor_get(v_mctx_3571_, 1);
                v_lmvarCounter_3581_ = crate::leanh::lean_ctor_get(v_mctx_3571_, 2);
                v_mvarCounter_3582_ = crate::leanh::lean_ctor_get(v_mctx_3571_, 3);
                v_lDecls_3583_ = crate::leanh::lean_ctor_get(v_mctx_3571_, 4);
                v_decls_3584_ = crate::leanh::lean_ctor_get(v_mctx_3571_, 5);
                v_userNames_3585_ = crate::leanh::lean_ctor_get(v_mctx_3571_, 6);
                v_lAssignment_3586_ = crate::leanh::lean_ctor_get(v_mctx_3571_, 7);
                v_eAssignment_3587_ = crate::leanh::lean_ctor_get(v_mctx_3571_, 8);
                v_dAssignment_3588_ = crate::leanh::lean_ctor_get(v_mctx_3571_, 9);
                v_isSharedCheck_3602_ = (!crate::leanh::lean_is_exclusive(v_mctx_3571_)) as u8;
                if v_isSharedCheck_3602_ == 0 {
                    v___x_3590_ = v_mctx_3571_;
                    v_isShared_3591_ = v_isSharedCheck_3602_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_dAssignment_3588_);
                    crate::leanh::lean_inc(v_eAssignment_3587_);
                    crate::leanh::lean_inc(v_lAssignment_3586_);
                    crate::leanh::lean_inc(v_userNames_3585_);
                    crate::leanh::lean_inc(v_decls_3584_);
                    crate::leanh::lean_inc(v_lDecls_3583_);
                    crate::leanh::lean_inc(v_mvarCounter_3582_);
                    crate::leanh::lean_inc(v_lmvarCounter_3581_);
                    crate::leanh::lean_inc(v_levelAssignDepth_3580_);
                    crate::leanh::lean_inc(v_depth_3579_);
                    crate::leanh::lean_dec(v_mctx_3571_);
                    v___x_3590_ = crate::leanh::lean_box(0);
                    v_isShared_3591_ = v_isSharedCheck_3602_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3592_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3___redArg(v_eAssignment_3587_, v_mvarId_3566_, v_val_3567_);
                if v_isShared_3591_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3590_, 8, v___x_3592_);
                    v___x_3594_ = v___x_3590_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3601_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3601_, 0, v_depth_3579_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3601_,
                        1,
                        v_levelAssignDepth_3580_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3601_, 2, v_lmvarCounter_3581_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3601_, 3, v_mvarCounter_3582_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3601_, 4, v_lDecls_3583_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3601_, 5, v_decls_3584_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3601_, 6, v_userNames_3585_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3601_, 7, v_lAssignment_3586_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3601_, 8, v___x_3592_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3601_, 9, v_dAssignment_3588_);
                    v___x_3594_ = v_reuseFailAlloc_3601_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3578_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3577_, 0, v___x_3594_);
                    v___x_3596_ = v___x_3577_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3600_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3600_, 0, v___x_3594_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3600_, 1, v_cache_3572_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3600_,
                        2,
                        v_zetaDeltaFVarIds_3573_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3600_, 3, v_postponed_3574_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3600_, 4, v_diag_3575_);
                    v___x_3596_ = v_reuseFailAlloc_3600_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3597_ = lean_st_ref_set(v___y_3568_, v___x_3596_);
                v___x_3598_ = crate::leanh::lean_box(0);
                v___x_3599_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3599_, 0, v___x_3598_);
                return v___x_3599_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2___redArg___boxed(
    mut v_mvarId_3604_: *mut crate::leanh::LeanObject,
    mut v_val_3605_: *mut crate::leanh::LeanObject,
    mut v___y_3606_: *mut crate::leanh::LeanObject,
    mut v___y_3607_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3608_ =
        l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2___redArg(
            v_mvarId_3604_,
            v_val_3605_,
            v___y_3606_,
        );
    crate::leanh::lean_dec(v___y_3606_);
    return v_res_3608_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___lam__1(
    mut v_snd_3610_: *mut crate::leanh::LeanObject,
    mut v_hyp_3611_: *mut crate::leanh::LeanObject,
    mut v___x_3612_: *mut crate::leanh::LeanObject,
    mut v_fst_3613_: *mut crate::leanh::LeanObject,
    mut v___y_3614_: *mut crate::leanh::LeanObject,
    mut v___y_3615_: *mut crate::leanh::LeanObject,
    mut v___y_3616_: *mut crate::leanh::LeanObject,
    mut v___y_3617_: *mut crate::leanh::LeanObject,
    mut v___y_3618_: *mut crate::leanh::LeanObject,
    mut v___y_3619_: *mut crate::leanh::LeanObject,
    mut v___y_3620_: *mut crate::leanh::LeanObject,
    mut v___y_3621_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_00_u03c3s_3626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_focusHyp_3627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: u8 = 0;
    let mut v___x_3630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3641_: u8 = 0;
    let mut v___x_3642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3650_: u8 = 0;
    let mut v_unused_3651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3655_: u8 = 0;
    let mut v___x_3657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3659_: u8 = 0;
    let mut v_a_3660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3663_: u8 = 0;
    let mut v___x_3665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3667_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_hyp_3611_);
                crate::leanh::lean_inc_ref(v_snd_3610_);
                v___x_3623_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo(
                    v_snd_3610_,
                    v_hyp_3611_,
                    v___y_3618_,
                    v___y_3619_,
                    v___y_3620_,
                    v___y_3621_,
                );
                if crate::leanh::lean_obj_tag(v___x_3623_) == 0 {
                    v_a_3624_ = crate::leanh::lean_ctor_get(v___x_3623_, 0);
                    crate::leanh::lean_inc_n(v_a_3624_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_3623_, 1);
                    v_ref_3625_ = crate::leanh::lean_ctor_get(v___y_3620_, 5);
                    v_00_u03c3s_3626_ = crate::leanh::lean_ctor_get(v_snd_3610_, 1);
                    v_focusHyp_3627_ = crate::leanh::lean_ctor_get(v_a_3624_, 0);
                    crate::leanh::lean_inc_ref(v_snd_3610_);
                    v___f_3628_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___lam__0___boxed
                            as *mut core::ffi::c_void,
                        13,
                        2,
                    );
                    crate::leanh::lean_closure_set(v___f_3628_, 0, v_a_3624_);
                    crate::leanh::lean_closure_set(v___f_3628_, 1, v_snd_3610_);
                    v___x_3629_ = 0;
                    v___x_3630_ = l_Lean_SourceInfo_fromRef(v_ref_3625_, v___x_3629_);
                    v___x_3631_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___lam__1___closed__0;
                    v___x_3632_ = l_Lean_Name_mkStr2(v___x_3612_, v___x_3631_);
                    v___x_3633_ = l_Lean_Syntax_node1(v___x_3630_, v___x_3632_, v_hyp_3611_);
                    crate::leanh::lean_inc_ref(v_focusHyp_3627_);
                    crate::leanh::lean_inc_ref(v_00_u03c3s_3626_);
                    v___x_3634_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1___redArg(v_00_u03c3s_3626_, v_focusHyp_3627_, v___x_3633_, v___f_3628_, v___y_3614_, v___y_3615_, v___y_3616_, v___y_3617_, v___y_3618_, v___y_3619_, v___y_3620_, v___y_3621_);
                    if crate::leanh::lean_obj_tag(v___x_3634_) == 0 {
                        v_a_3635_ = crate::leanh::lean_ctor_get(v___x_3634_, 0);
                        crate::leanh::lean_inc(v_a_3635_);
                        crate::leanh::lean_dec_ref_known(v___x_3634_, 1);
                        v_snd_3636_ = crate::leanh::lean_ctor_get(v_a_3635_, 1);
                        crate::leanh::lean_inc(v_snd_3636_);
                        v_fst_3637_ = crate::leanh::lean_ctor_get(v_a_3635_, 0);
                        crate::leanh::lean_inc(v_fst_3637_);
                        crate::leanh::lean_dec(v_a_3635_);
                        v_snd_3638_ = crate::leanh::lean_ctor_get(v_snd_3636_, 1);
                        v_isSharedCheck_3650_ =
                            (!crate::leanh::lean_is_exclusive(v_snd_3636_)) as u8;
                        if v_isSharedCheck_3650_ == 0 {
                            v_unused_3651_ = crate::leanh::lean_ctor_get(v_snd_3636_, 0);
                            crate::leanh::lean_dec(v_unused_3651_);
                            v___x_3640_ = v_snd_3636_;
                            v_isShared_3641_ = v_isSharedCheck_3650_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_3638_);
                            crate::leanh::lean_dec(v_snd_3636_);
                            v___x_3640_ = crate::leanh::lean_box(0);
                            v_isShared_3641_ = v_isSharedCheck_3650_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3624_);
                        crate::leanh::lean_dec(v_fst_3613_);
                        crate::leanh::lean_dec_ref(v_snd_3610_);
                        v_a_3652_ = crate::leanh::lean_ctor_get(v___x_3634_, 0);
                        v_isSharedCheck_3659_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3634_)) as u8;
                        if v_isSharedCheck_3659_ == 0 {
                            v___x_3654_ = v___x_3634_;
                            v_isShared_3655_ = v_isSharedCheck_3659_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3652_);
                            crate::leanh::lean_dec(v___x_3634_);
                            v___x_3654_ = crate::leanh::lean_box(0);
                            v_isShared_3655_ = v_isSharedCheck_3659_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_fst_3613_);
                    crate::leanh::lean_dec_ref(v___x_3612_);
                    crate::leanh::lean_dec(v_hyp_3611_);
                    crate::leanh::lean_dec_ref(v_snd_3610_);
                    v_a_3660_ = crate::leanh::lean_ctor_get(v___x_3623_, 0);
                    v_isSharedCheck_3667_ = (!crate::leanh::lean_is_exclusive(v___x_3623_)) as u8;
                    if v_isSharedCheck_3667_ == 0 {
                        v___x_3662_ = v___x_3623_;
                        v_isShared_3663_ = v_isSharedCheck_3667_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3660_);
                        crate::leanh::lean_dec(v___x_3623_);
                        v___x_3662_ = crate::leanh::lean_box(0);
                        v_isShared_3663_ = v_isSharedCheck_3667_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3642_ = l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_rewriteHyps(
                    v_a_3624_,
                    v_snd_3610_,
                    v_snd_3638_,
                );
                v___x_3643_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2___redArg(v_fst_3613_, v___x_3642_, v___y_3619_);
                crate::leanh::lean_dec_ref(v___x_3643_);
                v___x_3644_ = l_Lean_Expr_mvarId_x21(v_fst_3637_);
                crate::leanh::lean_dec(v_fst_3637_);
                v___x_3645_ = crate::leanh::lean_box(0);
                if v_isShared_3641_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3640_, 1);
                    crate::leanh::lean_ctor_set(v___x_3640_, 1, v___x_3645_);
                    crate::leanh::lean_ctor_set(v___x_3640_, 0, v___x_3644_);
                    v___x_3647_ = v___x_3640_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3649_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3649_, 0, v___x_3644_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3649_, 1, v___x_3645_);
                    v___x_3647_ = v_reuseFailAlloc_3649_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3648_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                    v___x_3647_,
                    v___y_3615_,
                    v___y_3618_,
                    v___y_3619_,
                    v___y_3620_,
                    v___y_3621_,
                );
                return v___x_3648_;
            }
            3 => {
                if v_isShared_3655_ == 0 {
                    v___x_3657_ = v___x_3654_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3658_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3658_, 0, v_a_3652_);
                    v___x_3657_ = v_reuseFailAlloc_3658_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3657_;
            }
            5 => {
                if v_isShared_3663_ == 0 {
                    v___x_3665_ = v___x_3662_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3666_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3666_, 0, v_a_3660_);
                    v___x_3665_ = v_reuseFailAlloc_3666_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3665_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___lam__1___boxed(
    mut v_snd_3668_: *mut crate::leanh::LeanObject,
    mut v_hyp_3669_: *mut crate::leanh::LeanObject,
    mut v___x_3670_: *mut crate::leanh::LeanObject,
    mut v_fst_3671_: *mut crate::leanh::LeanObject,
    mut v___y_3672_: *mut crate::leanh::LeanObject,
    mut v___y_3673_: *mut crate::leanh::LeanObject,
    mut v___y_3674_: *mut crate::leanh::LeanObject,
    mut v___y_3675_: *mut crate::leanh::LeanObject,
    mut v___y_3676_: *mut crate::leanh::LeanObject,
    mut v___y_3677_: *mut crate::leanh::LeanObject,
    mut v___y_3678_: *mut crate::leanh::LeanObject,
    mut v___y_3679_: *mut crate::leanh::LeanObject,
    mut v___y_3680_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3681_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___lam__1(
        v_snd_3668_,
        v_hyp_3669_,
        v___x_3670_,
        v_fst_3671_,
        v___y_3672_,
        v___y_3673_,
        v___y_3674_,
        v___y_3675_,
        v___y_3676_,
        v___y_3677_,
        v___y_3678_,
        v___y_3679_,
    );
    crate::leanh::lean_dec(v___y_3679_);
    crate::leanh::lean_dec_ref(v___y_3678_);
    crate::leanh::lean_dec(v___y_3677_);
    crate::leanh::lean_dec_ref(v___y_3676_);
    crate::leanh::lean_dec(v___y_3675_);
    crate::leanh::lean_dec_ref(v___y_3674_);
    crate::leanh::lean_dec(v___y_3673_);
    crate::leanh::lean_dec_ref(v___y_3672_);
    return v_res_3681_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMPure(
    mut v_x_3690_: *mut crate::leanh::LeanObject,
    mut v_a_3691_: *mut crate::leanh::LeanObject,
    mut v_a_3692_: *mut crate::leanh::LeanObject,
    mut v_a_3693_: *mut crate::leanh::LeanObject,
    mut v_a_3694_: *mut crate::leanh::LeanObject,
    mut v_a_3695_: *mut crate::leanh::LeanObject,
    mut v_a_3696_: *mut crate::leanh::LeanObject,
    mut v_a_3697_: *mut crate::leanh::LeanObject,
    mut v_a_3698_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3702_: u8 = 0;
    let mut v___x_3703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hyp_3709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3715_: u8 = 0;
    let mut v___x_3717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3719_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3700_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___closed__0;
                v___x_3701_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___closed__3;
                crate::leanh::lean_inc(v_x_3690_);
                v___x_3702_ = l_Lean_Syntax_isOfKind(v_x_3690_, v___x_3701_);
                if v___x_3702_ == 0 {
                    crate::leanh::lean_dec(v_x_3690_);
                    v___x_3703_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__0___redArg();
                    return v___x_3703_;
                } else {
                    v___x_3704_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(
                        v_a_3692_, v_a_3695_, v_a_3696_, v_a_3697_, v_a_3698_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3704_) == 0 {
                        v_a_3705_ = crate::leanh::lean_ctor_get(v___x_3704_, 0);
                        crate::leanh::lean_inc(v_a_3705_);
                        crate::leanh::lean_dec_ref_known(v___x_3704_, 1);
                        v_fst_3706_ = crate::leanh::lean_ctor_get(v_a_3705_, 0);
                        crate::leanh::lean_inc_n(v_fst_3706_, 2);
                        v_snd_3707_ = crate::leanh::lean_ctor_get(v_a_3705_, 1);
                        crate::leanh::lean_inc(v_snd_3707_);
                        crate::leanh::lean_dec(v_a_3705_);
                        v___x_3708_ = crate::leanh::lean_unsigned_to_nat(1);
                        v_hyp_3709_ = l_Lean_Syntax_getArg(v_x_3690_, v___x_3708_);
                        crate::leanh::lean_dec(v_x_3690_);
                        v___f_3710_ = crate::leanh::lean_alloc_closure(
                            l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___lam__1___boxed
                                as *mut core::ffi::c_void,
                            13,
                            4,
                        );
                        crate::leanh::lean_closure_set(v___f_3710_, 0, v_snd_3707_);
                        crate::leanh::lean_closure_set(v___f_3710_, 1, v_hyp_3709_);
                        crate::leanh::lean_closure_set(v___f_3710_, 2, v___x_3700_);
                        crate::leanh::lean_closure_set(v___f_3710_, 3, v_fst_3706_);
                        v___x_3711_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__3___redArg(v_fst_3706_, v___f_3710_, v_a_3691_, v_a_3692_, v_a_3693_, v_a_3694_, v_a_3695_, v_a_3696_, v_a_3697_, v_a_3698_);
                        return v___x_3711_;
                    } else {
                        crate::leanh::lean_dec(v_x_3690_);
                        v_a_3712_ = crate::leanh::lean_ctor_get(v___x_3704_, 0);
                        v_isSharedCheck_3719_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3704_)) as u8;
                        if v_isSharedCheck_3719_ == 0 {
                            v___x_3714_ = v___x_3704_;
                            v_isShared_3715_ = v_isSharedCheck_3719_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3712_);
                            crate::leanh::lean_dec(v___x_3704_);
                            v___x_3714_ = crate::leanh::lean_box(0);
                            v_isShared_3715_ = v_isSharedCheck_3719_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3715_ == 0 {
                    v___x_3717_ = v___x_3714_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3718_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3718_, 0, v_a_3712_);
                    v___x_3717_ = v_reuseFailAlloc_3718_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3717_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___boxed(
    mut v_x_3720_: *mut crate::leanh::LeanObject,
    mut v_a_3721_: *mut crate::leanh::LeanObject,
    mut v_a_3722_: *mut crate::leanh::LeanObject,
    mut v_a_3723_: *mut crate::leanh::LeanObject,
    mut v_a_3724_: *mut crate::leanh::LeanObject,
    mut v_a_3725_: *mut crate::leanh::LeanObject,
    mut v_a_3726_: *mut crate::leanh::LeanObject,
    mut v_a_3727_: *mut crate::leanh::LeanObject,
    mut v_a_3728_: *mut crate::leanh::LeanObject,
    mut v_a_3729_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3730_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMPure(
        v_x_3720_, v_a_3721_, v_a_3722_, v_a_3723_, v_a_3724_, v_a_3725_, v_a_3726_, v_a_3727_,
        v_a_3728_,
    );
    crate::leanh::lean_dec(v_a_3728_);
    crate::leanh::lean_dec_ref(v_a_3727_);
    crate::leanh::lean_dec(v_a_3726_);
    crate::leanh::lean_dec_ref(v_a_3725_);
    crate::leanh::lean_dec(v_a_3724_);
    crate::leanh::lean_dec_ref(v_a_3723_);
    crate::leanh::lean_dec(v_a_3722_);
    crate::leanh::lean_dec_ref(v_a_3721_);
    return v_res_3730_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1(
    mut v_00_u03b1_3731_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3s_3732_: *mut crate::leanh::LeanObject,
    mut v_hyp_3733_: *mut crate::leanh::LeanObject,
    mut v_name_3734_: *mut crate::leanh::LeanObject,
    mut v_k_3735_: *mut crate::leanh::LeanObject,
    mut v___y_3736_: *mut crate::leanh::LeanObject,
    mut v___y_3737_: *mut crate::leanh::LeanObject,
    mut v___y_3738_: *mut crate::leanh::LeanObject,
    mut v___y_3739_: *mut crate::leanh::LeanObject,
    mut v___y_3740_: *mut crate::leanh::LeanObject,
    mut v___y_3741_: *mut crate::leanh::LeanObject,
    mut v___y_3742_: *mut crate::leanh::LeanObject,
    mut v___y_3743_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3745_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1___redArg(v_00_u03c3s_3732_, v_hyp_3733_, v_name_3734_, v_k_3735_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_, v___y_3740_, v___y_3741_, v___y_3742_, v___y_3743_);
    return v___x_3745_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1___boxed(
    mut v_00_u03b1_3746_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3s_3747_: *mut crate::leanh::LeanObject,
    mut v_hyp_3748_: *mut crate::leanh::LeanObject,
    mut v_name_3749_: *mut crate::leanh::LeanObject,
    mut v_k_3750_: *mut crate::leanh::LeanObject,
    mut v___y_3751_: *mut crate::leanh::LeanObject,
    mut v___y_3752_: *mut crate::leanh::LeanObject,
    mut v___y_3753_: *mut crate::leanh::LeanObject,
    mut v___y_3754_: *mut crate::leanh::LeanObject,
    mut v___y_3755_: *mut crate::leanh::LeanObject,
    mut v___y_3756_: *mut crate::leanh::LeanObject,
    mut v___y_3757_: *mut crate::leanh::LeanObject,
    mut v___y_3758_: *mut crate::leanh::LeanObject,
    mut v___y_3759_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3760_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1(v_00_u03b1_3746_, v_00_u03c3s_3747_, v_hyp_3748_, v_name_3749_, v_k_3750_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_);
    crate::leanh::lean_dec(v___y_3758_);
    crate::leanh::lean_dec_ref(v___y_3757_);
    crate::leanh::lean_dec(v___y_3756_);
    crate::leanh::lean_dec_ref(v___y_3755_);
    crate::leanh::lean_dec(v___y_3754_);
    crate::leanh::lean_dec_ref(v___y_3753_);
    crate::leanh::lean_dec(v___y_3752_);
    crate::leanh::lean_dec_ref(v___y_3751_);
    return v_res_3760_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2(
    mut v_mvarId_3761_: *mut crate::leanh::LeanObject,
    mut v_val_3762_: *mut crate::leanh::LeanObject,
    mut v___y_3763_: *mut crate::leanh::LeanObject,
    mut v___y_3764_: *mut crate::leanh::LeanObject,
    mut v___y_3765_: *mut crate::leanh::LeanObject,
    mut v___y_3766_: *mut crate::leanh::LeanObject,
    mut v___y_3767_: *mut crate::leanh::LeanObject,
    mut v___y_3768_: *mut crate::leanh::LeanObject,
    mut v___y_3769_: *mut crate::leanh::LeanObject,
    mut v___y_3770_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3772_ =
        l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2___redArg(
            v_mvarId_3761_,
            v_val_3762_,
            v___y_3768_,
        );
    return v___x_3772_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2___boxed(
    mut v_mvarId_3773_: *mut crate::leanh::LeanObject,
    mut v_val_3774_: *mut crate::leanh::LeanObject,
    mut v___y_3775_: *mut crate::leanh::LeanObject,
    mut v___y_3776_: *mut crate::leanh::LeanObject,
    mut v___y_3777_: *mut crate::leanh::LeanObject,
    mut v___y_3778_: *mut crate::leanh::LeanObject,
    mut v___y_3779_: *mut crate::leanh::LeanObject,
    mut v___y_3780_: *mut crate::leanh::LeanObject,
    mut v___y_3781_: *mut crate::leanh::LeanObject,
    mut v___y_3782_: *mut crate::leanh::LeanObject,
    mut v___y_3783_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3784_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2(
        v_mvarId_3773_,
        v_val_3774_,
        v___y_3775_,
        v___y_3776_,
        v___y_3777_,
        v___y_3778_,
        v___y_3779_,
        v___y_3780_,
        v___y_3781_,
        v___y_3782_,
    );
    crate::leanh::lean_dec(v___y_3782_);
    crate::leanh::lean_dec_ref(v___y_3781_);
    crate::leanh::lean_dec(v___y_3780_);
    crate::leanh::lean_dec_ref(v___y_3779_);
    crate::leanh::lean_dec(v___y_3778_);
    crate::leanh::lean_dec_ref(v___y_3777_);
    crate::leanh::lean_dec(v___y_3776_);
    crate::leanh::lean_dec_ref(v___y_3775_);
    return v_res_3784_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1_spec__3(
    mut v_00_u03b1_3785_: *mut crate::leanh::LeanObject,
    mut v_name_3786_: *mut crate::leanh::LeanObject,
    mut v_bi_3787_: u8,
    mut v_type_3788_: *mut crate::leanh::LeanObject,
    mut v_k_3789_: *mut crate::leanh::LeanObject,
    mut v_kind_3790_: u8,
    mut v___y_3791_: *mut crate::leanh::LeanObject,
    mut v___y_3792_: *mut crate::leanh::LeanObject,
    mut v___y_3793_: *mut crate::leanh::LeanObject,
    mut v___y_3794_: *mut crate::leanh::LeanObject,
    mut v___y_3795_: *mut crate::leanh::LeanObject,
    mut v___y_3796_: *mut crate::leanh::LeanObject,
    mut v___y_3797_: *mut crate::leanh::LeanObject,
    mut v___y_3798_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3800_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1_spec__3___redArg(v_name_3786_, v_bi_3787_, v_type_3788_, v_k_3789_, v_kind_3790_, v___y_3791_, v___y_3792_, v___y_3793_, v___y_3794_, v___y_3795_, v___y_3796_, v___y_3797_, v___y_3798_);
    return v___x_3800_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1_spec__3___boxed(
    mut v_00_u03b1_3801_: *mut crate::leanh::LeanObject,
    mut v_name_3802_: *mut crate::leanh::LeanObject,
    mut v_bi_3803_: *mut crate::leanh::LeanObject,
    mut v_type_3804_: *mut crate::leanh::LeanObject,
    mut v_k_3805_: *mut crate::leanh::LeanObject,
    mut v_kind_3806_: *mut crate::leanh::LeanObject,
    mut v___y_3807_: *mut crate::leanh::LeanObject,
    mut v___y_3808_: *mut crate::leanh::LeanObject,
    mut v___y_3809_: *mut crate::leanh::LeanObject,
    mut v___y_3810_: *mut crate::leanh::LeanObject,
    mut v___y_3811_: *mut crate::leanh::LeanObject,
    mut v___y_3812_: *mut crate::leanh::LeanObject,
    mut v___y_3813_: *mut crate::leanh::LeanObject,
    mut v___y_3814_: *mut crate::leanh::LeanObject,
    mut v___y_3815_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_bi_boxed_3816_: u8 = 0;
    let mut v_kind_boxed_3817_: u8 = 0;
    let mut v_res_3818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_3816_ = (crate::leanh::lean_unbox(v_bi_3803_) as u8);
    v_kind_boxed_3817_ = (crate::leanh::lean_unbox(v_kind_3806_) as u8);
    v_res_3818_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1_spec__3(v_00_u03b1_3801_, v_name_3802_, v_bi_boxed_3816_, v_type_3804_, v_k_3805_, v_kind_boxed_3817_, v___y_3807_, v___y_3808_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_, v___y_3813_, v___y_3814_);
    crate::leanh::lean_dec(v___y_3814_);
    crate::leanh::lean_dec_ref(v___y_3813_);
    crate::leanh::lean_dec(v___y_3812_);
    crate::leanh::lean_dec_ref(v___y_3811_);
    crate::leanh::lean_dec(v___y_3810_);
    crate::leanh::lean_dec_ref(v___y_3809_);
    crate::leanh::lean_dec(v___y_3808_);
    crate::leanh::lean_dec_ref(v___y_3807_);
    return v_res_3818_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1(
    mut v_00_u03b1_3819_: *mut crate::leanh::LeanObject,
    mut v_name_3820_: *mut crate::leanh::LeanObject,
    mut v_type_3821_: *mut crate::leanh::LeanObject,
    mut v_k_3822_: *mut crate::leanh::LeanObject,
    mut v___y_3823_: *mut crate::leanh::LeanObject,
    mut v___y_3824_: *mut crate::leanh::LeanObject,
    mut v___y_3825_: *mut crate::leanh::LeanObject,
    mut v___y_3826_: *mut crate::leanh::LeanObject,
    mut v___y_3827_: *mut crate::leanh::LeanObject,
    mut v___y_3828_: *mut crate::leanh::LeanObject,
    mut v___y_3829_: *mut crate::leanh::LeanObject,
    mut v___y_3830_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3832_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1___redArg(v_name_3820_, v_type_3821_, v_k_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_, v___y_3829_, v___y_3830_);
    return v___x_3832_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1___boxed(
    mut v_00_u03b1_3833_: *mut crate::leanh::LeanObject,
    mut v_name_3834_: *mut crate::leanh::LeanObject,
    mut v_type_3835_: *mut crate::leanh::LeanObject,
    mut v_k_3836_: *mut crate::leanh::LeanObject,
    mut v___y_3837_: *mut crate::leanh::LeanObject,
    mut v___y_3838_: *mut crate::leanh::LeanObject,
    mut v___y_3839_: *mut crate::leanh::LeanObject,
    mut v___y_3840_: *mut crate::leanh::LeanObject,
    mut v___y_3841_: *mut crate::leanh::LeanObject,
    mut v___y_3842_: *mut crate::leanh::LeanObject,
    mut v___y_3843_: *mut crate::leanh::LeanObject,
    mut v___y_3844_: *mut crate::leanh::LeanObject,
    mut v___y_3845_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3846_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__1_spec__1(v_00_u03b1_3833_, v_name_3834_, v_type_3835_, v_k_3836_, v___y_3837_, v___y_3838_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_, v___y_3844_);
    crate::leanh::lean_dec(v___y_3844_);
    crate::leanh::lean_dec_ref(v___y_3843_);
    crate::leanh::lean_dec(v___y_3842_);
    crate::leanh::lean_dec_ref(v___y_3841_);
    crate::leanh::lean_dec(v___y_3840_);
    crate::leanh::lean_dec_ref(v___y_3839_);
    crate::leanh::lean_dec(v___y_3838_);
    crate::leanh::lean_dec_ref(v___y_3837_);
    return v_res_3846_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3(
    mut v_00_u03b2_3847_: *mut crate::leanh::LeanObject,
    mut v_x_3848_: *mut crate::leanh::LeanObject,
    mut v_x_3849_: *mut crate::leanh::LeanObject,
    mut v_x_3850_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3851_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3___redArg(v_x_3848_, v_x_3849_, v_x_3850_);
    return v___x_3851_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6(
    mut v_00_u03b2_3852_: *mut crate::leanh::LeanObject,
    mut v_x_3853_: *mut crate::leanh::LeanObject,
    mut v_x_3854_: usize,
    mut v_x_3855_: usize,
    mut v_x_3856_: *mut crate::leanh::LeanObject,
    mut v_x_3857_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3858_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6___redArg(v_x_3853_, v_x_3854_, v_x_3855_, v_x_3856_, v_x_3857_);
    return v___x_3858_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6___boxed(
    mut v_00_u03b2_3859_: *mut crate::leanh::LeanObject,
    mut v_x_3860_: *mut crate::leanh::LeanObject,
    mut v_x_3861_: *mut crate::leanh::LeanObject,
    mut v_x_3862_: *mut crate::leanh::LeanObject,
    mut v_x_3863_: *mut crate::leanh::LeanObject,
    mut v_x_3864_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_10929__boxed_3865_: usize = 0;
    let mut v_x_10930__boxed_3866_: usize = 0;
    let mut v_res_3867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_10929__boxed_3865_ = crate::leanh::lean_unbox_usize(v_x_3861_);
    crate::leanh::lean_dec(v_x_3861_);
    v_x_10930__boxed_3866_ = crate::leanh::lean_unbox_usize(v_x_3862_);
    crate::leanh::lean_dec(v_x_3862_);
    v_res_3867_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6(v_00_u03b2_3859_, v_x_3860_, v_x_10929__boxed_3865_, v_x_10930__boxed_3866_, v_x_3863_, v_x_3864_);
    return v_res_3867_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6_spec__7(
    mut v_00_u03b2_3868_: *mut crate::leanh::LeanObject,
    mut v_n_3869_: *mut crate::leanh::LeanObject,
    mut v_k_3870_: *mut crate::leanh::LeanObject,
    mut v_v_3871_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3872_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6_spec__7___redArg(v_n_3869_, v_k_3870_, v_v_3871_);
    return v___x_3872_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6_spec__8(
    mut v_00_u03b2_3873_: *mut crate::leanh::LeanObject,
    mut v_depth_3874_: usize,
    mut v_keys_3875_: *mut crate::leanh::LeanObject,
    mut v_vals_3876_: *mut crate::leanh::LeanObject,
    mut v_heq_3877_: *mut crate::leanh::LeanObject,
    mut v_i_3878_: *mut crate::leanh::LeanObject,
    mut v_entries_3879_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3880_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6_spec__8___redArg(v_depth_3874_, v_keys_3875_, v_vals_3876_, v_i_3878_, v_entries_3879_);
    return v___x_3880_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6_spec__8___boxed(
    mut v_00_u03b2_3881_: *mut crate::leanh::LeanObject,
    mut v_depth_3882_: *mut crate::leanh::LeanObject,
    mut v_keys_3883_: *mut crate::leanh::LeanObject,
    mut v_vals_3884_: *mut crate::leanh::LeanObject,
    mut v_heq_3885_: *mut crate::leanh::LeanObject,
    mut v_i_3886_: *mut crate::leanh::LeanObject,
    mut v_entries_3887_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_3888_: usize = 0;
    let mut v_res_3889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_3888_ = crate::leanh::lean_unbox_usize(v_depth_3882_);
    crate::leanh::lean_dec(v_depth_3882_);
    v_res_3889_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6_spec__8(v_00_u03b2_3881_, v_depth_boxed_3888_, v_keys_3883_, v_vals_3884_, v_heq_3885_, v_i_3886_, v_entries_3887_);
    crate::leanh::lean_dec_ref(v_vals_3884_);
    crate::leanh::lean_dec_ref(v_keys_3883_);
    return v_res_3889_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6_spec__7_spec__8(
    mut v_00_u03b2_3890_: *mut crate::leanh::LeanObject,
    mut v_x_3891_: *mut crate::leanh::LeanObject,
    mut v_x_3892_: *mut crate::leanh::LeanObject,
    mut v_x_3893_: *mut crate::leanh::LeanObject,
    mut v_x_3894_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3895_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3_spec__6_spec__7_spec__8___redArg(v_x_3891_, v_x_3892_, v_x_3893_, v_x_3894_);
    return v___x_3895_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPure__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3907_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_3908_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___closed__3;
    v___x_3909_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPure__1___closed__3;
    v___x_3910_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_ProofMode_elabMPure___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_3911_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_3907_,
        v___x_3908_,
        v___x_3909_,
        v___x_3910_,
    );
    return v___x_3911_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPure__1___boxed(
    mut v_a_3912_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3913_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPure__1();
    return v_res_3913_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___redArg___lam__0(
    mut v___x_3915_: *mut crate::leanh::LeanObject,
    mut v___x_3916_: *mut crate::leanh::LeanObject,
    mut v___x_3917_: *mut crate::leanh::LeanObject,
    mut v___x_3918_: *mut crate::leanh::LeanObject,
    mut v___x_3919_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3s_3920_: *mut crate::leanh::LeanObject,
    mut v_hyps_3921_: *mut crate::leanh::LeanObject,
    mut v_target_3922_: *mut crate::leanh::LeanObject,
    mut v_00_u03c6_3923_: *mut crate::leanh::LeanObject,
    mut v_inst_3924_: *mut crate::leanh::LeanObject,
    mut v_toPure_3925_: *mut crate::leanh::LeanObject,
    mut v_____x_3926_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_3927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3931_: u8 = 0;
    let mut v___x_3932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_prf_3936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3941_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_3927_ = crate::leanh::lean_ctor_get(v_____x_3926_, 0);
                v_snd_3928_ = crate::leanh::lean_ctor_get(v_____x_3926_, 1);
                v_isSharedCheck_3941_ = (!crate::leanh::lean_is_exclusive(v_____x_3926_)) as u8;
                if v_isSharedCheck_3941_ == 0 {
                    v___x_3930_ = v_____x_3926_;
                    v_isShared_3931_ = v_isSharedCheck_3941_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3928_);
                    crate::leanh::lean_inc(v_fst_3927_);
                    crate::leanh::lean_dec(v_____x_3926_);
                    v___x_3930_ = crate::leanh::lean_box(0);
                    v_isShared_3931_ = v_isSharedCheck_3941_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3932_ =
                    l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__2___closed__0;
                v___x_3933_ =
                    l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___redArg___lam__0___closed__0;
                v___x_3934_ = l_Lean_Name_mkStr6(
                    v___x_3915_,
                    v___x_3916_,
                    v___x_3917_,
                    v___x_3918_,
                    v___x_3932_,
                    v___x_3933_,
                );
                v___x_3935_ = l_Lean_mkConst(v___x_3934_, v___x_3919_);
                v_prf_3936_ = l_Lean_mkApp6(
                    v___x_3935_,
                    v_00_u03c3s_3920_,
                    v_hyps_3921_,
                    v_target_3922_,
                    v_00_u03c6_3923_,
                    v_inst_3924_,
                    v_snd_3928_,
                );
                if v_isShared_3931_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3930_, 1, v_prf_3936_);
                    v___x_3938_ = v___x_3930_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3940_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3940_, 0, v_fst_3927_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3940_, 1, v_prf_3936_);
                    v___x_3938_ = v_reuseFailAlloc_3940_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3939_ = crate::leanh::lean_apply_2(
                    v_toPure_3925_,
                    crate::leanh::lean_box(0),
                    v___x_3938_,
                );
                return v___x_3939_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___redArg___lam__1(
    mut v___x_3942_: *mut crate::leanh::LeanObject,
    mut v___x_3943_: *mut crate::leanh::LeanObject,
    mut v___x_3944_: *mut crate::leanh::LeanObject,
    mut v___x_3945_: *mut crate::leanh::LeanObject,
    mut v___x_3946_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3s_3947_: *mut crate::leanh::LeanObject,
    mut v_hyps_3948_: *mut crate::leanh::LeanObject,
    mut v_target_3949_: *mut crate::leanh::LeanObject,
    mut v_00_u03c6_3950_: *mut crate::leanh::LeanObject,
    mut v_toPure_3951_: *mut crate::leanh::LeanObject,
    mut v_k_3952_: *mut crate::leanh::LeanObject,
    mut v_toBind_3953_: *mut crate::leanh::LeanObject,
    mut v_inst_3954_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_00_u03c6_3950_);
    v___f_3955_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___redArg___lam__0 as *mut core::ffi::c_void,
        12,
        11,
    );
    crate::leanh::lean_closure_set(v___f_3955_, 0, v___x_3942_);
    crate::leanh::lean_closure_set(v___f_3955_, 1, v___x_3943_);
    crate::leanh::lean_closure_set(v___f_3955_, 2, v___x_3944_);
    crate::leanh::lean_closure_set(v___f_3955_, 3, v___x_3945_);
    crate::leanh::lean_closure_set(v___f_3955_, 4, v___x_3946_);
    crate::leanh::lean_closure_set(v___f_3955_, 5, v_00_u03c3s_3947_);
    crate::leanh::lean_closure_set(v___f_3955_, 6, v_hyps_3948_);
    crate::leanh::lean_closure_set(v___f_3955_, 7, v_target_3949_);
    crate::leanh::lean_closure_set(v___f_3955_, 8, v_00_u03c6_3950_);
    crate::leanh::lean_closure_set(v___f_3955_, 9, v_inst_3954_);
    crate::leanh::lean_closure_set(v___f_3955_, 10, v_toPure_3951_);
    v___x_3956_ = crate::leanh::lean_apply_1(v_k_3952_, v_00_u03c6_3950_);
    v___x_3957_ = crate::leanh::lean_apply_4(
        v_toBind_3953_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3956_,
        v___f_3955_,
    );
    return v___x_3957_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___redArg___lam__2(
    mut v_goal_3958_: *mut crate::leanh::LeanObject,
    mut v_toPure_3959_: *mut crate::leanh::LeanObject,
    mut v_k_3960_: *mut crate::leanh::LeanObject,
    mut v_toBind_3961_: *mut crate::leanh::LeanObject,
    mut v_inst_3962_: *mut crate::leanh::LeanObject,
    mut v_00_u03c6_3963_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_u_3964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_00_u03c3s_3965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hyps_3966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_3967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_u_3964_ = crate::leanh::lean_ctor_get(v_goal_3958_, 0);
    crate::leanh::lean_inc(v_u_3964_);
    v_00_u03c3s_3965_ = crate::leanh::lean_ctor_get(v_goal_3958_, 1);
    crate::leanh::lean_inc_ref_n(v_00_u03c3s_3965_, 2);
    v_hyps_3966_ = crate::leanh::lean_ctor_get(v_goal_3958_, 2);
    crate::leanh::lean_inc_ref(v_hyps_3966_);
    v_target_3967_ = crate::leanh::lean_ctor_get(v_goal_3958_, 3);
    crate::leanh::lean_inc_ref_n(v_target_3967_, 2);
    crate::leanh::lean_dec_ref(v_goal_3958_);
    v___x_3968_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__0;
    v___x_3969_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__1;
    v___x_3970_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__2;
    v___x_3971_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__3;
    v___x_3972_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__5;
    v___x_3973_ = crate::leanh::lean_box(0);
    v___x_3974_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3974_, 0, v_u_3964_);
    crate::leanh::lean_ctor_set(v___x_3974_, 1, v___x_3973_);
    crate::leanh::lean_inc(v_toBind_3961_);
    crate::leanh::lean_inc_ref(v_00_u03c6_3963_);
    crate::leanh::lean_inc_ref(v___x_3974_);
    v___f_3975_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___redArg___lam__1 as *mut core::ffi::c_void,
        13,
        12,
    );
    crate::leanh::lean_closure_set(v___f_3975_, 0, v___x_3968_);
    crate::leanh::lean_closure_set(v___f_3975_, 1, v___x_3969_);
    crate::leanh::lean_closure_set(v___f_3975_, 2, v___x_3970_);
    crate::leanh::lean_closure_set(v___f_3975_, 3, v___x_3971_);
    crate::leanh::lean_closure_set(v___f_3975_, 4, v___x_3974_);
    crate::leanh::lean_closure_set(v___f_3975_, 5, v_00_u03c3s_3965_);
    crate::leanh::lean_closure_set(v___f_3975_, 6, v_hyps_3966_);
    crate::leanh::lean_closure_set(v___f_3975_, 7, v_target_3967_);
    crate::leanh::lean_closure_set(v___f_3975_, 8, v_00_u03c6_3963_);
    crate::leanh::lean_closure_set(v___f_3975_, 9, v_toPure_3959_);
    crate::leanh::lean_closure_set(v___f_3975_, 10, v_k_3960_);
    crate::leanh::lean_closure_set(v___f_3975_, 11, v_toBind_3961_);
    v___x_3976_ = l_Lean_mkConst(v___x_3972_, v___x_3974_);
    v___x_3977_ = l_Lean_mkApp3(
        v___x_3976_,
        v_00_u03c3s_3965_,
        v_target_3967_,
        v_00_u03c6_3963_,
    );
    v___x_3978_ = crate::leanh::lean_box(0);
    v___x_3979_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_synthInstance___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_3979_, 0, v___x_3977_);
    crate::leanh::lean_closure_set(v___x_3979_, 1, v___x_3978_);
    v___x_3980_ = crate::leanh::lean_apply_2(v_inst_3962_, crate::leanh::lean_box(0), v___x_3979_);
    v___x_3981_ = crate::leanh::lean_apply_4(
        v_toBind_3961_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3980_,
        v___f_3975_,
    );
    return v___x_3981_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___redArg(
    mut v_inst_3982_: *mut crate::leanh::LeanObject,
    mut v_inst_3983_: *mut crate::leanh::LeanObject,
    mut v_goal_3984_: *mut crate::leanh::LeanObject,
    mut v_k_3985_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3986_ = crate::leanh::lean_ctor_get(v_inst_3982_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_3986_);
    v_toBind_3987_ = crate::leanh::lean_ctor_get(v_inst_3982_, 1);
    crate::leanh::lean_inc_n(v_toBind_3987_, 2);
    crate::leanh::lean_dec_ref(v_inst_3982_);
    v_toPure_3988_ = crate::leanh::lean_ctor_get(v_toApplicative_3986_, 1);
    crate::leanh::lean_inc(v_toPure_3988_);
    crate::leanh::lean_dec_ref(v_toApplicative_3986_);
    v___x_3989_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__2_once
        ),
        _init_l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__2,
    );
    crate::leanh::lean_inc(v_inst_3983_);
    v___x_3990_ = crate::leanh::lean_apply_2(v_inst_3983_, crate::leanh::lean_box(0), v___x_3989_);
    v___f_3991_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___redArg___lam__2 as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___f_3991_, 0, v_goal_3984_);
    crate::leanh::lean_closure_set(v___f_3991_, 1, v_toPure_3988_);
    crate::leanh::lean_closure_set(v___f_3991_, 2, v_k_3985_);
    crate::leanh::lean_closure_set(v___f_3991_, 3, v_toBind_3987_);
    crate::leanh::lean_closure_set(v___f_3991_, 4, v_inst_3983_);
    v___x_3992_ = crate::leanh::lean_apply_4(
        v_toBind_3987_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3990_,
        v___f_3991_,
    );
    return v___x_3992_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore(
    mut v_m_3993_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_3994_: *mut crate::leanh::LeanObject,
    mut v_inst_3995_: *mut crate::leanh::LeanObject,
    mut v_inst_3996_: *mut crate::leanh::LeanObject,
    mut v_goal_3997_: *mut crate::leanh::LeanObject,
    mut v_k_3998_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3999_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___redArg(
        v_inst_3995_,
        v_inst_3996_,
        v_goal_3997_,
        v_k_3998_,
    );
    return v___x_3999_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro_spec__0___redArg(
    mut v_goal_4007_: *mut crate::leanh::LeanObject,
    mut v_k_4008_: *mut crate::leanh::LeanObject,
    mut v___y_4009_: *mut crate::leanh::LeanObject,
    mut v___y_4010_: *mut crate::leanh::LeanObject,
    mut v___y_4011_: *mut crate::leanh::LeanObject,
    mut v___y_4012_: *mut crate::leanh::LeanObject,
    mut v___y_4013_: *mut crate::leanh::LeanObject,
    mut v___y_4014_: *mut crate::leanh::LeanObject,
    mut v___y_4015_: *mut crate::leanh::LeanObject,
    mut v___y_4016_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4019_: u8 = 0;
    let mut v___x_4020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_4023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_00_u03c3s_4024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hyps_4025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_4026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4039_: u8 = 0;
    let mut v_fst_4040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4044_: u8 = 0;
    let mut v___x_4045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_prf_4047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4054_: u8 = 0;
    let mut v_isSharedCheck_4055_: u8 = 0;
    let mut v_a_4056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4059_: u8 = 0;
    let mut v___x_4061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4063_: u8 = 0;
    let mut v_a_4064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4067_: u8 = 0;
    let mut v___x_4069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4071_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4018_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__1_once), _init_l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__1);
                v___x_4019_ = 0;
                v___x_4020_ = crate::leanh::lean_box(0);
                v___x_4021_ = l_Lean_Meta_mkFreshExprMVar(
                    v___x_4018_,
                    v___x_4019_,
                    v___x_4020_,
                    v___y_4013_,
                    v___y_4014_,
                    v___y_4015_,
                    v___y_4016_,
                );
                if crate::leanh::lean_obj_tag(v___x_4021_) == 0 {
                    v_a_4022_ = crate::leanh::lean_ctor_get(v___x_4021_, 0);
                    crate::leanh::lean_inc_n(v_a_4022_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_4021_, 1);
                    v_u_4023_ = crate::leanh::lean_ctor_get(v_goal_4007_, 0);
                    crate::leanh::lean_inc(v_u_4023_);
                    v_00_u03c3s_4024_ = crate::leanh::lean_ctor_get(v_goal_4007_, 1);
                    crate::leanh::lean_inc_ref_n(v_00_u03c3s_4024_, 2);
                    v_hyps_4025_ = crate::leanh::lean_ctor_get(v_goal_4007_, 2);
                    crate::leanh::lean_inc_ref(v_hyps_4025_);
                    v_target_4026_ = crate::leanh::lean_ctor_get(v_goal_4007_, 3);
                    crate::leanh::lean_inc_ref_n(v_target_4026_, 2);
                    crate::leanh::lean_dec_ref(v_goal_4007_);
                    v___x_4027_ =
                        l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__5;
                    v___x_4028_ = crate::leanh::lean_box(0);
                    v___x_4029_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4029_, 0, v_u_4023_);
                    crate::leanh::lean_ctor_set(v___x_4029_, 1, v___x_4028_);
                    crate::leanh::lean_inc_ref(v___x_4029_);
                    v___x_4030_ = l_Lean_mkConst(v___x_4027_, v___x_4029_);
                    v___x_4031_ =
                        l_Lean_mkApp3(v___x_4030_, v_00_u03c3s_4024_, v_target_4026_, v_a_4022_);
                    v___x_4032_ = crate::leanh::lean_box(0);
                    v___x_4033_ = l_Lean_Meta_synthInstance(
                        v___x_4031_,
                        v___x_4032_,
                        v___y_4013_,
                        v___y_4014_,
                        v___y_4015_,
                        v___y_4016_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4033_) == 0 {
                        v_a_4034_ = crate::leanh::lean_ctor_get(v___x_4033_, 0);
                        crate::leanh::lean_inc(v_a_4034_);
                        crate::leanh::lean_dec_ref_known(v___x_4033_, 1);
                        crate::leanh::lean_inc(v___y_4016_);
                        crate::leanh::lean_inc_ref(v___y_4015_);
                        crate::leanh::lean_inc(v___y_4014_);
                        crate::leanh::lean_inc_ref(v___y_4013_);
                        crate::leanh::lean_inc(v___y_4012_);
                        crate::leanh::lean_inc_ref(v___y_4011_);
                        crate::leanh::lean_inc(v___y_4010_);
                        crate::leanh::lean_inc_ref(v___y_4009_);
                        crate::leanh::lean_inc(v_a_4022_);
                        v___x_4035_ = crate::leanh::lean_apply_10(
                            v_k_4008_,
                            v_a_4022_,
                            v___y_4009_,
                            v___y_4010_,
                            v___y_4011_,
                            v___y_4012_,
                            v___y_4013_,
                            v___y_4014_,
                            v___y_4015_,
                            v___y_4016_,
                            crate::leanh::lean_box(0),
                        );
                        if crate::leanh::lean_obj_tag(v___x_4035_) == 0 {
                            v_a_4036_ = crate::leanh::lean_ctor_get(v___x_4035_, 0);
                            v_isSharedCheck_4055_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4035_)) as u8;
                            if v_isSharedCheck_4055_ == 0 {
                                v___x_4038_ = v___x_4035_;
                                v_isShared_4039_ = v_isSharedCheck_4055_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4036_);
                                crate::leanh::lean_dec(v___x_4035_);
                                v___x_4038_ = crate::leanh::lean_box(0);
                                v_isShared_4039_ = v_isSharedCheck_4055_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_4034_);
                            crate::leanh::lean_dec_ref_known(v___x_4029_, 2);
                            crate::leanh::lean_dec_ref(v_target_4026_);
                            crate::leanh::lean_dec_ref(v_hyps_4025_);
                            crate::leanh::lean_dec_ref(v_00_u03c3s_4024_);
                            crate::leanh::lean_dec(v_a_4022_);
                            return v___x_4035_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v___x_4029_, 2);
                        crate::leanh::lean_dec_ref(v_target_4026_);
                        crate::leanh::lean_dec_ref(v_hyps_4025_);
                        crate::leanh::lean_dec_ref(v_00_u03c3s_4024_);
                        crate::leanh::lean_dec(v_a_4022_);
                        crate::leanh::lean_dec_ref(v_k_4008_);
                        v_a_4056_ = crate::leanh::lean_ctor_get(v___x_4033_, 0);
                        v_isSharedCheck_4063_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4033_)) as u8;
                        if v_isSharedCheck_4063_ == 0 {
                            v___x_4058_ = v___x_4033_;
                            v_isShared_4059_ = v_isSharedCheck_4063_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4056_);
                            crate::leanh::lean_dec(v___x_4033_);
                            v___x_4058_ = crate::leanh::lean_box(0);
                            v_isShared_4059_ = v_isSharedCheck_4063_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_k_4008_);
                    crate::leanh::lean_dec_ref(v_goal_4007_);
                    v_a_4064_ = crate::leanh::lean_ctor_get(v___x_4021_, 0);
                    v_isSharedCheck_4071_ = (!crate::leanh::lean_is_exclusive(v___x_4021_)) as u8;
                    if v_isSharedCheck_4071_ == 0 {
                        v___x_4066_ = v___x_4021_;
                        v_isShared_4067_ = v_isSharedCheck_4071_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4064_);
                        crate::leanh::lean_dec(v___x_4021_);
                        v___x_4066_ = crate::leanh::lean_box(0);
                        v_isShared_4067_ = v_isSharedCheck_4071_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_4040_ = crate::leanh::lean_ctor_get(v_a_4036_, 0);
                v_snd_4041_ = crate::leanh::lean_ctor_get(v_a_4036_, 1);
                v_isSharedCheck_4054_ = (!crate::leanh::lean_is_exclusive(v_a_4036_)) as u8;
                if v_isSharedCheck_4054_ == 0 {
                    v___x_4043_ = v_a_4036_;
                    v_isShared_4044_ = v_isSharedCheck_4054_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_4041_);
                    crate::leanh::lean_inc(v_fst_4040_);
                    crate::leanh::lean_dec(v_a_4036_);
                    v___x_4043_ = crate::leanh::lean_box(0);
                    v_isShared_4044_ = v_isSharedCheck_4054_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4045_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro_spec__0___redArg___closed__0;
                v___x_4046_ = l_Lean_mkConst(v___x_4045_, v___x_4029_);
                v_prf_4047_ = l_Lean_mkApp6(
                    v___x_4046_,
                    v_00_u03c3s_4024_,
                    v_hyps_4025_,
                    v_target_4026_,
                    v_a_4022_,
                    v_a_4034_,
                    v_snd_4041_,
                );
                if v_isShared_4044_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4043_, 1, v_prf_4047_);
                    v___x_4049_ = v___x_4043_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4053_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4053_, 0, v_fst_4040_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4053_, 1, v_prf_4047_);
                    v___x_4049_ = v_reuseFailAlloc_4053_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4039_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4038_, 0, v___x_4049_);
                    v___x_4051_ = v___x_4038_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4052_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4052_, 0, v___x_4049_);
                    v___x_4051_ = v_reuseFailAlloc_4052_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4051_;
            }
            5 => {
                if v_isShared_4059_ == 0 {
                    v___x_4061_ = v___x_4058_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4062_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4062_, 0, v_a_4056_);
                    v___x_4061_ = v_reuseFailAlloc_4062_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4061_;
            }
            7 => {
                if v_isShared_4067_ == 0 {
                    v___x_4069_ = v___x_4066_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4070_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4070_, 0, v_a_4064_);
                    v___x_4069_ = v_reuseFailAlloc_4070_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4069_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro_spec__0___redArg___boxed(
    mut v_goal_4072_: *mut crate::leanh::LeanObject,
    mut v_k_4073_: *mut crate::leanh::LeanObject,
    mut v___y_4074_: *mut crate::leanh::LeanObject,
    mut v___y_4075_: *mut crate::leanh::LeanObject,
    mut v___y_4076_: *mut crate::leanh::LeanObject,
    mut v___y_4077_: *mut crate::leanh::LeanObject,
    mut v___y_4078_: *mut crate::leanh::LeanObject,
    mut v___y_4079_: *mut crate::leanh::LeanObject,
    mut v___y_4080_: *mut crate::leanh::LeanObject,
    mut v___y_4081_: *mut crate::leanh::LeanObject,
    mut v___y_4082_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4083_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro_spec__0___redArg(v_goal_4072_, v_k_4073_, v___y_4074_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_, v___y_4081_);
    crate::leanh::lean_dec(v___y_4081_);
    crate::leanh::lean_dec_ref(v___y_4080_);
    crate::leanh::lean_dec(v___y_4079_);
    crate::leanh::lean_dec_ref(v___y_4078_);
    crate::leanh::lean_dec(v___y_4077_);
    crate::leanh::lean_dec_ref(v___y_4076_);
    crate::leanh::lean_dec(v___y_4075_);
    crate::leanh::lean_dec_ref(v___y_4074_);
    return v_res_4083_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro_spec__0(
    mut v_00_u03b1_4084_: *mut crate::leanh::LeanObject,
    mut v_goal_4085_: *mut crate::leanh::LeanObject,
    mut v_k_4086_: *mut crate::leanh::LeanObject,
    mut v___y_4087_: *mut crate::leanh::LeanObject,
    mut v___y_4088_: *mut crate::leanh::LeanObject,
    mut v___y_4089_: *mut crate::leanh::LeanObject,
    mut v___y_4090_: *mut crate::leanh::LeanObject,
    mut v___y_4091_: *mut crate::leanh::LeanObject,
    mut v___y_4092_: *mut crate::leanh::LeanObject,
    mut v___y_4093_: *mut crate::leanh::LeanObject,
    mut v___y_4094_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4096_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro_spec__0___redArg(v_goal_4085_, v_k_4086_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_, v___y_4093_, v___y_4094_);
    return v___x_4096_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro_spec__0___boxed(
    mut v_00_u03b1_4097_: *mut crate::leanh::LeanObject,
    mut v_goal_4098_: *mut crate::leanh::LeanObject,
    mut v_k_4099_: *mut crate::leanh::LeanObject,
    mut v___y_4100_: *mut crate::leanh::LeanObject,
    mut v___y_4101_: *mut crate::leanh::LeanObject,
    mut v___y_4102_: *mut crate::leanh::LeanObject,
    mut v___y_4103_: *mut crate::leanh::LeanObject,
    mut v___y_4104_: *mut crate::leanh::LeanObject,
    mut v___y_4105_: *mut crate::leanh::LeanObject,
    mut v___y_4106_: *mut crate::leanh::LeanObject,
    mut v___y_4107_: *mut crate::leanh::LeanObject,
    mut v___y_4108_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4109_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro_spec__0(v_00_u03b1_4097_, v_goal_4098_, v_k_4099_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_);
    crate::leanh::lean_dec(v___y_4107_);
    crate::leanh::lean_dec_ref(v___y_4106_);
    crate::leanh::lean_dec(v___y_4105_);
    crate::leanh::lean_dec_ref(v___y_4104_);
    crate::leanh::lean_dec(v___y_4103_);
    crate::leanh::lean_dec_ref(v___y_4102_);
    crate::leanh::lean_dec(v___y_4101_);
    crate::leanh::lean_dec_ref(v___y_4100_);
    return v_res_4109_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___lam__0(
    mut v_fst_4110_: *mut crate::leanh::LeanObject,
    mut v_00_u03c6_4111_: *mut crate::leanh::LeanObject,
    mut v___y_4112_: *mut crate::leanh::LeanObject,
    mut v___y_4113_: *mut crate::leanh::LeanObject,
    mut v___y_4114_: *mut crate::leanh::LeanObject,
    mut v___y_4115_: *mut crate::leanh::LeanObject,
    mut v___y_4116_: *mut crate::leanh::LeanObject,
    mut v___y_4117_: *mut crate::leanh::LeanObject,
    mut v___y_4118_: *mut crate::leanh::LeanObject,
    mut v___y_4119_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4127_: u8 = 0;
    let mut v___x_4128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4133_: u8 = 0;
    let mut v_a_4134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4137_: u8 = 0;
    let mut v___x_4139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4141_: u8 = 0;
    let mut v_a_4142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4145_: u8 = 0;
    let mut v___x_4147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4149_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4121_ = l_Lean_MVarId_getTag(
                    v_fst_4110_,
                    v___y_4116_,
                    v___y_4117_,
                    v___y_4118_,
                    v___y_4119_,
                );
                if crate::leanh::lean_obj_tag(v___x_4121_) == 0 {
                    v_a_4122_ = crate::leanh::lean_ctor_get(v___x_4121_, 0);
                    crate::leanh::lean_inc(v_a_4122_);
                    crate::leanh::lean_dec_ref_known(v___x_4121_, 1);
                    v___x_4123_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                        v_00_u03c6_4111_,
                        v_a_4122_,
                        v___y_4116_,
                        v___y_4117_,
                        v___y_4118_,
                        v___y_4119_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4123_) == 0 {
                        v_a_4124_ = crate::leanh::lean_ctor_get(v___x_4123_, 0);
                        v_isSharedCheck_4133_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4123_)) as u8;
                        if v_isSharedCheck_4133_ == 0 {
                            v___x_4126_ = v___x_4123_;
                            v_isShared_4127_ = v_isSharedCheck_4133_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4124_);
                            crate::leanh::lean_dec(v___x_4123_);
                            v___x_4126_ = crate::leanh::lean_box(0);
                            v_isShared_4127_ = v_isSharedCheck_4133_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4134_ = crate::leanh::lean_ctor_get(v___x_4123_, 0);
                        v_isSharedCheck_4141_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4123_)) as u8;
                        if v_isSharedCheck_4141_ == 0 {
                            v___x_4136_ = v___x_4123_;
                            v_isShared_4137_ = v_isSharedCheck_4141_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4134_);
                            crate::leanh::lean_dec(v___x_4123_);
                            v___x_4136_ = crate::leanh::lean_box(0);
                            v_isShared_4137_ = v_isSharedCheck_4141_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_00_u03c6_4111_);
                    v_a_4142_ = crate::leanh::lean_ctor_get(v___x_4121_, 0);
                    v_isSharedCheck_4149_ = (!crate::leanh::lean_is_exclusive(v___x_4121_)) as u8;
                    if v_isSharedCheck_4149_ == 0 {
                        v___x_4144_ = v___x_4121_;
                        v_isShared_4145_ = v_isSharedCheck_4149_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4142_);
                        crate::leanh::lean_dec(v___x_4121_);
                        v___x_4144_ = crate::leanh::lean_box(0);
                        v_isShared_4145_ = v_isSharedCheck_4149_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4128_ = l_Lean_Expr_mvarId_x21(v_a_4124_);
                v___x_4129_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4129_, 0, v___x_4128_);
                crate::leanh::lean_ctor_set(v___x_4129_, 1, v_a_4124_);
                if v_isShared_4127_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4126_, 0, v___x_4129_);
                    v___x_4131_ = v___x_4126_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4132_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4132_, 0, v___x_4129_);
                    v___x_4131_ = v_reuseFailAlloc_4132_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4131_;
            }
            3 => {
                if v_isShared_4137_ == 0 {
                    v___x_4139_ = v___x_4136_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4140_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4140_, 0, v_a_4134_);
                    v___x_4139_ = v_reuseFailAlloc_4140_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4139_;
            }
            5 => {
                if v_isShared_4145_ == 0 {
                    v___x_4147_ = v___x_4144_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4148_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4148_, 0, v_a_4142_);
                    v___x_4147_ = v_reuseFailAlloc_4148_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4147_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___lam__0___boxed(
    mut v_fst_4150_: *mut crate::leanh::LeanObject,
    mut v_00_u03c6_4151_: *mut crate::leanh::LeanObject,
    mut v___y_4152_: *mut crate::leanh::LeanObject,
    mut v___y_4153_: *mut crate::leanh::LeanObject,
    mut v___y_4154_: *mut crate::leanh::LeanObject,
    mut v___y_4155_: *mut crate::leanh::LeanObject,
    mut v___y_4156_: *mut crate::leanh::LeanObject,
    mut v___y_4157_: *mut crate::leanh::LeanObject,
    mut v___y_4158_: *mut crate::leanh::LeanObject,
    mut v___y_4159_: *mut crate::leanh::LeanObject,
    mut v___y_4160_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4161_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___lam__0(
        v_fst_4150_,
        v_00_u03c6_4151_,
        v___y_4152_,
        v___y_4153_,
        v___y_4154_,
        v___y_4155_,
        v___y_4156_,
        v___y_4157_,
        v___y_4158_,
        v___y_4159_,
    );
    crate::leanh::lean_dec(v___y_4159_);
    crate::leanh::lean_dec_ref(v___y_4158_);
    crate::leanh::lean_dec(v___y_4157_);
    crate::leanh::lean_dec_ref(v___y_4156_);
    crate::leanh::lean_dec(v___y_4155_);
    crate::leanh::lean_dec_ref(v___y_4154_);
    crate::leanh::lean_dec(v___y_4153_);
    crate::leanh::lean_dec_ref(v___y_4152_);
    return v_res_4161_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___lam__1(
    mut v_snd_4162_: *mut crate::leanh::LeanObject,
    mut v___f_4163_: *mut crate::leanh::LeanObject,
    mut v_fst_4164_: *mut crate::leanh::LeanObject,
    mut v___y_4165_: *mut crate::leanh::LeanObject,
    mut v___y_4166_: *mut crate::leanh::LeanObject,
    mut v___y_4167_: *mut crate::leanh::LeanObject,
    mut v___y_4168_: *mut crate::leanh::LeanObject,
    mut v___y_4169_: *mut crate::leanh::LeanObject,
    mut v___y_4170_: *mut crate::leanh::LeanObject,
    mut v___y_4171_: *mut crate::leanh::LeanObject,
    mut v___y_4172_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4180_: u8 = 0;
    let mut v___x_4181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4187_: u8 = 0;
    let mut v_a_4188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4191_: u8 = 0;
    let mut v___x_4193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4195_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4174_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro_spec__0___redArg(v_snd_4162_, v___f_4163_, v___y_4165_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_, v___y_4172_);
                if crate::leanh::lean_obj_tag(v___x_4174_) == 0 {
                    v_a_4175_ = crate::leanh::lean_ctor_get(v___x_4174_, 0);
                    crate::leanh::lean_inc(v_a_4175_);
                    crate::leanh::lean_dec_ref_known(v___x_4174_, 1);
                    v_fst_4176_ = crate::leanh::lean_ctor_get(v_a_4175_, 0);
                    v_snd_4177_ = crate::leanh::lean_ctor_get(v_a_4175_, 1);
                    v_isSharedCheck_4187_ = (!crate::leanh::lean_is_exclusive(v_a_4175_)) as u8;
                    if v_isSharedCheck_4187_ == 0 {
                        v___x_4179_ = v_a_4175_;
                        v_isShared_4180_ = v_isSharedCheck_4187_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_4177_);
                        crate::leanh::lean_inc(v_fst_4176_);
                        crate::leanh::lean_dec(v_a_4175_);
                        v___x_4179_ = crate::leanh::lean_box(0);
                        v_isShared_4180_ = v_isSharedCheck_4187_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_fst_4164_);
                    v_a_4188_ = crate::leanh::lean_ctor_get(v___x_4174_, 0);
                    v_isSharedCheck_4195_ = (!crate::leanh::lean_is_exclusive(v___x_4174_)) as u8;
                    if v_isSharedCheck_4195_ == 0 {
                        v___x_4190_ = v___x_4174_;
                        v_isShared_4191_ = v_isSharedCheck_4195_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4188_);
                        crate::leanh::lean_dec(v___x_4174_);
                        v___x_4190_ = crate::leanh::lean_box(0);
                        v_isShared_4191_ = v_isSharedCheck_4195_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4181_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2___redArg(v_fst_4164_, v_snd_4177_, v___y_4170_);
                crate::leanh::lean_dec_ref(v___x_4181_);
                v___x_4182_ = crate::leanh::lean_box(0);
                if v_isShared_4180_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4179_, 1);
                    crate::leanh::lean_ctor_set(v___x_4179_, 1, v___x_4182_);
                    v___x_4184_ = v___x_4179_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4186_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4186_, 0, v_fst_4176_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4186_, 1, v___x_4182_);
                    v___x_4184_ = v_reuseFailAlloc_4186_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4185_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                    v___x_4184_,
                    v___y_4166_,
                    v___y_4169_,
                    v___y_4170_,
                    v___y_4171_,
                    v___y_4172_,
                );
                return v___x_4185_;
            }
            3 => {
                if v_isShared_4191_ == 0 {
                    v___x_4193_ = v___x_4190_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4194_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4194_, 0, v_a_4188_);
                    v___x_4193_ = v_reuseFailAlloc_4194_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4193_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___lam__1___boxed(
    mut v_snd_4196_: *mut crate::leanh::LeanObject,
    mut v___f_4197_: *mut crate::leanh::LeanObject,
    mut v_fst_4198_: *mut crate::leanh::LeanObject,
    mut v___y_4199_: *mut crate::leanh::LeanObject,
    mut v___y_4200_: *mut crate::leanh::LeanObject,
    mut v___y_4201_: *mut crate::leanh::LeanObject,
    mut v___y_4202_: *mut crate::leanh::LeanObject,
    mut v___y_4203_: *mut crate::leanh::LeanObject,
    mut v___y_4204_: *mut crate::leanh::LeanObject,
    mut v___y_4205_: *mut crate::leanh::LeanObject,
    mut v___y_4206_: *mut crate::leanh::LeanObject,
    mut v___y_4207_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4208_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___lam__1(
        v_snd_4196_,
        v___f_4197_,
        v_fst_4198_,
        v___y_4199_,
        v___y_4200_,
        v___y_4201_,
        v___y_4202_,
        v___y_4203_,
        v___y_4204_,
        v___y_4205_,
        v___y_4206_,
    );
    crate::leanh::lean_dec(v___y_4206_);
    crate::leanh::lean_dec_ref(v___y_4205_);
    crate::leanh::lean_dec(v___y_4204_);
    crate::leanh::lean_dec_ref(v___y_4203_);
    crate::leanh::lean_dec(v___y_4202_);
    crate::leanh::lean_dec_ref(v___y_4201_);
    crate::leanh::lean_dec(v___y_4200_);
    crate::leanh::lean_dec_ref(v___y_4199_);
    return v_res_4208_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro(
    mut v_x_4215_: *mut crate::leanh::LeanObject,
    mut v_a_4216_: *mut crate::leanh::LeanObject,
    mut v_a_4217_: *mut crate::leanh::LeanObject,
    mut v_a_4218_: *mut crate::leanh::LeanObject,
    mut v_a_4219_: *mut crate::leanh::LeanObject,
    mut v_a_4220_: *mut crate::leanh::LeanObject,
    mut v_a_4221_: *mut crate::leanh::LeanObject,
    mut v_a_4222_: *mut crate::leanh::LeanObject,
    mut v_a_4223_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: u8 = 0;
    let mut v___x_4227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4238_: u8 = 0;
    let mut v___x_4240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4242_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4225_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___closed__1;
                v___x_4226_ = l_Lean_Syntax_isOfKind(v_x_4215_, v___x_4225_);
                if v___x_4226_ == 0 {
                    v___x_4227_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__0___redArg();
                    return v___x_4227_;
                } else {
                    v___x_4228_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(
                        v_a_4217_, v_a_4220_, v_a_4221_, v_a_4222_, v_a_4223_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4228_) == 0 {
                        v_a_4229_ = crate::leanh::lean_ctor_get(v___x_4228_, 0);
                        crate::leanh::lean_inc(v_a_4229_);
                        crate::leanh::lean_dec_ref_known(v___x_4228_, 1);
                        v_fst_4230_ = crate::leanh::lean_ctor_get(v_a_4229_, 0);
                        crate::leanh::lean_inc_n(v_fst_4230_, 3);
                        v_snd_4231_ = crate::leanh::lean_ctor_get(v_a_4229_, 1);
                        crate::leanh::lean_inc(v_snd_4231_);
                        crate::leanh::lean_dec(v_a_4229_);
                        v___f_4232_ = crate::leanh::lean_alloc_closure(
                            l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___lam__0___boxed
                                as *mut core::ffi::c_void,
                            11,
                            1,
                        );
                        crate::leanh::lean_closure_set(v___f_4232_, 0, v_fst_4230_);
                        v___f_4233_ = crate::leanh::lean_alloc_closure(
                            l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___lam__1___boxed
                                as *mut core::ffi::c_void,
                            12,
                            3,
                        );
                        crate::leanh::lean_closure_set(v___f_4233_, 0, v_snd_4231_);
                        crate::leanh::lean_closure_set(v___f_4233_, 1, v___f_4232_);
                        crate::leanh::lean_closure_set(v___f_4233_, 2, v_fst_4230_);
                        v___x_4234_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__3___redArg(v_fst_4230_, v___f_4233_, v_a_4216_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_, v_a_4221_, v_a_4222_, v_a_4223_);
                        return v___x_4234_;
                    } else {
                        v_a_4235_ = crate::leanh::lean_ctor_get(v___x_4228_, 0);
                        v_isSharedCheck_4242_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4228_)) as u8;
                        if v_isSharedCheck_4242_ == 0 {
                            v___x_4237_ = v___x_4228_;
                            v_isShared_4238_ = v_isSharedCheck_4242_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4235_);
                            crate::leanh::lean_dec(v___x_4228_);
                            v___x_4237_ = crate::leanh::lean_box(0);
                            v_isShared_4238_ = v_isSharedCheck_4242_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_4238_ == 0 {
                    v___x_4240_ = v___x_4237_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4241_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4241_, 0, v_a_4235_);
                    v___x_4240_ = v_reuseFailAlloc_4241_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4240_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___boxed(
    mut v_x_4243_: *mut crate::leanh::LeanObject,
    mut v_a_4244_: *mut crate::leanh::LeanObject,
    mut v_a_4245_: *mut crate::leanh::LeanObject,
    mut v_a_4246_: *mut crate::leanh::LeanObject,
    mut v_a_4247_: *mut crate::leanh::LeanObject,
    mut v_a_4248_: *mut crate::leanh::LeanObject,
    mut v_a_4249_: *mut crate::leanh::LeanObject,
    mut v_a_4250_: *mut crate::leanh::LeanObject,
    mut v_a_4251_: *mut crate::leanh::LeanObject,
    mut v_a_4252_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4253_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro(
        v_x_4243_, v_a_4244_, v_a_4245_, v_a_4246_, v_a_4247_, v_a_4248_, v_a_4249_, v_a_4250_,
        v_a_4251_,
    );
    crate::leanh::lean_dec(v_a_4251_);
    crate::leanh::lean_dec_ref(v_a_4250_);
    crate::leanh::lean_dec(v_a_4249_);
    crate::leanh::lean_dec_ref(v_a_4248_);
    crate::leanh::lean_dec(v_a_4247_);
    crate::leanh::lean_dec_ref(v_a_4246_);
    crate::leanh::lean_dec(v_a_4245_);
    crate::leanh::lean_dec_ref(v_a_4244_);
    return v_res_4253_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4263_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_4264_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___closed__1;
    v___x_4265_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro__1___closed__1;
    v___x_4266_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_4267_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_4263_,
        v___x_4264_,
        v___x_4265_,
        v___x_4266_,
    );
    return v___x_4267_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro__1___boxed(
    mut v_a_4268_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4269_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro__1();
    return v_res_4269_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_4282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4281_ = crate::leanh::lean_box(0);
    v_dummy_4282_ = l_Lean_Expr_sort___override(v___x_4281_);
    return v_dummy_4282_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp(
    mut v_e_4283_: *mut crate::leanh::LeanObject,
    mut v_a_4284_: *mut crate::leanh::LeanObject,
    mut v_a_4285_: *mut crate::leanh::LeanObject,
    mut v_a_4286_: *mut crate::leanh::LeanObject,
    mut v_a_4287_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4293_: u8 = 0;
    let mut v___x_4294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4296_: u8 = 0;
    let mut v___x_4297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4304_: u8 = 0;
    let mut v___x_4305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_4309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_4310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4316_: u8 = 0;
    let mut v___x_4317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4324_: u8 = 0;
    let mut v___x_4325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4326_: u8 = 0;
    let mut v___x_4327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4336_: u8 = 0;
    let mut v_a_4337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4340_: u8 = 0;
    let mut v___x_4342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4344_: u8 = 0;
    let mut v___x_4345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4349_: u8 = 0;
    let mut v_a_4350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4353_: u8 = 0;
    let mut v___x_4355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4357_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4289_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_4283_, v_a_4285_);
                if crate::leanh::lean_obj_tag(v___x_4289_) == 0 {
                    v_a_4290_ = crate::leanh::lean_ctor_get(v___x_4289_, 0);
                    v_isSharedCheck_4349_ = (!crate::leanh::lean_is_exclusive(v___x_4289_)) as u8;
                    if v_isSharedCheck_4349_ == 0 {
                        v___x_4292_ = v___x_4289_;
                        v_isShared_4293_ = v_isSharedCheck_4349_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4290_);
                        crate::leanh::lean_dec(v___x_4289_);
                        v___x_4292_ = crate::leanh::lean_box(0);
                        v_isShared_4293_ = v_isSharedCheck_4349_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4350_ = crate::leanh::lean_ctor_get(v___x_4289_, 0);
                    v_isSharedCheck_4357_ = (!crate::leanh::lean_is_exclusive(v___x_4289_)) as u8;
                    if v_isSharedCheck_4357_ == 0 {
                        v___x_4352_ = v___x_4289_;
                        v_isShared_4353_ = v_isSharedCheck_4357_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4350_);
                        crate::leanh::lean_dec(v___x_4289_);
                        v___x_4352_ = crate::leanh::lean_box(0);
                        v_isShared_4353_ = v_isSharedCheck_4357_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4294_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___closed__2;
                v___x_4295_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_4296_ = l_Lean_Expr_isAppOfArity(v_a_4290_, v___x_4294_, v___x_4295_);
                if v___x_4296_ == 0 {
                    crate::leanh::lean_dec(v_a_4290_);
                    v___x_4297_ = crate::leanh::lean_box(0);
                    if v_isShared_4293_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4292_, 0, v___x_4297_);
                        v___x_4299_ = v___x_4292_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4300_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4300_, 0, v___x_4297_);
                        v___x_4299_ = v_reuseFailAlloc_4300_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_4301_ = l_Lean_Expr_appArg_x21(v_a_4290_);
                    crate::leanh::lean_dec(v_a_4290_);
                    v___x_4302_ = l_Lean_Expr_getAppFn(v___x_4301_);
                    v___x_4303_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___closed__4;
                    v___x_4304_ = l_Lean_Expr_isConstOf(v___x_4302_, v___x_4303_);
                    crate::leanh::lean_dec_ref(v___x_4302_);
                    if v___x_4304_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_4301_);
                        v___x_4305_ = crate::leanh::lean_box(0);
                        if v_isShared_4293_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4292_, 0, v___x_4305_);
                            v___x_4307_ = v___x_4292_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4308_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4308_, 0, v___x_4305_);
                            v___x_4307_ = v_reuseFailAlloc_4308_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_dummy_4309_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___closed__5_once), _init_l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___closed__5);
                        v_nargs_4310_ = l_Lean_Expr_getAppNumArgs(v___x_4301_);
                        crate::leanh::lean_inc(v_nargs_4310_);
                        v___x_4311_ = lean_mk_array(v_nargs_4310_, v_dummy_4309_);
                        v___x_4312_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_4313_ = lean_nat_sub(v_nargs_4310_, v___x_4312_);
                        crate::leanh::lean_dec(v_nargs_4310_);
                        v___x_4314_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                            v___x_4301_,
                            v___x_4311_,
                            v___x_4313_,
                        );
                        v___x_4315_ = lean_array_get_size(v___x_4314_);
                        v___x_4316_ = lean_nat_dec_lt(v___x_4315_, v___x_4295_);
                        if v___x_4316_ == 0 {
                            crate::leanh::lean_del_object(v___x_4292_);
                            v___x_4317_ = l_Lean_instInhabitedExpr;
                            v___x_4318_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___x_4319_ = lean_array_get(v___x_4317_, v___x_4314_, v___x_4318_);
                            v___x_4320_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_length(
                                v___x_4319_,
                                v_a_4284_,
                                v_a_4285_,
                                v_a_4286_,
                                v_a_4287_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_4320_) == 0 {
                                v_a_4321_ = crate::leanh::lean_ctor_get(v___x_4320_, 0);
                                v_isSharedCheck_4336_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4320_)) as u8;
                                if v_isSharedCheck_4336_ == 0 {
                                    v___x_4323_ = v___x_4320_;
                                    v_isShared_4324_ = v_isSharedCheck_4336_;
                                    state = 4;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4321_);
                                    crate::leanh::lean_dec(v___x_4320_);
                                    v___x_4323_ = crate::leanh::lean_box(0);
                                    v_isShared_4324_ = v_isSharedCheck_4336_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v___x_4314_);
                                v_a_4337_ = crate::leanh::lean_ctor_get(v___x_4320_, 0);
                                v_isSharedCheck_4344_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4320_)) as u8;
                                if v_isSharedCheck_4344_ == 0 {
                                    v___x_4339_ = v___x_4320_;
                                    v_isShared_4340_ = v_isSharedCheck_4344_;
                                    state = 7;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4337_);
                                    crate::leanh::lean_dec(v___x_4320_);
                                    v___x_4339_ = crate::leanh::lean_box(0);
                                    v_isShared_4340_ = v_isSharedCheck_4344_;
                                    state = 7;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_4314_);
                            v___x_4345_ = crate::leanh::lean_box(0);
                            if v_isShared_4293_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_4292_, 0, v___x_4345_);
                                v___x_4347_ = v___x_4292_;
                                state = 9;
                                continue;
                            } else {
                                v_reuseFailAlloc_4348_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_4348_, 0, v___x_4345_);
                                v___x_4347_ = v_reuseFailAlloc_4348_;
                                state = 9;
                                continue;
                            }
                        }
                    }
                }
            }
            2 => {
                return v___x_4299_;
            }
            3 => {
                return v___x_4307_;
            }
            4 => {
                v___x_4325_ = lean_nat_sub(v___x_4315_, v___x_4295_);
                v___x_4326_ = lean_nat_dec_eq(v_a_4321_, v___x_4325_);
                crate::leanh::lean_dec(v___x_4325_);
                crate::leanh::lean_dec(v_a_4321_);
                if v___x_4326_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_4314_);
                    v___x_4327_ = crate::leanh::lean_box(0);
                    if v_isShared_4324_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4323_, 0, v___x_4327_);
                        v___x_4329_ = v___x_4323_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4330_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4330_, 0, v___x_4327_);
                        v___x_4329_ = v_reuseFailAlloc_4330_;
                        state = 5;
                        continue;
                    }
                } else {
                    v___x_4331_ = lean_array_get(v___x_4317_, v___x_4314_, v___x_4312_);
                    crate::leanh::lean_dec_ref(v___x_4314_);
                    v___x_4332_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4332_, 0, v___x_4331_);
                    if v_isShared_4324_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4323_, 0, v___x_4332_);
                        v___x_4334_ = v___x_4323_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_4335_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4335_, 0, v___x_4332_);
                        v___x_4334_ = v_reuseFailAlloc_4335_;
                        state = 6;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_4329_;
            }
            6 => {
                return v___x_4334_;
            }
            7 => {
                if v_isShared_4340_ == 0 {
                    v___x_4342_ = v___x_4339_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4343_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4343_, 0, v_a_4337_);
                    v___x_4342_ = v_reuseFailAlloc_4343_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4342_;
            }
            9 => {
                return v___x_4347_;
            }
            10 => {
                if v_isShared_4353_ == 0 {
                    v___x_4355_ = v___x_4352_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4356_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4356_, 0, v_a_4350_);
                    v___x_4355_ = v_reuseFailAlloc_4356_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4355_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp___boxed(
    mut v_e_4358_: *mut crate::leanh::LeanObject,
    mut v_a_4359_: *mut crate::leanh::LeanObject,
    mut v_a_4360_: *mut crate::leanh::LeanObject,
    mut v_a_4361_: *mut crate::leanh::LeanObject,
    mut v_a_4362_: *mut crate::leanh::LeanObject,
    mut v_a_4363_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4364_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp(v_e_4358_, v_a_4359_, v_a_4360_, v_a_4361_, v_a_4362_);
    crate::leanh::lean_dec(v_a_4362_);
    crate::leanh::lean_dec_ref(v_a_4361_);
    crate::leanh::lean_dec(v_a_4360_);
    crate::leanh::lean_dec_ref(v_a_4359_);
    return v_res_4364_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1_spec__1(
    mut v_msgData_4365_: *mut crate::leanh::LeanObject,
    mut v___y_4366_: *mut crate::leanh::LeanObject,
    mut v___y_4367_: *mut crate::leanh::LeanObject,
    mut v___y_4368_: *mut crate::leanh::LeanObject,
    mut v___y_4369_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_4375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4371_ = lean_st_ref_get(v___y_4369_);
    v_env_4372_ = crate::leanh::lean_ctor_get(v___x_4371_, 0);
    crate::leanh::lean_inc_ref(v_env_4372_);
    crate::leanh::lean_dec(v___x_4371_);
    v___x_4373_ = lean_st_ref_get(v___y_4367_);
    v_mctx_4374_ = crate::leanh::lean_ctor_get(v___x_4373_, 0);
    crate::leanh::lean_inc_ref(v_mctx_4374_);
    crate::leanh::lean_dec(v___x_4373_);
    v_lctx_4375_ = crate::leanh::lean_ctor_get(v___y_4366_, 2);
    v_options_4376_ = crate::leanh::lean_ctor_get(v___y_4368_, 2);
    crate::leanh::lean_inc_ref(v_options_4376_);
    crate::leanh::lean_inc_ref(v_lctx_4375_);
    v___x_4377_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4377_, 0, v_env_4372_);
    crate::leanh::lean_ctor_set(v___x_4377_, 1, v_mctx_4374_);
    crate::leanh::lean_ctor_set(v___x_4377_, 2, v_lctx_4375_);
    crate::leanh::lean_ctor_set(v___x_4377_, 3, v_options_4376_);
    v___x_4378_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4378_, 0, v___x_4377_);
    crate::leanh::lean_ctor_set(v___x_4378_, 1, v_msgData_4365_);
    v___x_4379_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4379_, 0, v___x_4378_);
    return v___x_4379_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1_spec__1___boxed(
    mut v_msgData_4380_: *mut crate::leanh::LeanObject,
    mut v___y_4381_: *mut crate::leanh::LeanObject,
    mut v___y_4382_: *mut crate::leanh::LeanObject,
    mut v___y_4383_: *mut crate::leanh::LeanObject,
    mut v___y_4384_: *mut crate::leanh::LeanObject,
    mut v___y_4385_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4386_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1_spec__1(v_msgData_4380_, v___y_4381_, v___y_4382_, v___y_4383_, v___y_4384_);
    crate::leanh::lean_dec(v___y_4384_);
    crate::leanh::lean_dec_ref(v___y_4383_);
    crate::leanh::lean_dec(v___y_4382_);
    crate::leanh::lean_dec_ref(v___y_4381_);
    return v_res_4386_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1___closed__0()
-> f64 {
    let mut v___x_4387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4388_: f64 = 0.0;
    v___x_4387_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4388_ = lean_float_of_nat(v___x_4387_);
    return v___x_4388_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1(
    mut v_cls_4392_: *mut crate::leanh::LeanObject,
    mut v_msg_4393_: *mut crate::leanh::LeanObject,
    mut v___y_4394_: *mut crate::leanh::LeanObject,
    mut v___y_4395_: *mut crate::leanh::LeanObject,
    mut v___y_4396_: *mut crate::leanh::LeanObject,
    mut v___y_4397_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_4399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4404_: u8 = 0;
    let mut v___x_4405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_4411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4417_: u8 = 0;
    let mut v_tid_4418_: u64 = 0;
    let mut v_traces_4419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4422_: u8 = 0;
    let mut v___x_4423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4424_: f64 = 0.0;
    let mut v___x_4425_: u8 = 0;
    let mut v___x_4426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4443_: u8 = 0;
    let mut v_isSharedCheck_4444_: u8 = 0;
    let mut v_isSharedCheck_4445_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4399_ = crate::leanh::lean_ctor_get(v___y_4396_, 5);
                v___x_4400_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1_spec__1(v_msg_4393_, v___y_4394_, v___y_4395_, v___y_4396_, v___y_4397_);
                v_a_4401_ = crate::leanh::lean_ctor_get(v___x_4400_, 0);
                v_isSharedCheck_4445_ = (!crate::leanh::lean_is_exclusive(v___x_4400_)) as u8;
                if v_isSharedCheck_4445_ == 0 {
                    v___x_4403_ = v___x_4400_;
                    v_isShared_4404_ = v_isSharedCheck_4445_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_4401_);
                    crate::leanh::lean_dec(v___x_4400_);
                    v___x_4403_ = crate::leanh::lean_box(0);
                    v_isShared_4404_ = v_isSharedCheck_4445_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4405_ = lean_st_ref_take(v___y_4397_);
                v_traceState_4406_ = crate::leanh::lean_ctor_get(v___x_4405_, 4);
                v_env_4407_ = crate::leanh::lean_ctor_get(v___x_4405_, 0);
                v_nextMacroScope_4408_ = crate::leanh::lean_ctor_get(v___x_4405_, 1);
                v_ngen_4409_ = crate::leanh::lean_ctor_get(v___x_4405_, 2);
                v_auxDeclNGen_4410_ = crate::leanh::lean_ctor_get(v___x_4405_, 3);
                v_cache_4411_ = crate::leanh::lean_ctor_get(v___x_4405_, 5);
                v_messages_4412_ = crate::leanh::lean_ctor_get(v___x_4405_, 6);
                v_infoState_4413_ = crate::leanh::lean_ctor_get(v___x_4405_, 7);
                v_snapshotTasks_4414_ = crate::leanh::lean_ctor_get(v___x_4405_, 8);
                v_isSharedCheck_4444_ = (!crate::leanh::lean_is_exclusive(v___x_4405_)) as u8;
                if v_isSharedCheck_4444_ == 0 {
                    v___x_4416_ = v___x_4405_;
                    v_isShared_4417_ = v_isSharedCheck_4444_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_4414_);
                    crate::leanh::lean_inc(v_infoState_4413_);
                    crate::leanh::lean_inc(v_messages_4412_);
                    crate::leanh::lean_inc(v_cache_4411_);
                    crate::leanh::lean_inc(v_traceState_4406_);
                    crate::leanh::lean_inc(v_auxDeclNGen_4410_);
                    crate::leanh::lean_inc(v_ngen_4409_);
                    crate::leanh::lean_inc(v_nextMacroScope_4408_);
                    crate::leanh::lean_inc(v_env_4407_);
                    crate::leanh::lean_dec(v___x_4405_);
                    v___x_4416_ = crate::leanh::lean_box(0);
                    v_isShared_4417_ = v_isSharedCheck_4444_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_4418_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_4406_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_4419_ = crate::leanh::lean_ctor_get(v_traceState_4406_, 0);
                v_isSharedCheck_4443_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_4406_)) as u8;
                if v_isSharedCheck_4443_ == 0 {
                    v___x_4421_ = v_traceState_4406_;
                    v_isShared_4422_ = v_isSharedCheck_4443_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_4419_);
                    crate::leanh::lean_dec(v_traceState_4406_);
                    v___x_4421_ = crate::leanh::lean_box(0);
                    v_isShared_4422_ = v_isSharedCheck_4443_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4423_ = crate::leanh::lean_box(0);
                v___x_4424_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1___closed__0_once), _init_l_Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1___closed__0);
                v___x_4425_ = 0;
                v___x_4426_ =
                    l_Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1___closed__1;
                v___x_4427_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v___x_4427_, 0, v_cls_4392_);
                crate::leanh::lean_ctor_set(v___x_4427_, 1, v___x_4423_);
                crate::leanh::lean_ctor_set(v___x_4427_, 2, v___x_4426_);
                crate::leanh::lean_ctor_set_float(
                    v___x_4427_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_4424_,
                );
                crate::leanh::lean_ctor_set_float(
                    v___x_4427_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_4424_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4427_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_4425_,
                );
                v___x_4428_ =
                    l_Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1___closed__2;
                v___x_4429_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4429_, 0, v___x_4427_);
                crate::leanh::lean_ctor_set(v___x_4429_, 1, v_a_4401_);
                crate::leanh::lean_ctor_set(v___x_4429_, 2, v___x_4428_);
                crate::leanh::lean_inc(v_ref_4399_);
                v___x_4430_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4430_, 0, v_ref_4399_);
                crate::leanh::lean_ctor_set(v___x_4430_, 1, v___x_4429_);
                v___x_4431_ = l_Lean_PersistentArray_push___redArg(v_traces_4419_, v___x_4430_);
                if v_isShared_4422_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4421_, 0, v___x_4431_);
                    v___x_4433_ = v___x_4421_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4442_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4442_, 0, v___x_4431_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_4442_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_4418_,
                    );
                    v___x_4433_ = v_reuseFailAlloc_4442_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4417_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4416_, 4, v___x_4433_);
                    v___x_4435_ = v___x_4416_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4441_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4441_, 0, v_env_4407_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4441_, 1, v_nextMacroScope_4408_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4441_, 2, v_ngen_4409_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4441_, 3, v_auxDeclNGen_4410_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4441_, 4, v___x_4433_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4441_, 5, v_cache_4411_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4441_, 6, v_messages_4412_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4441_, 7, v_infoState_4413_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4441_, 8, v_snapshotTasks_4414_);
                    v___x_4435_ = v_reuseFailAlloc_4441_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4436_ = lean_st_ref_set(v___y_4397_, v___x_4435_);
                v___x_4437_ = crate::leanh::lean_box(0);
                if v_isShared_4404_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4403_, 0, v___x_4437_);
                    v___x_4439_ = v___x_4403_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4440_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4440_, 0, v___x_4437_);
                    v___x_4439_ = v_reuseFailAlloc_4440_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4439_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1___boxed(
    mut v_cls_4446_: *mut crate::leanh::LeanObject,
    mut v_msg_4447_: *mut crate::leanh::LeanObject,
    mut v___y_4448_: *mut crate::leanh::LeanObject,
    mut v___y_4449_: *mut crate::leanh::LeanObject,
    mut v___y_4450_: *mut crate::leanh::LeanObject,
    mut v___y_4451_: *mut crate::leanh::LeanObject,
    mut v___y_4452_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4453_ = l_Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1(
        v_cls_4446_,
        v_msg_4447_,
        v___y_4448_,
        v___y_4449_,
        v___y_4450_,
        v___y_4451_,
    );
    crate::leanh::lean_dec(v___y_4451_);
    crate::leanh::lean_dec_ref(v___y_4450_);
    crate::leanh::lean_dec(v___y_4449_);
    crate::leanh::lean_dec_ref(v___y_4448_);
    return v_res_4453_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_applyRflAndAndIntro_spec__0___redArg(
    mut v_mvarId_4454_: *mut crate::leanh::LeanObject,
    mut v_val_4455_: *mut crate::leanh::LeanObject,
    mut v___y_4456_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_4460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_4462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4466_: u8 = 0;
    let mut v_depth_4467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_4468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_4469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_4470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lDecls_4471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_4472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userNames_4473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_4474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_4475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_4476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4479_: u8 = 0;
    let mut v___x_4480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4490_: u8 = 0;
    let mut v_isSharedCheck_4491_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4458_ = lean_st_ref_take(v___y_4456_);
                v_mctx_4459_ = crate::leanh::lean_ctor_get(v___x_4458_, 0);
                v_cache_4460_ = crate::leanh::lean_ctor_get(v___x_4458_, 1);
                v_zetaDeltaFVarIds_4461_ = crate::leanh::lean_ctor_get(v___x_4458_, 2);
                v_postponed_4462_ = crate::leanh::lean_ctor_get(v___x_4458_, 3);
                v_diag_4463_ = crate::leanh::lean_ctor_get(v___x_4458_, 4);
                v_isSharedCheck_4491_ = (!crate::leanh::lean_is_exclusive(v___x_4458_)) as u8;
                if v_isSharedCheck_4491_ == 0 {
                    v___x_4465_ = v___x_4458_;
                    v_isShared_4466_ = v_isSharedCheck_4491_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_4463_);
                    crate::leanh::lean_inc(v_postponed_4462_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_4461_);
                    crate::leanh::lean_inc(v_cache_4460_);
                    crate::leanh::lean_inc(v_mctx_4459_);
                    crate::leanh::lean_dec(v___x_4458_);
                    v___x_4465_ = crate::leanh::lean_box(0);
                    v_isShared_4466_ = v_isSharedCheck_4491_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_4467_ = crate::leanh::lean_ctor_get(v_mctx_4459_, 0);
                v_levelAssignDepth_4468_ = crate::leanh::lean_ctor_get(v_mctx_4459_, 1);
                v_lmvarCounter_4469_ = crate::leanh::lean_ctor_get(v_mctx_4459_, 2);
                v_mvarCounter_4470_ = crate::leanh::lean_ctor_get(v_mctx_4459_, 3);
                v_lDecls_4471_ = crate::leanh::lean_ctor_get(v_mctx_4459_, 4);
                v_decls_4472_ = crate::leanh::lean_ctor_get(v_mctx_4459_, 5);
                v_userNames_4473_ = crate::leanh::lean_ctor_get(v_mctx_4459_, 6);
                v_lAssignment_4474_ = crate::leanh::lean_ctor_get(v_mctx_4459_, 7);
                v_eAssignment_4475_ = crate::leanh::lean_ctor_get(v_mctx_4459_, 8);
                v_dAssignment_4476_ = crate::leanh::lean_ctor_get(v_mctx_4459_, 9);
                v_isSharedCheck_4490_ = (!crate::leanh::lean_is_exclusive(v_mctx_4459_)) as u8;
                if v_isSharedCheck_4490_ == 0 {
                    v___x_4478_ = v_mctx_4459_;
                    v_isShared_4479_ = v_isSharedCheck_4490_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_dAssignment_4476_);
                    crate::leanh::lean_inc(v_eAssignment_4475_);
                    crate::leanh::lean_inc(v_lAssignment_4474_);
                    crate::leanh::lean_inc(v_userNames_4473_);
                    crate::leanh::lean_inc(v_decls_4472_);
                    crate::leanh::lean_inc(v_lDecls_4471_);
                    crate::leanh::lean_inc(v_mvarCounter_4470_);
                    crate::leanh::lean_inc(v_lmvarCounter_4469_);
                    crate::leanh::lean_inc(v_levelAssignDepth_4468_);
                    crate::leanh::lean_inc(v_depth_4467_);
                    crate::leanh::lean_dec(v_mctx_4459_);
                    v___x_4478_ = crate::leanh::lean_box(0);
                    v_isShared_4479_ = v_isSharedCheck_4490_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4480_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPure_spec__2_spec__3___redArg(v_eAssignment_4475_, v_mvarId_4454_, v_val_4455_);
                if v_isShared_4479_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4478_, 8, v___x_4480_);
                    v___x_4482_ = v___x_4478_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4489_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4489_, 0, v_depth_4467_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4489_,
                        1,
                        v_levelAssignDepth_4468_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4489_, 2, v_lmvarCounter_4469_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4489_, 3, v_mvarCounter_4470_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4489_, 4, v_lDecls_4471_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4489_, 5, v_decls_4472_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4489_, 6, v_userNames_4473_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4489_, 7, v_lAssignment_4474_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4489_, 8, v___x_4480_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4489_, 9, v_dAssignment_4476_);
                    v___x_4482_ = v_reuseFailAlloc_4489_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4466_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4465_, 0, v___x_4482_);
                    v___x_4484_ = v___x_4465_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4488_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4488_, 0, v___x_4482_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4488_, 1, v_cache_4460_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4488_,
                        2,
                        v_zetaDeltaFVarIds_4461_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4488_, 3, v_postponed_4462_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4488_, 4, v_diag_4463_);
                    v___x_4484_ = v_reuseFailAlloc_4488_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4485_ = lean_st_ref_set(v___y_4456_, v___x_4484_);
                v___x_4486_ = crate::leanh::lean_box(0);
                v___x_4487_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4487_, 0, v___x_4486_);
                return v___x_4487_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_applyRflAndAndIntro_spec__0___redArg___boxed(
    mut v_mvarId_4492_: *mut crate::leanh::LeanObject,
    mut v_val_4493_: *mut crate::leanh::LeanObject,
    mut v___y_4494_: *mut crate::leanh::LeanObject,
    mut v___y_4495_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4496_ = l_Lean_MVarId_assign___at___00Lean_MVarId_applyRflAndAndIntro_spec__0___redArg(
        v_mvarId_4492_,
        v_val_4493_,
        v___y_4494_,
    );
    crate::leanh::lean_dec(v___y_4494_);
    return v_res_4496_;
}
pub unsafe fn _init_l_Lean_MVarId_applyRflAndAndIntro___closed__5() -> *mut crate::leanh::LeanObject
{
    let mut v___x_4506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4506_ = crate::leanh::lean_box(0);
    v___x_4507_ = l_Lean_MVarId_applyRflAndAndIntro___closed__4;
    v___x_4508_ = l_Lean_mkConst(v___x_4507_, v___x_4506_);
    return v___x_4508_;
}
pub unsafe fn _init_l_Lean_MVarId_applyRflAndAndIntro___closed__7() -> *mut crate::leanh::LeanObject
{
    let mut v___x_4512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4512_ = crate::leanh::lean_box(0);
    v___x_4513_ = l_Lean_MVarId_applyRflAndAndIntro___closed__6;
    v___x_4514_ = l_Lean_mkConst(v___x_4513_, v___x_4512_);
    return v___x_4514_;
}
pub unsafe fn _init_l_Lean_MVarId_applyRflAndAndIntro___closed__12() -> *mut crate::leanh::LeanObject
{
    let mut v___x_4524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4524_ = l_Lean_MVarId_applyRflAndAndIntro___closed__9;
    v___x_4525_ = l_Lean_MVarId_applyRflAndAndIntro___closed__11;
    v___x_4526_ = l_Lean_Name_append(v___x_4525_, v___x_4524_);
    return v___x_4526_;
}
pub unsafe fn _init_l_Lean_MVarId_applyRflAndAndIntro___closed__14() -> *mut crate::leanh::LeanObject
{
    let mut v___x_4528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4528_ = l_Lean_MVarId_applyRflAndAndIntro___closed__13;
    v___x_4529_ = l_Lean_stringToMessageData(v___x_4528_);
    return v___x_4529_;
}
pub unsafe fn l_Lean_MVarId_applyRflAndAndIntro(
    mut v_mvar_4530_: *mut crate::leanh::LeanObject,
    mut v_a_4531_: *mut crate::leanh::LeanObject,
    mut v_a_4532_: *mut crate::leanh::LeanObject,
    mut v_a_4533_: *mut crate::leanh::LeanObject,
    mut v_a_4534_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4543_: u8 = 0;
    let mut v___x_4544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4546_: u8 = 0;
    let mut v___x_4547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4552_: u8 = 0;
    let mut v___x_4553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4570_: u8 = 0;
    let mut v___x_4572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4574_: u8 = 0;
    let mut v_a_4575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4578_: u8 = 0;
    let mut v___x_4580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4582_: u8 = 0;
    let mut v___x_4583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_4588_: u8 = 0;
    let mut v_inheritedTraceOptions_4589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4592_: u8 = 0;
    let mut v___x_4593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4606_: u8 = 0;
    let mut v___x_4608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4610_: u8 = 0;
    let mut v_a_4611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4614_: u8 = 0;
    let mut v___x_4616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4618_: u8 = 0;
    let mut v___x_4619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_mvar_4530_);
                v___x_4619_ =
                    l_Lean_MVarId_getType(v_mvar_4530_, v_a_4531_, v_a_4532_, v_a_4533_, v_a_4534_);
                if crate::leanh::lean_obj_tag(v___x_4619_) == 0 {
                    v_a_4620_ = crate::leanh::lean_ctor_get(v___x_4619_, 0);
                    crate::leanh::lean_inc(v_a_4620_);
                    crate::leanh::lean_dec_ref_known(v___x_4619_, 1);
                    v___x_4621_ =
                        l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_4620_, v_a_4532_);
                    v___y_4598_ = v___x_4621_;
                    state = 7;
                    continue;
                } else {
                    v___y_4598_ = v___x_4619_;
                    state = 7;
                    continue;
                }
            }
            1 => {
                v___x_4542_ = l_Lean_MVarId_applyRflAndAndIntro___closed__1;
                v___x_4543_ = l_Lean_Expr_isAppOf(v___y_4537_, v___x_4542_);
                if v___x_4543_ == 0 {
                    v___x_4544_ = l_Lean_MVarId_applyRflAndAndIntro___closed__3;
                    v___x_4545_ = crate::leanh::lean_unsigned_to_nat(2);
                    v___x_4546_ = l_Lean_Expr_isAppOfArity(v___y_4537_, v___x_4544_, v___x_4545_);
                    if v___x_4546_ == 0 {
                        crate::leanh::lean_inc(v_mvar_4530_);
                        v___x_4547_ =
                            l_Lean_MVarId_setType___redArg(v_mvar_4530_, v___y_4537_, v___y_4539_);
                        if crate::leanh::lean_obj_tag(v___x_4547_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_4547_, 1);
                            v___x_4548_ = l_Lean_MVarId_applyRfl(
                                v_mvar_4530_,
                                v___y_4538_,
                                v___y_4539_,
                                v___y_4540_,
                                v___y_4541_,
                            );
                            return v___x_4548_;
                        } else {
                            crate::leanh::lean_dec(v_mvar_4530_);
                            return v___x_4547_;
                        }
                    } else {
                        v___x_4549_ = l_Lean_Expr_appFn_x21(v___y_4537_);
                        v___x_4550_ = l_Lean_Expr_appArg_x21(v___x_4549_);
                        crate::leanh::lean_dec_ref(v___x_4549_);
                        crate::leanh::lean_inc_ref(v___x_4550_);
                        v___x_4551_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4551_, 0, v___x_4550_);
                        v___x_4552_ = 0;
                        v___x_4553_ = crate::leanh::lean_box(0);
                        v___x_4554_ = l_Lean_Meta_mkFreshExprMVar(
                            v___x_4551_,
                            v___x_4552_,
                            v___x_4553_,
                            v___y_4538_,
                            v___y_4539_,
                            v___y_4540_,
                            v___y_4541_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4554_) == 0 {
                            v_a_4555_ = crate::leanh::lean_ctor_get(v___x_4554_, 0);
                            crate::leanh::lean_inc(v_a_4555_);
                            crate::leanh::lean_dec_ref_known(v___x_4554_, 1);
                            v___x_4556_ = l_Lean_Expr_appArg_x21(v___y_4537_);
                            crate::leanh::lean_dec_ref(v___y_4537_);
                            crate::leanh::lean_inc_ref(v___x_4556_);
                            v___x_4557_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4557_, 0, v___x_4556_);
                            v___x_4558_ = l_Lean_Meta_mkFreshExprMVar(
                                v___x_4557_,
                                v___x_4552_,
                                v___x_4553_,
                                v___y_4538_,
                                v___y_4539_,
                                v___y_4540_,
                                v___y_4541_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_4558_) == 0 {
                                v_a_4559_ = crate::leanh::lean_ctor_get(v___x_4558_, 0);
                                crate::leanh::lean_inc(v_a_4559_);
                                crate::leanh::lean_dec_ref_known(v___x_4558_, 1);
                                v___x_4560_ = l_Lean_Expr_mvarId_x21(v_a_4555_);
                                v___x_4561_ = l_Lean_MVarId_applyRflAndAndIntro(
                                    v___x_4560_,
                                    v___y_4538_,
                                    v___y_4539_,
                                    v___y_4540_,
                                    v___y_4541_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_4561_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_4561_, 1);
                                    v___x_4562_ = l_Lean_Expr_mvarId_x21(v_a_4559_);
                                    v___x_4563_ = l_Lean_MVarId_applyRflAndAndIntro(
                                        v___x_4562_,
                                        v___y_4538_,
                                        v___y_4539_,
                                        v___y_4540_,
                                        v___y_4541_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_4563_) == 0 {
                                        crate::leanh::lean_dec_ref_known(v___x_4563_, 1);
                                        v___x_4564_ = crate::leanh::lean_obj_once(
                                            core::ptr::addr_of_mut!(
                                                l_Lean_MVarId_applyRflAndAndIntro___closed__5
                                            ),
                                            core::ptr::addr_of_mut!(
                                                l_Lean_MVarId_applyRflAndAndIntro___closed__5_once
                                            ),
                                            _init_l_Lean_MVarId_applyRflAndAndIntro___closed__5,
                                        );
                                        v___x_4565_ = l_Lean_mkApp4(
                                            v___x_4564_,
                                            v___x_4550_,
                                            v___x_4556_,
                                            v_a_4555_,
                                            v_a_4559_,
                                        );
                                        v___x_4566_ = l_Lean_MVarId_assign___at___00Lean_MVarId_applyRflAndAndIntro_spec__0___redArg(v_mvar_4530_, v___x_4565_, v___y_4539_);
                                        return v___x_4566_;
                                    } else {
                                        crate::leanh::lean_dec(v_a_4559_);
                                        crate::leanh::lean_dec_ref(v___x_4556_);
                                        crate::leanh::lean_dec(v_a_4555_);
                                        crate::leanh::lean_dec_ref(v___x_4550_);
                                        crate::leanh::lean_dec(v_mvar_4530_);
                                        return v___x_4563_;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_4559_);
                                    crate::leanh::lean_dec_ref(v___x_4556_);
                                    crate::leanh::lean_dec(v_a_4555_);
                                    crate::leanh::lean_dec_ref(v___x_4550_);
                                    crate::leanh::lean_dec(v_mvar_4530_);
                                    return v___x_4561_;
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v___x_4556_);
                                crate::leanh::lean_dec(v_a_4555_);
                                crate::leanh::lean_dec_ref(v___x_4550_);
                                crate::leanh::lean_dec(v_mvar_4530_);
                                v_a_4567_ = crate::leanh::lean_ctor_get(v___x_4558_, 0);
                                v_isSharedCheck_4574_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4558_)) as u8;
                                if v_isSharedCheck_4574_ == 0 {
                                    v___x_4569_ = v___x_4558_;
                                    v_isShared_4570_ = v_isSharedCheck_4574_;
                                    state = 2;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4567_);
                                    crate::leanh::lean_dec(v___x_4558_);
                                    v___x_4569_ = crate::leanh::lean_box(0);
                                    v_isShared_4570_ = v_isSharedCheck_4574_;
                                    state = 2;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_4550_);
                            crate::leanh::lean_dec_ref(v___y_4537_);
                            crate::leanh::lean_dec(v_mvar_4530_);
                            v_a_4575_ = crate::leanh::lean_ctor_get(v___x_4554_, 0);
                            v_isSharedCheck_4582_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4554_)) as u8;
                            if v_isSharedCheck_4582_ == 0 {
                                v___x_4577_ = v___x_4554_;
                                v_isShared_4578_ = v_isSharedCheck_4582_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4575_);
                                crate::leanh::lean_dec(v___x_4554_);
                                v___x_4577_ = crate::leanh::lean_box(0);
                                v_isShared_4578_ = v_isSharedCheck_4582_;
                                state = 4;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_4537_);
                    v___x_4583_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_MVarId_applyRflAndAndIntro___closed__7),
                        core::ptr::addr_of_mut!(l_Lean_MVarId_applyRflAndAndIntro___closed__7_once),
                        _init_l_Lean_MVarId_applyRflAndAndIntro___closed__7,
                    );
                    v___x_4584_ = l_Lean_MVarId_assign___at___00Lean_MVarId_applyRflAndAndIntro_spec__0___redArg(v_mvar_4530_, v___x_4583_, v___y_4539_);
                    return v___x_4584_;
                }
            }
            2 => {
                if v_isShared_4570_ == 0 {
                    v___x_4572_ = v___x_4569_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4573_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4573_, 0, v_a_4567_);
                    v___x_4572_ = v_reuseFailAlloc_4573_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4572_;
            }
            4 => {
                if v_isShared_4578_ == 0 {
                    v___x_4580_ = v___x_4577_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4581_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4581_, 0, v_a_4575_);
                    v___x_4580_ = v_reuseFailAlloc_4581_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4580_;
            }
            6 => {
                v_options_4587_ = crate::leanh::lean_ctor_get(v_a_4533_, 2);
                v_hasTrace_4588_ = crate::leanh::lean_ctor_get_uint8(
                    v_options_4587_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                if v_hasTrace_4588_ == 0 {
                    v___y_4537_ = v_a_4586_;
                    v___y_4538_ = v_a_4531_;
                    v___y_4539_ = v_a_4532_;
                    v___y_4540_ = v_a_4533_;
                    v___y_4541_ = v_a_4534_;
                    state = 1;
                    continue;
                } else {
                    v_inheritedTraceOptions_4589_ = crate::leanh::lean_ctor_get(v_a_4533_, 13);
                    v___x_4590_ = l_Lean_MVarId_applyRflAndAndIntro___closed__9;
                    v___x_4591_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_MVarId_applyRflAndAndIntro___closed__12),
                        core::ptr::addr_of_mut!(
                            l_Lean_MVarId_applyRflAndAndIntro___closed__12_once
                        ),
                        _init_l_Lean_MVarId_applyRflAndAndIntro___closed__12,
                    );
                    v___x_4592_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_4589_,
                        v_options_4587_,
                        v___x_4591_,
                    );
                    if v___x_4592_ == 0 {
                        v___y_4537_ = v_a_4586_;
                        v___y_4538_ = v_a_4531_;
                        v___y_4539_ = v_a_4532_;
                        v___y_4540_ = v_a_4533_;
                        v___y_4541_ = v_a_4534_;
                        state = 1;
                        continue;
                    } else {
                        v___x_4593_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_MVarId_applyRflAndAndIntro___closed__14),
                            core::ptr::addr_of_mut!(
                                l_Lean_MVarId_applyRflAndAndIntro___closed__14_once
                            ),
                            _init_l_Lean_MVarId_applyRflAndAndIntro___closed__14,
                        );
                        crate::leanh::lean_inc_ref(v_a_4586_);
                        v___x_4594_ = l_Lean_MessageData_ofExpr(v_a_4586_);
                        v___x_4595_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4595_, 0, v___x_4593_);
                        crate::leanh::lean_ctor_set(v___x_4595_, 1, v___x_4594_);
                        v___x_4596_ =
                            l_Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1(
                                v___x_4590_,
                                v___x_4595_,
                                v_a_4531_,
                                v_a_4532_,
                                v_a_4533_,
                                v_a_4534_,
                            );
                        if crate::leanh::lean_obj_tag(v___x_4596_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_4596_, 1);
                            v___y_4537_ = v_a_4586_;
                            v___y_4538_ = v_a_4531_;
                            v___y_4539_ = v_a_4532_;
                            v___y_4540_ = v_a_4533_;
                            v___y_4541_ = v_a_4534_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_a_4586_);
                            crate::leanh::lean_dec(v_mvar_4530_);
                            return v___x_4596_;
                        }
                    }
                }
            }
            7 => {
                if crate::leanh::lean_obj_tag(v___y_4598_) == 0 {
                    v_a_4599_ = crate::leanh::lean_ctor_get(v___y_4598_, 0);
                    crate::leanh::lean_inc_n(v_a_4599_, 2);
                    crate::leanh::lean_dec_ref_known(v___y_4598_, 1);
                    v___x_4600_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_extractPureProp(v_a_4599_, v_a_4531_, v_a_4532_, v_a_4533_, v_a_4534_);
                    if crate::leanh::lean_obj_tag(v___x_4600_) == 0 {
                        v_a_4601_ = crate::leanh::lean_ctor_get(v___x_4600_, 0);
                        crate::leanh::lean_inc(v_a_4601_);
                        crate::leanh::lean_dec_ref_known(v___x_4600_, 1);
                        if crate::leanh::lean_obj_tag(v_a_4601_) == 0 {
                            v_a_4586_ = v_a_4599_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_a_4599_);
                            v_val_4602_ = crate::leanh::lean_ctor_get(v_a_4601_, 0);
                            crate::leanh::lean_inc(v_val_4602_);
                            crate::leanh::lean_dec_ref_known(v_a_4601_, 1);
                            v_a_4586_ = v_val_4602_;
                            state = 6;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_4599_);
                        crate::leanh::lean_dec(v_mvar_4530_);
                        v_a_4603_ = crate::leanh::lean_ctor_get(v___x_4600_, 0);
                        v_isSharedCheck_4610_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4600_)) as u8;
                        if v_isSharedCheck_4610_ == 0 {
                            v___x_4605_ = v___x_4600_;
                            v_isShared_4606_ = v_isSharedCheck_4610_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4603_);
                            crate::leanh::lean_dec(v___x_4600_);
                            v___x_4605_ = crate::leanh::lean_box(0);
                            v_isShared_4606_ = v_isSharedCheck_4610_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_mvar_4530_);
                    v_a_4611_ = crate::leanh::lean_ctor_get(v___y_4598_, 0);
                    v_isSharedCheck_4618_ = (!crate::leanh::lean_is_exclusive(v___y_4598_)) as u8;
                    if v_isSharedCheck_4618_ == 0 {
                        v___x_4613_ = v___y_4598_;
                        v_isShared_4614_ = v_isSharedCheck_4618_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4611_);
                        crate::leanh::lean_dec(v___y_4598_);
                        v___x_4613_ = crate::leanh::lean_box(0);
                        v_isShared_4614_ = v_isSharedCheck_4618_;
                        state = 10;
                        continue;
                    }
                }
            }
            8 => {
                if v_isShared_4606_ == 0 {
                    v___x_4608_ = v___x_4605_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4609_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4609_, 0, v_a_4603_);
                    v___x_4608_ = v_reuseFailAlloc_4609_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4608_;
            }
            10 => {
                if v_isShared_4614_ == 0 {
                    v___x_4616_ = v___x_4613_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4617_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4617_, 0, v_a_4611_);
                    v___x_4616_ = v_reuseFailAlloc_4617_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4616_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_applyRflAndAndIntro___boxed(
    mut v_mvar_4622_: *mut crate::leanh::LeanObject,
    mut v_a_4623_: *mut crate::leanh::LeanObject,
    mut v_a_4624_: *mut crate::leanh::LeanObject,
    mut v_a_4625_: *mut crate::leanh::LeanObject,
    mut v_a_4626_: *mut crate::leanh::LeanObject,
    mut v_a_4627_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4628_ =
        l_Lean_MVarId_applyRflAndAndIntro(v_mvar_4622_, v_a_4623_, v_a_4624_, v_a_4625_, v_a_4626_);
    crate::leanh::lean_dec(v_a_4626_);
    crate::leanh::lean_dec_ref(v_a_4625_);
    crate::leanh::lean_dec(v_a_4624_);
    crate::leanh::lean_dec_ref(v_a_4623_);
    return v_res_4628_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_applyRflAndAndIntro_spec__0(
    mut v_mvarId_4629_: *mut crate::leanh::LeanObject,
    mut v_val_4630_: *mut crate::leanh::LeanObject,
    mut v___y_4631_: *mut crate::leanh::LeanObject,
    mut v___y_4632_: *mut crate::leanh::LeanObject,
    mut v___y_4633_: *mut crate::leanh::LeanObject,
    mut v___y_4634_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4636_ = l_Lean_MVarId_assign___at___00Lean_MVarId_applyRflAndAndIntro_spec__0___redArg(
        v_mvarId_4629_,
        v_val_4630_,
        v___y_4632_,
    );
    return v___x_4636_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_applyRflAndAndIntro_spec__0___boxed(
    mut v_mvarId_4637_: *mut crate::leanh::LeanObject,
    mut v_val_4638_: *mut crate::leanh::LeanObject,
    mut v___y_4639_: *mut crate::leanh::LeanObject,
    mut v___y_4640_: *mut crate::leanh::LeanObject,
    mut v___y_4641_: *mut crate::leanh::LeanObject,
    mut v___y_4642_: *mut crate::leanh::LeanObject,
    mut v___y_4643_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4644_ = l_Lean_MVarId_assign___at___00Lean_MVarId_applyRflAndAndIntro_spec__0(
        v_mvarId_4637_,
        v_val_4638_,
        v___y_4639_,
        v___y_4640_,
        v___y_4641_,
        v___y_4642_,
    );
    crate::leanh::lean_dec(v___y_4642_);
    crate::leanh::lean_dec_ref(v___y_4641_);
    crate::leanh::lean_dec(v___y_4640_);
    crate::leanh::lean_dec_ref(v___y_4639_);
    return v_res_4644_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro_spec__1___redArg(
    mut v_goal_4645_: *mut crate::leanh::LeanObject,
    mut v_k_4646_: *mut crate::leanh::LeanObject,
    mut v___y_4647_: *mut crate::leanh::LeanObject,
    mut v___y_4648_: *mut crate::leanh::LeanObject,
    mut v___y_4649_: *mut crate::leanh::LeanObject,
    mut v___y_4650_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4653_: u8 = 0;
    let mut v___x_4654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_4657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_00_u03c3s_4658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hyps_4659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_4660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4673_: u8 = 0;
    let mut v_val_4674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4677_: u8 = 0;
    let mut v_fst_4678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4682_: u8 = 0;
    let mut v___x_4683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_prf_4685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4695_: u8 = 0;
    let mut v_isSharedCheck_4696_: u8 = 0;
    let mut v_isSharedCheck_4697_: u8 = 0;
    let mut v_unused_4698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4702_: u8 = 0;
    let mut v___x_4704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4706_: u8 = 0;
    let mut v_a_4707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4710_: u8 = 0;
    let mut v___x_4712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4714_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4652_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__1_once), _init_l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__10___closed__1);
                v___x_4653_ = 0;
                v___x_4654_ = crate::leanh::lean_box(0);
                v___x_4655_ = l_Lean_Meta_mkFreshExprMVar(
                    v___x_4652_,
                    v___x_4653_,
                    v___x_4654_,
                    v___y_4647_,
                    v___y_4648_,
                    v___y_4649_,
                    v___y_4650_,
                );
                if crate::leanh::lean_obj_tag(v___x_4655_) == 0 {
                    v_a_4656_ = crate::leanh::lean_ctor_get(v___x_4655_, 0);
                    crate::leanh::lean_inc_n(v_a_4656_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_4655_, 1);
                    v_u_4657_ = crate::leanh::lean_ctor_get(v_goal_4645_, 0);
                    crate::leanh::lean_inc(v_u_4657_);
                    v_00_u03c3s_4658_ = crate::leanh::lean_ctor_get(v_goal_4645_, 1);
                    crate::leanh::lean_inc_ref_n(v_00_u03c3s_4658_, 2);
                    v_hyps_4659_ = crate::leanh::lean_ctor_get(v_goal_4645_, 2);
                    crate::leanh::lean_inc_ref(v_hyps_4659_);
                    v_target_4660_ = crate::leanh::lean_ctor_get(v_goal_4645_, 3);
                    crate::leanh::lean_inc_ref_n(v_target_4660_, 2);
                    crate::leanh::lean_dec_ref(v_goal_4645_);
                    v___x_4661_ =
                        l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___redArg___lam__9___closed__5;
                    v___x_4662_ = crate::leanh::lean_box(0);
                    v___x_4663_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4663_, 0, v_u_4657_);
                    crate::leanh::lean_ctor_set(v___x_4663_, 1, v___x_4662_);
                    crate::leanh::lean_inc_ref(v___x_4663_);
                    v___x_4664_ = l_Lean_mkConst(v___x_4661_, v___x_4663_);
                    v___x_4665_ =
                        l_Lean_mkApp3(v___x_4664_, v_00_u03c3s_4658_, v_target_4660_, v_a_4656_);
                    v___x_4666_ = crate::leanh::lean_box(0);
                    v___x_4667_ = l_Lean_Meta_synthInstance(
                        v___x_4665_,
                        v___x_4666_,
                        v___y_4647_,
                        v___y_4648_,
                        v___y_4649_,
                        v___y_4650_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4667_) == 0 {
                        v_a_4668_ = crate::leanh::lean_ctor_get(v___x_4667_, 0);
                        crate::leanh::lean_inc(v_a_4668_);
                        crate::leanh::lean_dec_ref_known(v___x_4667_, 1);
                        crate::leanh::lean_inc(v___y_4650_);
                        crate::leanh::lean_inc_ref(v___y_4649_);
                        crate::leanh::lean_inc(v___y_4648_);
                        crate::leanh::lean_inc_ref(v___y_4647_);
                        crate::leanh::lean_inc(v_a_4656_);
                        v___x_4669_ = crate::leanh::lean_apply_6(
                            v_k_4646_,
                            v_a_4656_,
                            v___y_4647_,
                            v___y_4648_,
                            v___y_4649_,
                            v___y_4650_,
                            crate::leanh::lean_box(0),
                        );
                        if crate::leanh::lean_obj_tag(v___x_4669_) == 0 {
                            v_a_4670_ = crate::leanh::lean_ctor_get(v___x_4669_, 0);
                            crate::leanh::lean_inc(v_a_4670_);
                            if crate::leanh::lean_obj_tag(v_a_4670_) == 0 {
                                crate::leanh::lean_dec(v_a_4668_);
                                crate::leanh::lean_dec_ref_known(v___x_4663_, 2);
                                crate::leanh::lean_dec_ref(v_target_4660_);
                                crate::leanh::lean_dec_ref(v_hyps_4659_);
                                crate::leanh::lean_dec_ref(v_00_u03c3s_4658_);
                                crate::leanh::lean_dec(v_a_4656_);
                                return v___x_4669_;
                            } else {
                                v_isSharedCheck_4697_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4669_)) as u8;
                                if v_isSharedCheck_4697_ == 0 {
                                    v_unused_4698_ = crate::leanh::lean_ctor_get(v___x_4669_, 0);
                                    crate::leanh::lean_dec(v_unused_4698_);
                                    v___x_4672_ = v___x_4669_;
                                    v_isShared_4673_ = v_isSharedCheck_4697_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v___x_4669_);
                                    v___x_4672_ = crate::leanh::lean_box(0);
                                    v_isShared_4673_ = v_isSharedCheck_4697_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_4668_);
                            crate::leanh::lean_dec_ref_known(v___x_4663_, 2);
                            crate::leanh::lean_dec_ref(v_target_4660_);
                            crate::leanh::lean_dec_ref(v_hyps_4659_);
                            crate::leanh::lean_dec_ref(v_00_u03c3s_4658_);
                            crate::leanh::lean_dec(v_a_4656_);
                            return v___x_4669_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v___x_4663_, 2);
                        crate::leanh::lean_dec_ref(v_target_4660_);
                        crate::leanh::lean_dec_ref(v_hyps_4659_);
                        crate::leanh::lean_dec_ref(v_00_u03c3s_4658_);
                        crate::leanh::lean_dec(v_a_4656_);
                        crate::leanh::lean_dec_ref(v_k_4646_);
                        v_a_4699_ = crate::leanh::lean_ctor_get(v___x_4667_, 0);
                        v_isSharedCheck_4706_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4667_)) as u8;
                        if v_isSharedCheck_4706_ == 0 {
                            v___x_4701_ = v___x_4667_;
                            v_isShared_4702_ = v_isSharedCheck_4706_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4699_);
                            crate::leanh::lean_dec(v___x_4667_);
                            v___x_4701_ = crate::leanh::lean_box(0);
                            v_isShared_4702_ = v_isSharedCheck_4706_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_k_4646_);
                    crate::leanh::lean_dec_ref(v_goal_4645_);
                    v_a_4707_ = crate::leanh::lean_ctor_get(v___x_4655_, 0);
                    v_isSharedCheck_4714_ = (!crate::leanh::lean_is_exclusive(v___x_4655_)) as u8;
                    if v_isSharedCheck_4714_ == 0 {
                        v___x_4709_ = v___x_4655_;
                        v_isShared_4710_ = v_isSharedCheck_4714_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4707_);
                        crate::leanh::lean_dec(v___x_4655_);
                        v___x_4709_ = crate::leanh::lean_box(0);
                        v_isShared_4710_ = v_isSharedCheck_4714_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v_val_4674_ = crate::leanh::lean_ctor_get(v_a_4670_, 0);
                v_isSharedCheck_4696_ = (!crate::leanh::lean_is_exclusive(v_a_4670_)) as u8;
                if v_isSharedCheck_4696_ == 0 {
                    v___x_4676_ = v_a_4670_;
                    v_isShared_4677_ = v_isSharedCheck_4696_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_val_4674_);
                    crate::leanh::lean_dec(v_a_4670_);
                    v___x_4676_ = crate::leanh::lean_box(0);
                    v_isShared_4677_ = v_isSharedCheck_4696_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_fst_4678_ = crate::leanh::lean_ctor_get(v_val_4674_, 0);
                v_snd_4679_ = crate::leanh::lean_ctor_get(v_val_4674_, 1);
                v_isSharedCheck_4695_ = (!crate::leanh::lean_is_exclusive(v_val_4674_)) as u8;
                if v_isSharedCheck_4695_ == 0 {
                    v___x_4681_ = v_val_4674_;
                    v_isShared_4682_ = v_isSharedCheck_4695_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_4679_);
                    crate::leanh::lean_inc(v_fst_4678_);
                    crate::leanh::lean_dec(v_val_4674_);
                    v___x_4681_ = crate::leanh::lean_box(0);
                    v_isShared_4682_ = v_isSharedCheck_4695_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4683_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro_spec__0___redArg___closed__0;
                v___x_4684_ = l_Lean_mkConst(v___x_4683_, v___x_4663_);
                v_prf_4685_ = l_Lean_mkApp6(
                    v___x_4684_,
                    v_00_u03c3s_4658_,
                    v_hyps_4659_,
                    v_target_4660_,
                    v_a_4656_,
                    v_a_4668_,
                    v_snd_4679_,
                );
                if v_isShared_4682_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4681_, 1, v_prf_4685_);
                    v___x_4687_ = v___x_4681_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4694_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4694_, 0, v_fst_4678_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4694_, 1, v_prf_4685_);
                    v___x_4687_ = v_reuseFailAlloc_4694_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4677_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4676_, 0, v___x_4687_);
                    v___x_4689_ = v___x_4676_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4693_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4693_, 0, v___x_4687_);
                    v___x_4689_ = v_reuseFailAlloc_4693_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_4673_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4672_, 0, v___x_4689_);
                    v___x_4691_ = v___x_4672_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4692_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4692_, 0, v___x_4689_);
                    v___x_4691_ = v_reuseFailAlloc_4692_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4691_;
            }
            7 => {
                if v_isShared_4702_ == 0 {
                    v___x_4704_ = v___x_4701_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4705_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4705_, 0, v_a_4699_);
                    v___x_4704_ = v_reuseFailAlloc_4705_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4704_;
            }
            9 => {
                if v_isShared_4710_ == 0 {
                    v___x_4712_ = v___x_4709_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4713_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4713_, 0, v_a_4707_);
                    v___x_4712_ = v_reuseFailAlloc_4713_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4712_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro_spec__1___redArg___boxed(
    mut v_goal_4715_: *mut crate::leanh::LeanObject,
    mut v_k_4716_: *mut crate::leanh::LeanObject,
    mut v___y_4717_: *mut crate::leanh::LeanObject,
    mut v___y_4718_: *mut crate::leanh::LeanObject,
    mut v___y_4719_: *mut crate::leanh::LeanObject,
    mut v___y_4720_: *mut crate::leanh::LeanObject,
    mut v___y_4721_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4722_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro_spec__1___redArg(v_goal_4715_, v_k_4716_, v___y_4717_, v___y_4718_, v___y_4719_, v___y_4720_);
    crate::leanh::lean_dec(v___y_4720_);
    crate::leanh::lean_dec_ref(v___y_4719_);
    crate::leanh::lean_dec(v___y_4718_);
    crate::leanh::lean_dec_ref(v___y_4717_);
    return v_res_4722_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro_spec__1(
    mut v_00_u03b1_4723_: *mut crate::leanh::LeanObject,
    mut v_goal_4724_: *mut crate::leanh::LeanObject,
    mut v_k_4725_: *mut crate::leanh::LeanObject,
    mut v___y_4726_: *mut crate::leanh::LeanObject,
    mut v___y_4727_: *mut crate::leanh::LeanObject,
    mut v___y_4728_: *mut crate::leanh::LeanObject,
    mut v___y_4729_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4731_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro_spec__1___redArg(v_goal_4724_, v_k_4725_, v___y_4726_, v___y_4727_, v___y_4728_, v___y_4729_);
    return v___x_4731_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro_spec__1___boxed(
    mut v_00_u03b1_4732_: *mut crate::leanh::LeanObject,
    mut v_goal_4733_: *mut crate::leanh::LeanObject,
    mut v_k_4734_: *mut crate::leanh::LeanObject,
    mut v___y_4735_: *mut crate::leanh::LeanObject,
    mut v___y_4736_: *mut crate::leanh::LeanObject,
    mut v___y_4737_: *mut crate::leanh::LeanObject,
    mut v___y_4738_: *mut crate::leanh::LeanObject,
    mut v___y_4739_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4740_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro_spec__1(v_00_u03b1_4732_, v_goal_4733_, v_k_4734_, v___y_4735_, v___y_4736_, v___y_4737_, v___y_4738_);
    crate::leanh::lean_dec(v___y_4738_);
    crate::leanh::lean_dec_ref(v___y_4737_);
    crate::leanh::lean_dec(v___y_4736_);
    crate::leanh::lean_dec_ref(v___y_4735_);
    return v_res_4740_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__0(
    mut v_cls_4741_: *mut crate::leanh::LeanObject,
    mut v___y_4742_: *mut crate::leanh::LeanObject,
    mut v___y_4743_: *mut crate::leanh::LeanObject,
    mut v___y_4744_: *mut crate::leanh::LeanObject,
    mut v___y_4745_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_4747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_4748_: u8 = 0;
    v_options_4747_ = crate::leanh::lean_ctor_get(v___y_4744_, 2);
    v_hasTrace_4748_ = crate::leanh::lean_ctor_get_uint8(
        v_options_4747_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
    );
    if v_hasTrace_4748_ == 0 {
        let mut v___x_4749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_cls_4741_);
        v___x_4749_ = crate::leanh::lean_box((v_hasTrace_4748_) as usize);
        v___x_4750_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4750_, 0, v___x_4749_);
        v___x_4751_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4751_, 0, v___x_4750_);
        return v___x_4751_;
    } else {
        let mut v_inheritedTraceOptions_4752_: *mut crate::leanh::LeanObject =
            core::ptr::null_mut();
        let mut v___x_4753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4755_: u8 = 0;
        let mut v___x_4756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_inheritedTraceOptions_4752_ = crate::leanh::lean_ctor_get(v___y_4744_, 13);
        v___x_4753_ = l_Lean_MVarId_applyRflAndAndIntro___closed__11;
        v___x_4754_ = l_Lean_Name_append(v___x_4753_, v_cls_4741_);
        v___x_4755_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
            v_inheritedTraceOptions_4752_,
            v_options_4747_,
            v___x_4754_,
        );
        crate::leanh::lean_dec(v___x_4754_);
        v___x_4756_ = crate::leanh::lean_box((v___x_4755_) as usize);
        v___x_4757_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4757_, 0, v___x_4756_);
        v___x_4758_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4758_, 0, v___x_4757_);
        return v___x_4758_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__0___boxed(
    mut v_cls_4759_: *mut crate::leanh::LeanObject,
    mut v___y_4760_: *mut crate::leanh::LeanObject,
    mut v___y_4761_: *mut crate::leanh::LeanObject,
    mut v___y_4762_: *mut crate::leanh::LeanObject,
    mut v___y_4763_: *mut crate::leanh::LeanObject,
    mut v___y_4764_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4765_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__0(
        v_cls_4759_,
        v___y_4760_,
        v___y_4761_,
        v___y_4762_,
        v___y_4763_,
    );
    crate::leanh::lean_dec(v___y_4763_);
    crate::leanh::lean_dec_ref(v___y_4762_);
    crate::leanh::lean_dec(v___y_4761_);
    crate::leanh::lean_dec_ref(v___y_4760_);
    return v_res_4765_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro_spec__0(
    mut v_cls_4768_: *mut crate::leanh::LeanObject,
    mut v_msg_4769_: *mut crate::leanh::LeanObject,
    mut v___y_4770_: *mut crate::leanh::LeanObject,
    mut v___y_4771_: *mut crate::leanh::LeanObject,
    mut v___y_4772_: *mut crate::leanh::LeanObject,
    mut v___y_4773_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_4775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4780_: u8 = 0;
    let mut v___x_4781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_4787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4793_: u8 = 0;
    let mut v_tid_4794_: u64 = 0;
    let mut v_traces_4795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4798_: u8 = 0;
    let mut v___x_4799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4800_: f64 = 0.0;
    let mut v___x_4801_: u8 = 0;
    let mut v___x_4802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4819_: u8 = 0;
    let mut v_isSharedCheck_4820_: u8 = 0;
    let mut v_isSharedCheck_4821_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4775_ = crate::leanh::lean_ctor_get(v___y_4772_, 5);
                v___x_4776_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1_spec__1(v_msg_4769_, v___y_4770_, v___y_4771_, v___y_4772_, v___y_4773_);
                v_a_4777_ = crate::leanh::lean_ctor_get(v___x_4776_, 0);
                v_isSharedCheck_4821_ = (!crate::leanh::lean_is_exclusive(v___x_4776_)) as u8;
                if v_isSharedCheck_4821_ == 0 {
                    v___x_4779_ = v___x_4776_;
                    v_isShared_4780_ = v_isSharedCheck_4821_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_4777_);
                    crate::leanh::lean_dec(v___x_4776_);
                    v___x_4779_ = crate::leanh::lean_box(0);
                    v_isShared_4780_ = v_isSharedCheck_4821_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4781_ = lean_st_ref_take(v___y_4773_);
                v_traceState_4782_ = crate::leanh::lean_ctor_get(v___x_4781_, 4);
                v_env_4783_ = crate::leanh::lean_ctor_get(v___x_4781_, 0);
                v_nextMacroScope_4784_ = crate::leanh::lean_ctor_get(v___x_4781_, 1);
                v_ngen_4785_ = crate::leanh::lean_ctor_get(v___x_4781_, 2);
                v_auxDeclNGen_4786_ = crate::leanh::lean_ctor_get(v___x_4781_, 3);
                v_cache_4787_ = crate::leanh::lean_ctor_get(v___x_4781_, 5);
                v_messages_4788_ = crate::leanh::lean_ctor_get(v___x_4781_, 6);
                v_infoState_4789_ = crate::leanh::lean_ctor_get(v___x_4781_, 7);
                v_snapshotTasks_4790_ = crate::leanh::lean_ctor_get(v___x_4781_, 8);
                v_isSharedCheck_4820_ = (!crate::leanh::lean_is_exclusive(v___x_4781_)) as u8;
                if v_isSharedCheck_4820_ == 0 {
                    v___x_4792_ = v___x_4781_;
                    v_isShared_4793_ = v_isSharedCheck_4820_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_4790_);
                    crate::leanh::lean_inc(v_infoState_4789_);
                    crate::leanh::lean_inc(v_messages_4788_);
                    crate::leanh::lean_inc(v_cache_4787_);
                    crate::leanh::lean_inc(v_traceState_4782_);
                    crate::leanh::lean_inc(v_auxDeclNGen_4786_);
                    crate::leanh::lean_inc(v_ngen_4785_);
                    crate::leanh::lean_inc(v_nextMacroScope_4784_);
                    crate::leanh::lean_inc(v_env_4783_);
                    crate::leanh::lean_dec(v___x_4781_);
                    v___x_4792_ = crate::leanh::lean_box(0);
                    v_isShared_4793_ = v_isSharedCheck_4820_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_4794_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_4782_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_4795_ = crate::leanh::lean_ctor_get(v_traceState_4782_, 0);
                v_isSharedCheck_4819_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_4782_)) as u8;
                if v_isSharedCheck_4819_ == 0 {
                    v___x_4797_ = v_traceState_4782_;
                    v_isShared_4798_ = v_isSharedCheck_4819_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_4795_);
                    crate::leanh::lean_dec(v_traceState_4782_);
                    v___x_4797_ = crate::leanh::lean_box(0);
                    v_isShared_4798_ = v_isSharedCheck_4819_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4799_ = crate::leanh::lean_box(0);
                v___x_4800_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1___closed__0_once), _init_l_Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1___closed__0);
                v___x_4801_ = 0;
                v___x_4802_ =
                    l_Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1___closed__1;
                v___x_4803_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v___x_4803_, 0, v_cls_4768_);
                crate::leanh::lean_ctor_set(v___x_4803_, 1, v___x_4799_);
                crate::leanh::lean_ctor_set(v___x_4803_, 2, v___x_4802_);
                crate::leanh::lean_ctor_set_float(
                    v___x_4803_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_4800_,
                );
                crate::leanh::lean_ctor_set_float(
                    v___x_4803_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_4800_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4803_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_4801_,
                );
                v___x_4804_ =
                    l_Lean_addTrace___at___00Lean_MVarId_applyRflAndAndIntro_spec__1___closed__2;
                v___x_4805_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4805_, 0, v___x_4803_);
                crate::leanh::lean_ctor_set(v___x_4805_, 1, v_a_4777_);
                crate::leanh::lean_ctor_set(v___x_4805_, 2, v___x_4804_);
                crate::leanh::lean_inc(v_ref_4775_);
                v___x_4806_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4806_, 0, v_ref_4775_);
                crate::leanh::lean_ctor_set(v___x_4806_, 1, v___x_4805_);
                v___x_4807_ = l_Lean_PersistentArray_push___redArg(v_traces_4795_, v___x_4806_);
                if v_isShared_4798_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4797_, 0, v___x_4807_);
                    v___x_4809_ = v___x_4797_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4818_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4818_, 0, v___x_4807_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_4818_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_4794_,
                    );
                    v___x_4809_ = v_reuseFailAlloc_4818_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4793_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4792_, 4, v___x_4809_);
                    v___x_4811_ = v___x_4792_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4817_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4817_, 0, v_env_4783_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4817_, 1, v_nextMacroScope_4784_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4817_, 2, v_ngen_4785_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4817_, 3, v_auxDeclNGen_4786_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4817_, 4, v___x_4809_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4817_, 5, v_cache_4787_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4817_, 6, v_messages_4788_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4817_, 7, v_infoState_4789_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4817_, 8, v_snapshotTasks_4790_);
                    v___x_4811_ = v_reuseFailAlloc_4817_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4812_ = lean_st_ref_set(v___y_4773_, v___x_4811_);
                v___x_4813_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro_spec__0___closed__0;
                if v_isShared_4780_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4779_, 0, v___x_4813_);
                    v___x_4815_ = v___x_4779_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4816_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4816_, 0, v___x_4813_);
                    v___x_4815_ = v_reuseFailAlloc_4816_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4815_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro_spec__0___boxed(
    mut v_cls_4822_: *mut crate::leanh::LeanObject,
    mut v_msg_4823_: *mut crate::leanh::LeanObject,
    mut v___y_4824_: *mut crate::leanh::LeanObject,
    mut v___y_4825_: *mut crate::leanh::LeanObject,
    mut v___y_4826_: *mut crate::leanh::LeanObject,
    mut v___y_4827_: *mut crate::leanh::LeanObject,
    mut v___y_4828_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4829_ =
        l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro_spec__0(
            v_cls_4822_,
            v_msg_4823_,
            v___y_4824_,
            v___y_4825_,
            v___y_4826_,
            v___y_4827_,
        );
    crate::leanh::lean_dec(v___y_4827_);
    crate::leanh::lean_dec_ref(v___y_4826_);
    crate::leanh::lean_dec(v___y_4825_);
    crate::leanh::lean_dec_ref(v___y_4824_);
    return v_res_4829_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4831_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__1___closed__0;
    v___x_4832_ = l_Lean_stringToMessageData(v___x_4831_);
    return v___x_4832_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__1___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4834_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__1___closed__2;
    v___x_4835_ = l_Lean_stringToMessageData(v___x_4834_);
    return v___x_4835_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__1(
    mut v___f_4836_: *mut crate::leanh::LeanObject,
    mut v_cls_4837_: *mut crate::leanh::LeanObject,
    mut v_00_u03c6_4838_: *mut crate::leanh::LeanObject,
    mut v___y_4839_: *mut crate::leanh::LeanObject,
    mut v___y_4840_: *mut crate::leanh::LeanObject,
    mut v___y_4841_: *mut crate::leanh::LeanObject,
    mut v___y_4842_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4856_: u8 = 0;
    let mut v___x_4857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_4863_: u8 = 0;
    let mut v_inheritedTraceOptions_4864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4867_: u8 = 0;
    let mut v___x_4868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4875_: u8 = 0;
    let mut v___x_4877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4879_: u8 = 0;
    let mut v_a_4880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4883_: u8 = 0;
    let mut v___x_4885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4887_: u8 = 0;
    let mut v_a_4888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4891_: u8 = 0;
    let mut v___x_4893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4895_: u8 = 0;
    let mut v___x_4896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4900_: u8 = 0;
    let mut v___x_4901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4906_: u8 = 0;
    let mut v___x_4907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4914_: u8 = 0;
    let mut v___x_4916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4918_: u8 = 0;
    let mut v_isSharedCheck_4919_: u8 = 0;
    let mut v_a_4920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4923_: u8 = 0;
    let mut v___x_4925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4927_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_4842_);
                crate::leanh::lean_inc_ref(v___y_4841_);
                crate::leanh::lean_inc(v___y_4840_);
                crate::leanh::lean_inc_ref(v___y_4839_);
                v___x_4896_ = crate::leanh::lean_apply_5(
                    v___f_4836_,
                    v___y_4839_,
                    v___y_4840_,
                    v___y_4841_,
                    v___y_4842_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_4896_) == 0 {
                    v_a_4897_ = crate::leanh::lean_ctor_get(v___x_4896_, 0);
                    v_isSharedCheck_4919_ = (!crate::leanh::lean_is_exclusive(v___x_4896_)) as u8;
                    if v_isSharedCheck_4919_ == 0 {
                        v___x_4899_ = v___x_4896_;
                        v_isShared_4900_ = v_isSharedCheck_4919_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4897_);
                        crate::leanh::lean_dec(v___x_4896_);
                        v___x_4899_ = crate::leanh::lean_box(0);
                        v_isShared_4900_ = v_isSharedCheck_4919_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_00_u03c6_4838_);
                    crate::leanh::lean_dec(v_cls_4837_);
                    v_a_4920_ = crate::leanh::lean_ctor_get(v___x_4896_, 0);
                    v_isSharedCheck_4927_ = (!crate::leanh::lean_is_exclusive(v___x_4896_)) as u8;
                    if v_isSharedCheck_4927_ == 0 {
                        v___x_4922_ = v___x_4896_;
                        v_isShared_4923_ = v_isSharedCheck_4927_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4920_);
                        crate::leanh::lean_dec(v___x_4896_);
                        v___x_4922_ = crate::leanh::lean_box(0);
                        v_isShared_4923_ = v_isSharedCheck_4927_;
                        state = 13;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4846_ = crate::leanh::lean_box(0);
                v___x_4847_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4847_, 0, v___x_4846_);
                crate::leanh::lean_ctor_set(v___x_4847_, 1, v___y_4845_);
                v___x_4848_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4848_, 0, v___x_4847_);
                v___x_4849_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4849_, 0, v___x_4848_);
                return v___x_4849_;
            }
            2 => {
                crate::leanh::lean_inc_ref(v_00_u03c6_4838_);
                v___x_4855_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4855_, 0, v_00_u03c6_4838_);
                v___x_4856_ = 0;
                v___x_4857_ = crate::leanh::lean_box(0);
                v___x_4858_ = l_Lean_Meta_mkFreshExprMVar(
                    v___x_4855_,
                    v___x_4856_,
                    v___x_4857_,
                    v___y_4851_,
                    v___y_4852_,
                    v___y_4853_,
                    v___y_4854_,
                );
                if crate::leanh::lean_obj_tag(v___x_4858_) == 0 {
                    v_a_4859_ = crate::leanh::lean_ctor_get(v___x_4858_, 0);
                    crate::leanh::lean_inc(v_a_4859_);
                    crate::leanh::lean_dec_ref_known(v___x_4858_, 1);
                    v___x_4860_ = l_Lean_Expr_mvarId_x21(v_a_4859_);
                    v___x_4861_ = l_Lean_MVarId_applyRflAndAndIntro(
                        v___x_4860_,
                        v___y_4851_,
                        v___y_4852_,
                        v___y_4853_,
                        v___y_4854_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4861_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_4861_, 1);
                        v_options_4862_ = crate::leanh::lean_ctor_get(v___y_4853_, 2);
                        v_hasTrace_4863_ = crate::leanh::lean_ctor_get_uint8(
                            v_options_4862_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        );
                        if v_hasTrace_4863_ == 0 {
                            crate::leanh::lean_dec_ref(v_00_u03c6_4838_);
                            crate::leanh::lean_dec(v_cls_4837_);
                            v___y_4845_ = v_a_4859_;
                            state = 1;
                            continue;
                        } else {
                            v_inheritedTraceOptions_4864_ =
                                crate::leanh::lean_ctor_get(v___y_4853_, 13);
                            v___x_4865_ = l_Lean_MVarId_applyRflAndAndIntro___closed__11;
                            crate::leanh::lean_inc(v_cls_4837_);
                            v___x_4866_ = l_Lean_Name_append(v___x_4865_, v_cls_4837_);
                            v___x_4867_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                v_inheritedTraceOptions_4864_,
                                v_options_4862_,
                                v___x_4866_,
                            );
                            crate::leanh::lean_dec(v___x_4866_);
                            if v___x_4867_ == 0 {
                                crate::leanh::lean_dec_ref(v_00_u03c6_4838_);
                                crate::leanh::lean_dec(v_cls_4837_);
                                v___y_4845_ = v_a_4859_;
                                state = 1;
                                continue;
                            } else {
                                v___x_4868_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__1___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__1___closed__1_once), _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__1___closed__1);
                                v___x_4869_ = l_Lean_MessageData_ofExpr(v_00_u03c6_4838_);
                                v___x_4870_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_4870_, 0, v___x_4868_);
                                crate::leanh::lean_ctor_set(v___x_4870_, 1, v___x_4869_);
                                v___x_4871_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro_spec__0(v_cls_4837_, v___x_4870_, v___y_4851_, v___y_4852_, v___y_4853_, v___y_4854_);
                                if crate::leanh::lean_obj_tag(v___x_4871_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_4871_, 1);
                                    v___y_4845_ = v_a_4859_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_a_4859_);
                                    v_a_4872_ = crate::leanh::lean_ctor_get(v___x_4871_, 0);
                                    v_isSharedCheck_4879_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_4871_)) as u8;
                                    if v_isSharedCheck_4879_ == 0 {
                                        v___x_4874_ = v___x_4871_;
                                        v_isShared_4875_ = v_isSharedCheck_4879_;
                                        state = 3;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_4872_);
                                        crate::leanh::lean_dec(v___x_4871_);
                                        v___x_4874_ = crate::leanh::lean_box(0);
                                        v_isShared_4875_ = v_isSharedCheck_4879_;
                                        state = 3;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_4859_);
                        crate::leanh::lean_dec_ref(v_00_u03c6_4838_);
                        crate::leanh::lean_dec(v_cls_4837_);
                        v_a_4880_ = crate::leanh::lean_ctor_get(v___x_4861_, 0);
                        v_isSharedCheck_4887_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4861_)) as u8;
                        if v_isSharedCheck_4887_ == 0 {
                            v___x_4882_ = v___x_4861_;
                            v_isShared_4883_ = v_isSharedCheck_4887_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4880_);
                            crate::leanh::lean_dec(v___x_4861_);
                            v___x_4882_ = crate::leanh::lean_box(0);
                            v_isShared_4883_ = v_isSharedCheck_4887_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_00_u03c6_4838_);
                    crate::leanh::lean_dec(v_cls_4837_);
                    v_a_4888_ = crate::leanh::lean_ctor_get(v___x_4858_, 0);
                    v_isSharedCheck_4895_ = (!crate::leanh::lean_is_exclusive(v___x_4858_)) as u8;
                    if v_isSharedCheck_4895_ == 0 {
                        v___x_4890_ = v___x_4858_;
                        v_isShared_4891_ = v_isSharedCheck_4895_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4888_);
                        crate::leanh::lean_dec(v___x_4858_);
                        v___x_4890_ = crate::leanh::lean_box(0);
                        v_isShared_4891_ = v_isSharedCheck_4895_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_4875_ == 0 {
                    v___x_4877_ = v___x_4874_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4878_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4878_, 0, v_a_4872_);
                    v___x_4877_ = v_reuseFailAlloc_4878_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4877_;
            }
            5 => {
                if v_isShared_4883_ == 0 {
                    v___x_4885_ = v___x_4882_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4886_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4886_, 0, v_a_4880_);
                    v___x_4885_ = v_reuseFailAlloc_4886_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4885_;
            }
            7 => {
                if v_isShared_4891_ == 0 {
                    v___x_4893_ = v___x_4890_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4894_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4894_, 0, v_a_4888_);
                    v___x_4893_ = v_reuseFailAlloc_4894_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4893_;
            }
            9 => {
                if crate::leanh::lean_obj_tag(v_a_4897_) == 0 {
                    crate::leanh::lean_dec_ref(v_00_u03c6_4838_);
                    crate::leanh::lean_dec(v_cls_4837_);
                    v___x_4901_ = crate::leanh::lean_box(0);
                    if v_isShared_4900_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4899_, 0, v___x_4901_);
                        v___x_4903_ = v___x_4899_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_4904_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4904_, 0, v___x_4901_);
                        v___x_4903_ = v_reuseFailAlloc_4904_;
                        state = 10;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4899_);
                    v_val_4905_ = crate::leanh::lean_ctor_get(v_a_4897_, 0);
                    crate::leanh::lean_inc(v_val_4905_);
                    crate::leanh::lean_dec_ref_known(v_a_4897_, 1);
                    v___x_4906_ = (crate::leanh::lean_unbox(v_val_4905_) as u8);
                    crate::leanh::lean_dec(v_val_4905_);
                    if v___x_4906_ == 0 {
                        v___y_4851_ = v___y_4839_;
                        v___y_4852_ = v___y_4840_;
                        v___y_4853_ = v___y_4841_;
                        v___y_4854_ = v___y_4842_;
                        state = 2;
                        continue;
                    } else {
                        v___x_4907_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__1___closed__3), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__1___closed__3_once), _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__1___closed__3);
                        crate::leanh::lean_inc_ref(v_00_u03c6_4838_);
                        v___x_4908_ = l_Lean_MessageData_ofExpr(v_00_u03c6_4838_);
                        v___x_4909_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4909_, 0, v___x_4907_);
                        crate::leanh::lean_ctor_set(v___x_4909_, 1, v___x_4908_);
                        crate::leanh::lean_inc(v_cls_4837_);
                        v___x_4910_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro_spec__0(v_cls_4837_, v___x_4909_, v___y_4839_, v___y_4840_, v___y_4841_, v___y_4842_);
                        if crate::leanh::lean_obj_tag(v___x_4910_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_4910_, 1);
                            v___y_4851_ = v___y_4839_;
                            v___y_4852_ = v___y_4840_;
                            v___y_4853_ = v___y_4841_;
                            v___y_4854_ = v___y_4842_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_00_u03c6_4838_);
                            crate::leanh::lean_dec(v_cls_4837_);
                            v_a_4911_ = crate::leanh::lean_ctor_get(v___x_4910_, 0);
                            v_isSharedCheck_4918_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4910_)) as u8;
                            if v_isSharedCheck_4918_ == 0 {
                                v___x_4913_ = v___x_4910_;
                                v_isShared_4914_ = v_isSharedCheck_4918_;
                                state = 11;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4911_);
                                crate::leanh::lean_dec(v___x_4910_);
                                v___x_4913_ = crate::leanh::lean_box(0);
                                v_isShared_4914_ = v_isSharedCheck_4918_;
                                state = 11;
                                continue;
                            }
                        }
                    }
                }
            }
            10 => {
                return v___x_4903_;
            }
            11 => {
                if v_isShared_4914_ == 0 {
                    v___x_4916_ = v___x_4913_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4917_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4917_, 0, v_a_4911_);
                    v___x_4916_ = v_reuseFailAlloc_4917_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4916_;
            }
            13 => {
                if v_isShared_4923_ == 0 {
                    v___x_4925_ = v___x_4922_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4926_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4926_, 0, v_a_4920_);
                    v___x_4925_ = v_reuseFailAlloc_4926_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4925_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__1___boxed(
    mut v___f_4928_: *mut crate::leanh::LeanObject,
    mut v_cls_4929_: *mut crate::leanh::LeanObject,
    mut v_00_u03c6_4930_: *mut crate::leanh::LeanObject,
    mut v___y_4931_: *mut crate::leanh::LeanObject,
    mut v___y_4932_: *mut crate::leanh::LeanObject,
    mut v___y_4933_: *mut crate::leanh::LeanObject,
    mut v___y_4934_: *mut crate::leanh::LeanObject,
    mut v___y_4935_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4936_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__1(
        v___f_4928_,
        v_cls_4929_,
        v_00_u03c6_4930_,
        v___y_4931_,
        v___y_4932_,
        v___y_4933_,
        v___y_4934_,
    );
    crate::leanh::lean_dec(v___y_4934_);
    crate::leanh::lean_dec_ref(v___y_4933_);
    crate::leanh::lean_dec(v___y_4932_);
    crate::leanh::lean_dec_ref(v___y_4931_);
    return v_res_4936_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4943_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___closed__2;
    v___x_4944_ = l_Lean_stringToMessageData(v___x_4943_);
    return v___x_4944_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro(
    mut v_goal_4945_: *mut crate::leanh::LeanObject,
    mut v_a_4946_: *mut crate::leanh::LeanObject,
    mut v_a_4947_: *mut crate::leanh::LeanObject,
    mut v_a_4948_: *mut crate::leanh::LeanObject,
    mut v_a_4949_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4956_: u8 = 0;
    let mut v___x_4957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cls_4958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4972_: u8 = 0;
    let mut v_val_4973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4976_: u8 = 0;
    let mut v_snd_4977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4984_: u8 = 0;
    let mut v_isSharedCheck_4985_: u8 = 0;
    let mut v_a_4986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4987_: u8 = 0;
    let mut v___x_4988_: u8 = 0;
    let mut v___x_4989_: u8 = 0;
    let mut v_target_4990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4998_: u8 = 0;
    let mut v___x_5000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5002_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_cls_4958_ = l_Lean_MVarId_applyRflAndAndIntro___closed__9;
                v___x_4959_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___lam__0(
                    v_cls_4958_,
                    v_a_4946_,
                    v_a_4947_,
                    v_a_4948_,
                    v_a_4949_,
                );
                v_a_4960_ = crate::leanh::lean_ctor_get(v___x_4959_, 0);
                crate::leanh::lean_inc(v_a_4960_);
                crate::leanh::lean_dec_ref(v___x_4959_);
                v_val_4961_ = crate::leanh::lean_ctor_get(v_a_4960_, 0);
                crate::leanh::lean_inc(v_val_4961_);
                crate::leanh::lean_dec(v_a_4960_);
                v___f_4962_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___closed__1;
                v___x_4989_ = (crate::leanh::lean_unbox(v_val_4961_) as u8);
                crate::leanh::lean_dec(v_val_4961_);
                if v___x_4989_ == 0 {
                    v___y_4964_ = v_a_4946_;
                    v___y_4965_ = v_a_4947_;
                    v___y_4966_ = v_a_4948_;
                    v___y_4967_ = v_a_4949_;
                    state = 3;
                    continue;
                } else {
                    v_target_4990_ = crate::leanh::lean_ctor_get(v_goal_4945_, 3);
                    v___x_4991_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___closed__3), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___closed__3_once), _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___closed__3);
                    crate::leanh::lean_inc_ref(v_target_4990_);
                    v___x_4992_ = l_Lean_MessageData_ofExpr(v_target_4990_);
                    v___x_4993_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4993_, 0, v___x_4991_);
                    crate::leanh::lean_ctor_set(v___x_4993_, 1, v___x_4992_);
                    v___x_4994_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro_spec__0(v_cls_4958_, v___x_4993_, v_a_4946_, v_a_4947_, v_a_4948_, v_a_4949_);
                    if crate::leanh::lean_obj_tag(v___x_4994_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_4994_, 1);
                        v___y_4964_ = v_a_4946_;
                        v___y_4965_ = v_a_4947_;
                        v___y_4966_ = v_a_4948_;
                        v___y_4967_ = v_a_4949_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_goal_4945_);
                        v_a_4995_ = crate::leanh::lean_ctor_get(v___x_4994_, 0);
                        v_isSharedCheck_5002_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4994_)) as u8;
                        if v_isSharedCheck_5002_ == 0 {
                            v___x_4997_ = v___x_4994_;
                            v_isShared_4998_ = v_isSharedCheck_5002_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4995_);
                            crate::leanh::lean_dec(v___x_4994_);
                            v___x_4997_ = crate::leanh::lean_box(0);
                            v_isShared_4998_ = v_isSharedCheck_5002_;
                            state = 8;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_4952_ = crate::leanh::lean_box(0);
                v___x_4953_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4953_, 0, v___x_4952_);
                return v___x_4953_;
            }
            2 => {
                if v___y_4956_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_4955_);
                    state = 1;
                    continue;
                } else {
                    v___x_4957_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4957_, 0, v___y_4955_);
                    return v___x_4957_;
                }
            }
            3 => {
                v___x_4968_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro_spec__1___redArg(v_goal_4945_, v___f_4962_, v___y_4964_, v___y_4965_, v___y_4966_, v___y_4967_);
                if crate::leanh::lean_obj_tag(v___x_4968_) == 0 {
                    v_a_4969_ = crate::leanh::lean_ctor_get(v___x_4968_, 0);
                    v_isSharedCheck_4985_ = (!crate::leanh::lean_is_exclusive(v___x_4968_)) as u8;
                    if v_isSharedCheck_4985_ == 0 {
                        v___x_4971_ = v___x_4968_;
                        v_isShared_4972_ = v_isSharedCheck_4985_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4969_);
                        crate::leanh::lean_dec(v___x_4968_);
                        v___x_4971_ = crate::leanh::lean_box(0);
                        v_isShared_4972_ = v_isSharedCheck_4985_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_4986_ = crate::leanh::lean_ctor_get(v___x_4968_, 0);
                    crate::leanh::lean_inc(v_a_4986_);
                    crate::leanh::lean_dec_ref_known(v___x_4968_, 1);
                    v___x_4987_ = l_Lean_Exception_isInterrupt(v_a_4986_);
                    if v___x_4987_ == 0 {
                        crate::leanh::lean_inc(v_a_4986_);
                        v___x_4988_ = l_Lean_Exception_isRuntime(v_a_4986_);
                        v___y_4955_ = v_a_4986_;
                        v___y_4956_ = v___x_4988_;
                        state = 2;
                        continue;
                    } else {
                        v___y_4955_ = v_a_4986_;
                        v___y_4956_ = v___x_4987_;
                        state = 2;
                        continue;
                    }
                }
            }
            4 => {
                if crate::leanh::lean_obj_tag(v_a_4969_) == 0 {
                    crate::leanh::lean_del_object(v___x_4971_);
                    state = 1;
                    continue;
                } else {
                    v_val_4973_ = crate::leanh::lean_ctor_get(v_a_4969_, 0);
                    v_isSharedCheck_4984_ = (!crate::leanh::lean_is_exclusive(v_a_4969_)) as u8;
                    if v_isSharedCheck_4984_ == 0 {
                        v___x_4975_ = v_a_4969_;
                        v_isShared_4976_ = v_isSharedCheck_4984_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4973_);
                        crate::leanh::lean_dec(v_a_4969_);
                        v___x_4975_ = crate::leanh::lean_box(0);
                        v_isShared_4976_ = v_isSharedCheck_4984_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v_snd_4977_ = crate::leanh::lean_ctor_get(v_val_4973_, 1);
                crate::leanh::lean_inc(v_snd_4977_);
                crate::leanh::lean_dec(v_val_4973_);
                if v_isShared_4976_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4975_, 0, v_snd_4977_);
                    v___x_4979_ = v___x_4975_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4983_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4983_, 0, v_snd_4977_);
                    v___x_4979_ = v_reuseFailAlloc_4983_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_4972_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4971_, 0, v___x_4979_);
                    v___x_4981_ = v___x_4971_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4982_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4982_, 0, v___x_4979_);
                    v___x_4981_ = v_reuseFailAlloc_4982_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4981_;
            }
            8 => {
                if v_isShared_4998_ == 0 {
                    v___x_5000_ = v___x_4997_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5001_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5001_, 0, v_a_4995_);
                    v___x_5000_ = v_reuseFailAlloc_5001_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5000_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro___boxed(
    mut v_goal_5003_: *mut crate::leanh::LeanObject,
    mut v_a_5004_: *mut crate::leanh::LeanObject,
    mut v_a_5005_: *mut crate::leanh::LeanObject,
    mut v_a_5006_: *mut crate::leanh::LeanObject,
    mut v_a_5007_: *mut crate::leanh::LeanObject,
    mut v_a_5008_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5009_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro(
        v_goal_5003_,
        v_a_5004_,
        v_a_5005_,
        v_a_5006_,
        v_a_5007_,
    );
    crate::leanh::lean_dec(v_a_5007_);
    crate::leanh::lean_dec_ref(v_a_5006_);
    crate::leanh::lean_dec(v_a_5005_);
    crate::leanh::lean_dec_ref(v_a_5004_);
    return v_res_5009_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__0(
    mut v___y_5010_: u8,
    mut v_x_5011_: *mut crate::leanh::LeanObject,
) -> u8 {
    return v___y_5010_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__0___boxed(
    mut v___y_5012_: *mut crate::leanh::LeanObject,
    mut v_x_5013_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_9301__boxed_5014_: u8 = 0;
    let mut v_res_5015_: u8 = 0;
    let mut v_r_5016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_9301__boxed_5014_ = (crate::leanh::lean_unbox(v___y_5012_) as u8);
    v_res_5015_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__0(
        v___y_9301__boxed_5014_,
        v_x_5013_,
    );
    crate::leanh::lean_dec(v_x_5013_);
    v_r_5016_ = crate::leanh::lean_box((v_res_5015_) as usize);
    return v_r_5016_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__1(
    mut v_00_u03c6_5029_: *mut crate::leanh::LeanObject,
    mut v___y_5030_: *mut crate::leanh::LeanObject,
    mut v___y_5031_: *mut crate::leanh::LeanObject,
    mut v___y_5032_: *mut crate::leanh::LeanObject,
    mut v___y_5033_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5036_: u8 = 0;
    let mut v___x_5037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5042_: u8 = 0;
    let mut v___x_5044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5055_: u8 = 0;
    let mut v___y_5057_: u8 = 0;
    let mut v_ref_5058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5068_: u8 = 0;
    let mut v___x_5069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5077_: u8 = 0;
    let mut v_fst_5078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5082_: u8 = 0;
    let mut v_a_5083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5086_: u8 = 0;
    let mut v___x_5088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5090_: u8 = 0;
    let mut v___x_5092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5094_: u8 = 0;
    let mut v___x_5095_: u8 = 0;
    let mut v_isSharedCheck_5096_: u8 = 0;
    let mut v_isSharedCheck_5097_: u8 = 0;
    let mut v_a_5098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5101_: u8 = 0;
    let mut v___x_5103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5105_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5035_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5035_, 0, v_00_u03c6_5029_);
                v___x_5036_ = 0;
                v___x_5037_ = crate::leanh::lean_box(0);
                v___x_5038_ = l_Lean_Meta_mkFreshExprMVar(
                    v___x_5035_,
                    v___x_5036_,
                    v___x_5037_,
                    v___y_5030_,
                    v___y_5031_,
                    v___y_5032_,
                    v___y_5033_,
                );
                if crate::leanh::lean_obj_tag(v___x_5038_) == 0 {
                    v_a_5039_ = crate::leanh::lean_ctor_get(v___x_5038_, 0);
                    v_isSharedCheck_5097_ = (!crate::leanh::lean_is_exclusive(v___x_5038_)) as u8;
                    if v_isSharedCheck_5097_ == 0 {
                        v___x_5041_ = v___x_5038_;
                        v_isShared_5042_ = v_isSharedCheck_5097_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5039_);
                        crate::leanh::lean_dec(v___x_5038_);
                        v___x_5041_ = crate::leanh::lean_box(0);
                        v_isShared_5042_ = v_isSharedCheck_5097_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5098_ = crate::leanh::lean_ctor_get(v___x_5038_, 0);
                    v_isSharedCheck_5105_ = (!crate::leanh::lean_is_exclusive(v___x_5038_)) as u8;
                    if v_isSharedCheck_5105_ == 0 {
                        v___x_5100_ = v___x_5038_;
                        v_isShared_5101_ = v_isSharedCheck_5105_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5098_);
                        crate::leanh::lean_dec(v___x_5038_);
                        v___x_5100_ = crate::leanh::lean_box(0);
                        v_isShared_5101_ = v_isSharedCheck_5105_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5050_ = l_Lean_Expr_mvarId_x21(v_a_5039_);
                crate::leanh::lean_inc(v___x_5050_);
                v___x_5051_ = l_Lean_MVarId_applyRflAndAndIntro(
                    v___x_5050_,
                    v___y_5030_,
                    v___y_5031_,
                    v___y_5032_,
                    v___y_5033_,
                );
                if crate::leanh::lean_obj_tag(v___x_5051_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_5051_, 1);
                    crate::leanh::lean_dec(v___x_5050_);
                    state = 2;
                    continue;
                } else {
                    v_a_5052_ = crate::leanh::lean_ctor_get(v___x_5051_, 0);
                    v_isSharedCheck_5096_ = (!crate::leanh::lean_is_exclusive(v___x_5051_)) as u8;
                    if v_isSharedCheck_5096_ == 0 {
                        v___x_5054_ = v___x_5051_;
                        v_isShared_5055_ = v_isSharedCheck_5096_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5052_);
                        crate::leanh::lean_dec(v___x_5051_);
                        v___x_5054_ = crate::leanh::lean_box(0);
                        v_isShared_5055_ = v_isSharedCheck_5096_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5044_ = crate::leanh::lean_box(0);
                v___x_5045_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5045_, 0, v___x_5044_);
                crate::leanh::lean_ctor_set(v___x_5045_, 1, v_a_5039_);
                v___x_5046_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5046_, 0, v___x_5045_);
                if v_isShared_5042_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5041_, 0, v___x_5046_);
                    v___x_5048_ = v___x_5041_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5049_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5049_, 0, v___x_5046_);
                    v___x_5048_ = v_reuseFailAlloc_5049_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5048_;
            }
            4 => {
                v___x_5094_ = l_Lean_Exception_isInterrupt(v_a_5052_);
                if v___x_5094_ == 0 {
                    crate::leanh::lean_inc(v_a_5052_);
                    v___x_5095_ = l_Lean_Exception_isRuntime(v_a_5052_);
                    v___y_5057_ = v___x_5095_;
                    state = 5;
                    continue;
                } else {
                    v___y_5057_ = v___x_5094_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v___y_5057_ == 0 {
                    crate::leanh::lean_del_object(v___x_5054_);
                    crate::leanh::lean_dec(v_a_5052_);
                    v_ref_5058_ = crate::leanh::lean_ctor_get(v___y_5032_, 5);
                    v___x_5059_ = crate::leanh::lean_box((v___y_5057_) as usize);
                    v___f_5060_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__0___boxed
                            as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_5060_, 0, v___x_5059_);
                    v___x_5061_ = l_Lean_SourceInfo_fromRef(v_ref_5058_, v___y_5057_);
                    v___x_5062_ =
                        l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__1___closed__1;
                    v___x_5063_ =
                        l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__1___closed__2;
                    crate::leanh::lean_inc(v___x_5061_);
                    v___x_5064_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5064_, 0, v___x_5061_);
                    crate::leanh::lean_ctor_set(v___x_5064_, 1, v___x_5063_);
                    v___x_5065_ = l_Lean_Syntax_node1(v___x_5061_, v___x_5062_, v___x_5064_);
                    v___x_5066_ = crate::leanh::lean_box(0);
                    v___x_5067_ = crate::leanh::lean_box(0);
                    v___x_5068_ = 1;
                    v___x_5069_ = crate::leanh::lean_box(1);
                    v___x_5070_ =
                        l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__1___closed__3;
                    v___x_5071_ = crate::leanh::lean_alloc_ctor(0, 8, (11) as u32);
                    crate::leanh::lean_ctor_set(v___x_5071_, 0, v___x_5066_);
                    crate::leanh::lean_ctor_set(v___x_5071_, 1, v___x_5067_);
                    crate::leanh::lean_ctor_set(v___x_5071_, 2, v___x_5066_);
                    crate::leanh::lean_ctor_set(v___x_5071_, 3, v___f_5060_);
                    crate::leanh::lean_ctor_set(v___x_5071_, 4, v___x_5069_);
                    crate::leanh::lean_ctor_set(v___x_5071_, 5, v___x_5069_);
                    crate::leanh::lean_ctor_set(v___x_5071_, 6, v___x_5066_);
                    crate::leanh::lean_ctor_set(v___x_5071_, 7, v___x_5070_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_5071_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                        v___x_5068_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_5071_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 1) as u32,
                        v___x_5068_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_5071_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 2) as u32,
                        v___x_5068_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_5071_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 3) as u32,
                        v___x_5068_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_5071_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 4) as u32,
                        v___y_5057_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_5071_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 5) as u32,
                        v___y_5057_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_5071_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 6) as u32,
                        v___y_5057_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_5071_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 7) as u32,
                        v___y_5057_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_5071_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 8) as u32,
                        v___x_5068_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_5071_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 9) as u32,
                        v___y_5057_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_5071_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 10) as u32,
                        v___x_5068_,
                    );
                    v___x_5072_ =
                        l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__1___closed__4;
                    v___x_5073_ = l_Lean_Elab_runTactic(
                        v___x_5050_,
                        v___x_5065_,
                        v___x_5071_,
                        v___x_5072_,
                        v___y_5030_,
                        v___y_5031_,
                        v___y_5032_,
                        v___y_5033_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5073_) == 0 {
                        v_a_5074_ = crate::leanh::lean_ctor_get(v___x_5073_, 0);
                        v_isSharedCheck_5082_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5073_)) as u8;
                        if v_isSharedCheck_5082_ == 0 {
                            v___x_5076_ = v___x_5073_;
                            v_isShared_5077_ = v_isSharedCheck_5082_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5074_);
                            crate::leanh::lean_dec(v___x_5073_);
                            v___x_5076_ = crate::leanh::lean_box(0);
                            v_isShared_5077_ = v_isSharedCheck_5082_;
                            state = 6;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_5041_);
                        crate::leanh::lean_dec(v_a_5039_);
                        v_a_5083_ = crate::leanh::lean_ctor_get(v___x_5073_, 0);
                        v_isSharedCheck_5090_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5073_)) as u8;
                        if v_isSharedCheck_5090_ == 0 {
                            v___x_5085_ = v___x_5073_;
                            v_isShared_5086_ = v_isSharedCheck_5090_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5083_);
                            crate::leanh::lean_dec(v___x_5073_);
                            v___x_5085_ = crate::leanh::lean_box(0);
                            v_isShared_5086_ = v_isSharedCheck_5090_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_5050_);
                    crate::leanh::lean_del_object(v___x_5041_);
                    crate::leanh::lean_dec(v_a_5039_);
                    if v_isShared_5055_ == 0 {
                        v___x_5092_ = v___x_5054_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_5093_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5093_, 0, v_a_5052_);
                        v___x_5092_ = v_reuseFailAlloc_5093_;
                        state = 10;
                        continue;
                    }
                }
            }
            6 => {
                v_fst_5078_ = crate::leanh::lean_ctor_get(v_a_5074_, 0);
                crate::leanh::lean_inc(v_fst_5078_);
                crate::leanh::lean_dec(v_a_5074_);
                if crate::leanh::lean_obj_tag(v_fst_5078_) == 0 {
                    crate::leanh::lean_del_object(v___x_5076_);
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_fst_5078_);
                    crate::leanh::lean_del_object(v___x_5041_);
                    crate::leanh::lean_dec(v_a_5039_);
                    if v_isShared_5077_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5076_, 0, v___x_5066_);
                        v___x_5080_ = v___x_5076_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_5081_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5081_, 0, v___x_5066_);
                        v___x_5080_ = v_reuseFailAlloc_5081_;
                        state = 7;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_5080_;
            }
            8 => {
                if v_isShared_5086_ == 0 {
                    v___x_5088_ = v___x_5085_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5089_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5089_, 0, v_a_5083_);
                    v___x_5088_ = v_reuseFailAlloc_5089_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5088_;
            }
            10 => {
                return v___x_5092_;
            }
            11 => {
                if v_isShared_5101_ == 0 {
                    v___x_5103_ = v___x_5100_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5104_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5104_, 0, v_a_5098_);
                    v___x_5103_ = v_reuseFailAlloc_5104_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5103_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__1___boxed(
    mut v_00_u03c6_5106_: *mut crate::leanh::LeanObject,
    mut v___y_5107_: *mut crate::leanh::LeanObject,
    mut v___y_5108_: *mut crate::leanh::LeanObject,
    mut v___y_5109_: *mut crate::leanh::LeanObject,
    mut v___y_5110_: *mut crate::leanh::LeanObject,
    mut v___y_5111_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5112_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___lam__1(
        v_00_u03c6_5106_,
        v___y_5107_,
        v___y_5108_,
        v___y_5109_,
        v___y_5110_,
    );
    crate::leanh::lean_dec(v___y_5110_);
    crate::leanh::lean_dec_ref(v___y_5109_);
    crate::leanh::lean_dec(v___y_5108_);
    crate::leanh::lean_dec_ref(v___y_5107_);
    return v_res_5112_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial(
    mut v_goal_5114_: *mut crate::leanh::LeanObject,
    mut v_a_5115_: *mut crate::leanh::LeanObject,
    mut v_a_5116_: *mut crate::leanh::LeanObject,
    mut v_a_5117_: *mut crate::leanh::LeanObject,
    mut v_a_5118_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5128_: u8 = 0;
    let mut v_val_5129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5132_: u8 = 0;
    let mut v_snd_5133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5140_: u8 = 0;
    let mut v_isSharedCheck_5141_: u8 = 0;
    let mut v_a_5142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5145_: u8 = 0;
    let mut v___y_5147_: u8 = 0;
    let mut v___x_5149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5151_: u8 = 0;
    let mut v___x_5152_: u8 = 0;
    let mut v_isSharedCheck_5153_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_5123_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___closed__0;
                v___x_5124_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureIntroCore___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_pureRflAndAndIntro_spec__1___redArg(v_goal_5114_, v___f_5123_, v_a_5115_, v_a_5116_, v_a_5117_, v_a_5118_);
                if crate::leanh::lean_obj_tag(v___x_5124_) == 0 {
                    v_a_5125_ = crate::leanh::lean_ctor_get(v___x_5124_, 0);
                    v_isSharedCheck_5141_ = (!crate::leanh::lean_is_exclusive(v___x_5124_)) as u8;
                    if v_isSharedCheck_5141_ == 0 {
                        v___x_5127_ = v___x_5124_;
                        v_isShared_5128_ = v_isSharedCheck_5141_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5125_);
                        crate::leanh::lean_dec(v___x_5124_);
                        v___x_5127_ = crate::leanh::lean_box(0);
                        v_isShared_5128_ = v_isSharedCheck_5141_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_5142_ = crate::leanh::lean_ctor_get(v___x_5124_, 0);
                    v_isSharedCheck_5153_ = (!crate::leanh::lean_is_exclusive(v___x_5124_)) as u8;
                    if v_isSharedCheck_5153_ == 0 {
                        v___x_5144_ = v___x_5124_;
                        v_isShared_5145_ = v_isSharedCheck_5153_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5142_);
                        crate::leanh::lean_dec(v___x_5124_);
                        v___x_5144_ = crate::leanh::lean_box(0);
                        v_isShared_5145_ = v_isSharedCheck_5153_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5121_ = crate::leanh::lean_box(0);
                v___x_5122_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5122_, 0, v___x_5121_);
                return v___x_5122_;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_5125_) == 0 {
                    crate::leanh::lean_del_object(v___x_5127_);
                    state = 1;
                    continue;
                } else {
                    v_val_5129_ = crate::leanh::lean_ctor_get(v_a_5125_, 0);
                    v_isSharedCheck_5140_ = (!crate::leanh::lean_is_exclusive(v_a_5125_)) as u8;
                    if v_isSharedCheck_5140_ == 0 {
                        v___x_5131_ = v_a_5125_;
                        v_isShared_5132_ = v_isSharedCheck_5140_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5129_);
                        crate::leanh::lean_dec(v_a_5125_);
                        v___x_5131_ = crate::leanh::lean_box(0);
                        v_isShared_5132_ = v_isSharedCheck_5140_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v_snd_5133_ = crate::leanh::lean_ctor_get(v_val_5129_, 1);
                crate::leanh::lean_inc(v_snd_5133_);
                crate::leanh::lean_dec(v_val_5129_);
                if v_isShared_5132_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5131_, 0, v_snd_5133_);
                    v___x_5135_ = v___x_5131_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5139_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5139_, 0, v_snd_5133_);
                    v___x_5135_ = v_reuseFailAlloc_5139_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_5128_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5127_, 0, v___x_5135_);
                    v___x_5137_ = v___x_5127_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5138_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5138_, 0, v___x_5135_);
                    v___x_5137_ = v_reuseFailAlloc_5138_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5137_;
            }
            6 => {
                v___x_5151_ = l_Lean_Exception_isInterrupt(v_a_5142_);
                if v___x_5151_ == 0 {
                    crate::leanh::lean_inc(v_a_5142_);
                    v___x_5152_ = l_Lean_Exception_isRuntime(v_a_5142_);
                    v___y_5147_ = v___x_5152_;
                    state = 7;
                    continue;
                } else {
                    v___y_5147_ = v___x_5151_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v___y_5147_ == 0 {
                    crate::leanh::lean_del_object(v___x_5144_);
                    crate::leanh::lean_dec(v_a_5142_);
                    state = 1;
                    continue;
                } else {
                    if v_isShared_5145_ == 0 {
                        v___x_5149_ = v___x_5144_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_5150_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5150_, 0, v_a_5142_);
                        v___x_5149_ = v_reuseFailAlloc_5150_;
                        state = 8;
                        continue;
                    }
                }
            }
            8 => {
                return v___x_5149_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial___boxed(
    mut v_goal_5154_: *mut crate::leanh::LeanObject,
    mut v_a_5155_: *mut crate::leanh::LeanObject,
    mut v_a_5156_: *mut crate::leanh::LeanObject,
    mut v_a_5157_: *mut crate::leanh::LeanObject,
    mut v_a_5158_: *mut crate::leanh::LeanObject,
    mut v_a_5159_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5160_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_pureTrivial(
        v_goal_5154_,
        v_a_5155_,
        v_a_5156_,
        v_a_5157_,
        v_a_5158_,
    );
    crate::leanh::lean_dec(v_a_5158_);
    crate::leanh::lean_dec_ref(v_a_5157_);
    crate::leanh::lean_dec(v_a_5156_);
    crate::leanh::lean_dec_ref(v_a_5155_);
    return v_res_5160_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Pure(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Meta(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Rfl(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPure___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPure__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Do_ProofMode_Pure_0__Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMPureIntro__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Pure(
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
pub unsafe fn initialize_Lean_Elab_Tactic_Do_ProofMode_Pure(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Meta(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Rfl(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Pure(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Pure(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Do_ProofMode_Pure(builtin);
}
