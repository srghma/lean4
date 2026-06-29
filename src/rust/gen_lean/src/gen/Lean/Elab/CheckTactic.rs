// Lean compiler output
// Module: Lean.Elab.CheckTactic
// Imports: Lean.Elab.Tactic.ElabTerm Lean.Elab.Command Lean.Elab.Tactic.Meta Lean.Meta.CheckTactic
use crate::ffi::{
    lean_infer_type, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take, lean_uint64_lor,
    lean_uint64_shift_left, lean_uint64_shift_right,
};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Lean_Macro_throwUnsupported___redArg, l_Lean_SourceInfo_fromRef,
    l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind, l_Lean_Syntax_node1, l_Lean_Syntax_node4,
    l_Lean_Syntax_node6, l_Lean_replaceRef,
};
use crate::r#gen::Lean::CoreM::l_Lean_Exception_isRuntime;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::DeclarationRange::l_Lean_addBuiltinDeclarationRanges;
use crate::r#gen::Lean::Elab::Command::{
    initialize_Lean_Elab_Command, l_Lean_Elab_Command_commandElabAttribute,
    l_Lean_Elab_Command_runTermElabM___boxed, runtime_initialize_Lean_Elab_Command,
};
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::SyntheticMVars::l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp;
use crate::r#gen::Lean::Elab::Tactic::ElabTerm::{
    initialize_Lean_Elab_Tactic_ElabTerm, runtime_initialize_Lean_Elab_Tactic_ElabTerm,
};
use crate::r#gen::Lean::Elab::Tactic::Meta::{
    initialize_Lean_Elab_Tactic_Meta, l_Lean_Elab_runTactic,
    runtime_initialize_Lean_Elab_Tactic_Meta,
};
use crate::r#gen::Lean::Elab::Term::TermElabM::{
    l_Lean_Elab_Term_elabTerm, l_Lean_Elab_Term_elabTerm___boxed,
    l_Lean_Elab_Term_withoutErrToSorryImp___redArg,
};
use crate::r#gen::Lean::Elab::Util::{
    l_Lean_Elab_getBetterRef, l_Lean_Elab_macroAttribute, l_Lean_Elab_pp_macroStack,
};
use crate::r#gen::Lean::Environment::l_Lean_Environment_unlockAsync;
use crate::r#gen::Lean::Exception::l_Lean_Exception_isInterrupt;
use crate::r#gen::Lean::Expr::l_Lean_Expr_mvarId_x21;
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofSyntax, l_Lean_indentD, l_Lean_indentExpr,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l_Lean_Meta_Context_config, l_Lean_Meta_Context_configKey,
    l_Lean_Meta_TransparencyMode_toUInt64, l_Lean_Meta_isExprDefEq, l_Lean_Meta_mkFreshExprMVar,
};
use crate::r#gen::Lean::Meta::Check::l_Lean_Meta_addPPExplicitToExposeDiff;
use crate::r#gen::Lean::Meta::CheckTactic::{
    initialize_Lean_Meta_CheckTactic, l_Lean_Meta_CheckTactic_matchCheckGoalType,
    l_Lean_Meta_CheckTactic_mkCheckGoalType, runtime_initialize_Lean_Meta_CheckTactic,
};
use crate::r#gen::Lean::Meta::Tactic::Util::l_Lean_MVarId_getType;
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__7___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__7___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__7___closed__1_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__7___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__7___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__7___closed__2_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__7___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__7___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__7___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__7___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__7___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3___redArg___closed__0_value: crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3___redArg___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3___redArg___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__0_value:
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
static mut l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__1_value:
    crate::leanh::LeanStringObject<44> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 44,
    m_capacity: 44,
    m_length: 43,
    m_data: [
        32, 99, 108, 111, 115, 101, 100, 32, 103, 111, 97, 108, 44, 32, 98, 117, 116, 32, 105, 115,
        32, 101, 120, 112, 101, 99, 116, 101, 100, 32, 116, 111, 32, 114, 101, 100, 117, 99, 101,
        32, 116, 111, 32, 0,
    ],
};
static mut l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__3_value:
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
static mut l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__5_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 16,
    m_capacity: 16,
    m_length: 15,
    m_data: [
        84, 101, 114, 109, 32, 114, 101, 100, 117, 99, 101, 115, 32, 116, 111, 0,
    ],
};
static mut l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__7_value:
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
        10, 98, 117, 116, 32, 105, 115, 32, 101, 120, 112, 101, 99, 116, 101, 100, 32, 116, 111,
        32, 114, 101, 100, 117, 99, 101, 32, 116, 111, 32, 0,
    ],
};
static mut l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__7_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__8_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__9_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__9: u64 = 0;
pub static l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__10_value:
    crate::leanh::LeanStringObject<56> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 56,
    m_capacity: 56,
    m_length: 55,
    m_data: [
        32, 112, 114, 111, 100, 117, 99, 101, 100, 32, 109, 117, 108, 116, 105, 112, 108, 101, 32,
        103, 111, 97, 108, 115, 44, 32, 98, 117, 116, 32, 105, 115, 32, 101, 120, 112, 101, 99,
        116, 101, 100, 32, 116, 111, 32, 114, 101, 100, 117, 99, 101, 32, 116, 111, 32, 0,
    ],
};
static mut l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__10_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__11_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_CheckTactic_elabCheckTactic___closed__0_value:
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
static mut l_Lean_Elab_CheckTactic_elabCheckTactic___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_CheckTactic_elabCheckTactic___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_CheckTactic_elabCheckTactic___closed__1_value:
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
static mut l_Lean_Elab_CheckTactic_elabCheckTactic___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_CheckTactic_elabCheckTactic___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_CheckTactic_elabCheckTactic___closed__2_value:
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
    m_data: [99, 104, 101, 99, 107, 84, 97, 99, 116, 105, 99, 0],
};
static mut l_Lean_Elab_CheckTactic_elabCheckTactic___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_CheckTactic_elabCheckTactic___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_CheckTactic_elabCheckTactic___closed__3_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_CheckTactic_elabCheckTactic___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_CheckTactic_elabCheckTactic___closed__3_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_CheckTactic_elabCheckTactic___closed__3_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_CheckTactic_elabCheckTactic___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_CheckTactic_elabCheckTactic___closed__3_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_CheckTactic_elabCheckTactic___closed__3_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_CheckTactic_elabCheckTactic___closed__2_value)
            as *mut crate::leanh::LeanObject,
        1214589715727107155 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_CheckTactic_elabCheckTactic___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_CheckTactic_elabCheckTactic___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_CheckTactic_elabCheckTactic___closed__4_value:
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
    m_fun: l_Lean_Elab_CheckTactic_elabCheckTactic___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_CheckTactic_elabCheckTactic___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_CheckTactic_elabCheckTactic___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__1_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [67, 104, 101, 99, 107, 84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__2_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [101, 108, 97, 98, 67, 104, 101, 99, 107, 84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__2_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_CheckTactic_elabCheckTactic___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__0_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__1_value) as *mut crate::leanh::LeanObject,5729374976268143281 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__3_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__2_value) as *mut crate::leanh::LeanObject,10614445492145178730 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 24 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 45 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 95 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__2_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject,((( 95 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 24 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 4 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 24 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 19 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__5_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject,((( 4 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject,((( 19 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__6_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__0_value:
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
        32, 101, 120, 112, 101, 99, 116, 101, 100, 32, 116, 111, 32, 102, 97, 105, 108, 32, 111,
        110, 32, 0,
    ],
};
static mut l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__2_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 19,
    m_capacity: 19,
    m_length: 18,
    m_data: [
        44, 32, 98, 117, 116, 32, 99, 108, 111, 115, 101, 100, 32, 103, 111, 97, 108, 46, 0,
    ],
};
static mut l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__4_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 17,
    m_capacity: 17,
    m_length: 16,
    m_data: [
        44, 32, 98, 117, 116, 32, 114, 101, 116, 117, 114, 110, 101, 100, 58, 32, 0,
    ],
};
static mut l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__6_value:
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
        44, 32, 98, 117, 116, 32, 114, 101, 116, 117, 114, 110, 101, 100, 32, 103, 111, 97, 108,
        115, 58, 0,
    ],
};
static mut l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_CheckTactic_elabCheckTacticFailure___closed__0_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 19,
    m_capacity: 19,
    m_length: 18,
    m_data: [
        99, 104, 101, 99, 107, 84, 97, 99, 116, 105, 99, 70, 97, 105, 108, 117, 114, 101, 0,
    ],
};
static mut l_Lean_Elab_CheckTactic_elabCheckTacticFailure___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_CheckTactic_elabCheckTacticFailure___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_CheckTactic_elabCheckTactic___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_CheckTactic_elabCheckTacticFailure___closed__1_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_CheckTactic_elabCheckTactic___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_CheckTactic_elabCheckTacticFailure___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11101102451118813740 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_CheckTactic_elabCheckTacticFailure___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1___closed__0_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [101, 108, 97, 98, 67, 104, 101, 99, 107, 84, 97, 99, 116, 105, 99, 70, 97, 105, 108, 117, 114, 101, 0]};
static mut l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_CheckTactic_elabCheckTactic___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__0_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__1_value) as *mut crate::leanh::LeanObject,5729374976268143281 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1___closed__0_value) as *mut crate::leanh::LeanObject,10664081151829438362 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 48 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 73 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 30 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__2_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject,((( 30 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 48 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 4 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 48 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 26 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__5_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject,((( 4 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject,((( 26 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__6_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_CheckTactic_expandCheckSimp___closed__0_value:
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
    m_data: [99, 104, 101, 99, 107, 83, 105, 109, 112, 0],
};
static mut l_Lean_Elab_CheckTactic_expandCheckSimp___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_CheckTactic_expandCheckSimp___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_CheckTactic_elabCheckTactic___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_CheckTactic_expandCheckSimp___closed__1_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_CheckTactic_elabCheckTactic___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_CheckTactic_expandCheckSimp___closed__1_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__0_value)
            as *mut crate::leanh::LeanObject,
        4228361627258539776 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_CheckTactic_expandCheckSimp___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_CheckTactic_expandCheckSimp___closed__2_value:
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
    m_data: [35, 99, 104, 101, 99, 107, 95, 116, 97, 99, 116, 105, 99, 0],
};
static mut l_Lean_Elab_CheckTactic_expandCheckSimp___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_CheckTactic_expandCheckSimp___closed__3_value:
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
    m_data: [126, 62, 0],
};
static mut l_Lean_Elab_CheckTactic_expandCheckSimp___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_CheckTactic_expandCheckSimp___closed__4_value:
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
    m_data: [98, 121, 0],
};
static mut l_Lean_Elab_CheckTactic_expandCheckSimp___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_CheckTactic_expandCheckSimp___closed__5_value:
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
static mut l_Lean_Elab_CheckTactic_expandCheckSimp___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_CheckTactic_expandCheckSimp___closed__6_value:
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
    m_data: [115, 105, 109, 112, 0],
};
static mut l_Lean_Elab_CheckTactic_expandCheckSimp___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__6_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_CheckTactic_expandCheckSimp___closed__7_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_CheckTactic_elabCheckTactic___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_CheckTactic_expandCheckSimp___closed__7_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__7_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_CheckTactic_elabCheckTactic___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_CheckTactic_expandCheckSimp___closed__7_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__7_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__5_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_CheckTactic_expandCheckSimp___closed__7_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__7_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__6_value)
            as *mut crate::leanh::LeanObject,
        12783917532758215986 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_CheckTactic_expandCheckSimp___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_CheckTactic_expandCheckSimp___closed__8_value:
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
    m_data: [111, 112, 116, 67, 111, 110, 102, 105, 103, 0],
};
static mut l_Lean_Elab_CheckTactic_expandCheckSimp___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__8_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_CheckTactic_expandCheckSimp___closed__9_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_CheckTactic_elabCheckTactic___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_CheckTactic_expandCheckSimp___closed__9_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__9_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_CheckTactic_elabCheckTactic___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_CheckTactic_expandCheckSimp___closed__9_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__9_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__5_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_CheckTactic_expandCheckSimp___closed__9_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__9_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__8_value)
            as *mut crate::leanh::LeanObject,
        3488656302031949961 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_CheckTactic_expandCheckSimp___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_CheckTactic_expandCheckSimp___closed__10_value:
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
    m_data: [110, 117, 108, 108, 0],
};
static mut l_Lean_Elab_CheckTactic_expandCheckSimp___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_CheckTactic_expandCheckSimp___closed__11_value:
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
        core::ptr::addr_of!(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__10_value)
            as *mut crate::leanh::LeanObject,
        9855511589286918680 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_CheckTactic_expandCheckSimp___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__11_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_CheckTactic_expandCheckSimp___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_CheckTactic_expandCheckSimp___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___closed__0_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [101, 120, 112, 97, 110, 100, 67, 104, 101, 99, 107, 83, 105, 109, 112, 0]};
static mut l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_CheckTactic_elabCheckTactic___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__0_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__1_value) as *mut crate::leanh::LeanObject,5729374976268143281 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___closed__0_value) as *mut crate::leanh::LeanObject,5385904866729992180 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 76 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 78 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 45 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__2_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject,((( 45 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 76 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 4 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 76 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 19 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__5_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject,((( 4 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject,((( 19 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__6_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_CheckTactic_expandCheckSimpFailure___closed__0_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 17,
    m_capacity: 17,
    m_length: 16,
    m_data: [
        99, 104, 101, 99, 107, 83, 105, 109, 112, 70, 97, 105, 108, 117, 114, 101, 0,
    ],
};
static mut l_Lean_Elab_CheckTactic_expandCheckSimpFailure___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_CheckTactic_expandCheckSimpFailure___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_CheckTactic_expandCheckSimpFailure___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_CheckTactic_elabCheckTactic___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_CheckTactic_expandCheckSimpFailure___closed__1_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_CheckTactic_expandCheckSimpFailure___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_CheckTactic_elabCheckTactic___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_CheckTactic_expandCheckSimpFailure___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Elab_CheckTactic_expandCheckSimpFailure___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_CheckTactic_expandCheckSimpFailure___closed__0_value)
            as *mut crate::leanh::LeanObject,
        13602963300204363974 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_CheckTactic_expandCheckSimpFailure___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_CheckTactic_expandCheckSimpFailure___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_CheckTactic_expandCheckSimpFailure___closed__2_value:
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
        35, 99, 104, 101, 99, 107, 95, 116, 97, 99, 116, 105, 99, 95, 102, 97, 105, 108, 117, 114,
        101, 0,
    ],
};
static mut l_Lean_Elab_CheckTactic_expandCheckSimpFailure___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_CheckTactic_expandCheckSimpFailure___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1___closed__0_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [101, 120, 112, 97, 110, 100, 67, 104, 101, 99, 107, 83, 105, 109, 112, 70, 97, 105, 108, 117, 114, 101, 0]};
static mut l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_CheckTactic_elabCheckTactic___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__0_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__1_value) as *mut crate::leanh::LeanObject,5729374976268143281 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1___closed__0_value) as *mut crate::leanh::LeanObject,15886782356662143607 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 81 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 83 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 45 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__2_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject,((( 45 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 81 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 4 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 81 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 26 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__5_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject,((( 4 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject,((( 26 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__6_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__6_value) as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1390_ = crate::leanh::lean_box(0);
    v___x_1391_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_1392_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1392_, 0, v___x_1391_);
    crate::leanh::lean_ctor_set(v___x_1392_, 1, v___x_1390_);
    return v___x_1392_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__0___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1394_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__0___redArg___closed__0);
    v___x_1395_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1395_, 0, v___x_1394_);
    return v___x_1395_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__0___redArg___boxed(
    mut v___y_1396_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1397_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__0___redArg();
    return v_res_1397_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__0(
    mut v_00_u03b1_1398_: *mut crate::leanh::LeanObject,
    mut v___y_1399_: *mut crate::leanh::LeanObject,
    mut v___y_1400_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1402_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__0___redArg();
    return v___x_1402_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__0___boxed(
    mut v_00_u03b1_1403_: *mut crate::leanh::LeanObject,
    mut v___y_1404_: *mut crate::leanh::LeanObject,
    mut v___y_1405_: *mut crate::leanh::LeanObject,
    mut v___y_1406_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1407_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__0(
            v_00_u03b1_1403_,
            v___y_1404_,
            v___y_1405_,
        );
    crate::leanh::lean_dec(v___y_1405_);
    crate::leanh::lean_dec_ref(v___y_1404_);
    return v_res_1407_;
}
pub unsafe fn l_Lean_Elab_CheckTactic_elabCheckTactic___lam__0(
    mut v_x_1408_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1409_: u8 = 0;
    v___x_1409_ = 0;
    return v___x_1409_;
}
pub unsafe fn l_Lean_Elab_CheckTactic_elabCheckTactic___lam__0___boxed(
    mut v_x_1410_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1411_: u8 = 0;
    let mut v_r_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1411_ = l_Lean_Elab_CheckTactic_elabCheckTactic___lam__0(v_x_1410_);
    crate::leanh::lean_dec(v_x_1410_);
    v_r_1412_ = crate::leanh::lean_box((v_res_1411_) as usize);
    return v_r_1412_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2(
    mut v_msgData_1413_: *mut crate::leanh::LeanObject,
    mut v___y_1414_: *mut crate::leanh::LeanObject,
    mut v___y_1415_: *mut crate::leanh::LeanObject,
    mut v___y_1416_: *mut crate::leanh::LeanObject,
    mut v___y_1417_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1419_ = lean_st_ref_get(v___y_1417_);
    v_env_1420_ = crate::leanh::lean_ctor_get(v___x_1419_, 0);
    crate::leanh::lean_inc_ref(v_env_1420_);
    crate::leanh::lean_dec(v___x_1419_);
    v___x_1421_ = lean_st_ref_get(v___y_1415_);
    v_mctx_1422_ = crate::leanh::lean_ctor_get(v___x_1421_, 0);
    crate::leanh::lean_inc_ref(v_mctx_1422_);
    crate::leanh::lean_dec(v___x_1421_);
    v_lctx_1423_ = crate::leanh::lean_ctor_get(v___y_1414_, 2);
    v_options_1424_ = crate::leanh::lean_ctor_get(v___y_1416_, 2);
    crate::leanh::lean_inc_ref(v_options_1424_);
    crate::leanh::lean_inc_ref(v_lctx_1423_);
    v___x_1425_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1425_, 0, v_env_1420_);
    crate::leanh::lean_ctor_set(v___x_1425_, 1, v_mctx_1422_);
    crate::leanh::lean_ctor_set(v___x_1425_, 2, v_lctx_1423_);
    crate::leanh::lean_ctor_set(v___x_1425_, 3, v_options_1424_);
    v___x_1426_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1426_, 0, v___x_1425_);
    crate::leanh::lean_ctor_set(v___x_1426_, 1, v_msgData_1413_);
    v___x_1427_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1427_, 0, v___x_1426_);
    return v___x_1427_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2___boxed(
    mut v_msgData_1428_: *mut crate::leanh::LeanObject,
    mut v___y_1429_: *mut crate::leanh::LeanObject,
    mut v___y_1430_: *mut crate::leanh::LeanObject,
    mut v___y_1431_: *mut crate::leanh::LeanObject,
    mut v___y_1432_: *mut crate::leanh::LeanObject,
    mut v___y_1433_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1434_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2(v_msgData_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_);
    crate::leanh::lean_dec(v___y_1432_);
    crate::leanh::lean_dec_ref(v___y_1431_);
    crate::leanh::lean_dec(v___y_1430_);
    crate::leanh::lean_dec_ref(v___y_1429_);
    return v_res_1434_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__7___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1435_ = crate::leanh::lean_box(1);
    v___x_1436_ = l_Lean_MessageData_ofFormat(v___x_1435_);
    return v___x_1436_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__7___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1440_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__7___closed__2;
    v___x_1441_ = l_Lean_MessageData_ofFormat(v___x_1440_);
    return v___x_1441_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__7(
    mut v_x_1442_: *mut crate::leanh::LeanObject,
    mut v_x_1443_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1448_: u8 = 0;
    let mut v_before_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1452_: u8 = 0;
    let mut v___x_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1465_: u8 = 0;
    let mut v_unused_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1467_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1443_) == 0 {
                    return v_x_1442_;
                } else {
                    v_head_1444_ = crate::leanh::lean_ctor_get(v_x_1443_, 0);
                    v_tail_1445_ = crate::leanh::lean_ctor_get(v_x_1443_, 1);
                    v_isSharedCheck_1467_ = (!crate::leanh::lean_is_exclusive(v_x_1443_)) as u8;
                    if v_isSharedCheck_1467_ == 0 {
                        v___x_1447_ = v_x_1443_;
                        v_isShared_1448_ = v_isSharedCheck_1467_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1445_);
                        crate::leanh::lean_inc(v_head_1444_);
                        crate::leanh::lean_dec(v_x_1443_);
                        v___x_1447_ = crate::leanh::lean_box(0);
                        v_isShared_1448_ = v_isSharedCheck_1467_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_1449_ = crate::leanh::lean_ctor_get(v_head_1444_, 0);
                v_isSharedCheck_1465_ = (!crate::leanh::lean_is_exclusive(v_head_1444_)) as u8;
                if v_isSharedCheck_1465_ == 0 {
                    v_unused_1466_ = crate::leanh::lean_ctor_get(v_head_1444_, 1);
                    crate::leanh::lean_dec(v_unused_1466_);
                    v___x_1451_ = v_head_1444_;
                    v_isShared_1452_ = v_isSharedCheck_1465_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_before_1449_);
                    crate::leanh::lean_dec(v_head_1444_);
                    v___x_1451_ = crate::leanh::lean_box(0);
                    v_isShared_1452_ = v_isSharedCheck_1465_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1453_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__7___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__7___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__7___closed__0);
                if v_isShared_1452_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1451_, 7);
                    crate::leanh::lean_ctor_set(v___x_1451_, 1, v___x_1453_);
                    crate::leanh::lean_ctor_set(v___x_1451_, 0, v_x_1442_);
                    v___x_1455_ = v___x_1451_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1464_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1464_, 0, v_x_1442_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1464_, 1, v___x_1453_);
                    v___x_1455_ = v_reuseFailAlloc_1464_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1456_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__7___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__7___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__7___closed__3);
                if v_isShared_1448_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1447_, 7);
                    crate::leanh::lean_ctor_set(v___x_1447_, 1, v___x_1456_);
                    crate::leanh::lean_ctor_set(v___x_1447_, 0, v___x_1455_);
                    v___x_1458_ = v___x_1447_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1463_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1463_, 0, v___x_1455_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1463_, 1, v___x_1456_);
                    v___x_1458_ = v_reuseFailAlloc_1463_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1459_ = l_Lean_MessageData_ofSyntax(v_before_1449_);
                v___x_1460_ = l_Lean_indentD(v___x_1459_);
                v___x_1461_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1461_, 0, v___x_1458_);
                crate::leanh::lean_ctor_set(v___x_1461_, 1, v___x_1460_);
                v_x_1442_ = v___x_1461_;
                v_x_1443_ = v_tail_1445_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__6(
    mut v_opts_1468_: *mut crate::leanh::LeanObject,
    mut v_opt_1469_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_1470_ = crate::leanh::lean_ctor_get(v_opt_1469_, 0);
    v_defValue_1471_ = crate::leanh::lean_ctor_get(v_opt_1469_, 1);
    v_map_1472_ = crate::leanh::lean_ctor_get(v_opts_1468_, 0);
    v___x_1473_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_1472_,
            v_name_1470_,
        );
    if crate::leanh::lean_obj_tag(v___x_1473_) == 0 {
        let mut v___x_1474_: u8 = 0;
        v___x_1474_ = (crate::leanh::lean_unbox(v_defValue_1471_) as u8);
        return v___x_1474_;
    } else {
        let mut v_val_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1475_ = crate::leanh::lean_ctor_get(v___x_1473_, 0);
        crate::leanh::lean_inc(v_val_1475_);
        crate::leanh::lean_dec_ref_known(v___x_1473_, 1);
        if crate::leanh::lean_obj_tag(v_val_1475_) == 1 {
            let mut v_v_1476_: u8 = 0;
            v_v_1476_ = crate::leanh::lean_ctor_get_uint8(v_val_1475_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_1475_, 0);
            return v_v_1476_;
        } else {
            let mut v___x_1477_: u8 = 0;
            crate::leanh::lean_dec(v_val_1475_);
            v___x_1477_ = (crate::leanh::lean_unbox(v_defValue_1471_) as u8);
            return v___x_1477_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__6___boxed(
    mut v_opts_1478_: *mut crate::leanh::LeanObject,
    mut v_opt_1479_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1480_: u8 = 0;
    let mut v_r_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1480_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__6(v_opts_1478_, v_opt_1479_);
    crate::leanh::lean_dec_ref(v_opt_1479_);
    crate::leanh::lean_dec_ref(v_opts_1478_);
    v_r_1481_ = crate::leanh::lean_box((v_res_1480_) as usize);
    return v_r_1481_;
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1485_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3___redArg___closed__1;
    v___x_1486_ = l_Lean_MessageData_ofFormat(v___x_1485_);
    return v___x_1486_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3___redArg(
    mut v_msgData_1487_: *mut crate::leanh::LeanObject,
    mut v_macroStack_1488_: *mut crate::leanh::LeanObject,
    mut v___y_1489_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: u8 = 0;
    let mut v___x_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_after_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1500_: u8 = 0;
    let mut v___x_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgData_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1512_: u8 = 0;
    let mut v_unused_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_1491_ = crate::leanh::lean_ctor_get(v___y_1489_, 2);
                v___x_1492_ = l_Lean_Elab_pp_macroStack;
                v___x_1493_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__6(v_options_1491_, v___x_1492_);
                if v___x_1493_ == 0 {
                    crate::leanh::lean_dec(v_macroStack_1488_);
                    v___x_1494_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1494_, 0, v_msgData_1487_);
                    return v___x_1494_;
                } else {
                    if crate::leanh::lean_obj_tag(v_macroStack_1488_) == 0 {
                        v___x_1495_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1495_, 0, v_msgData_1487_);
                        return v___x_1495_;
                    } else {
                        v_head_1496_ = crate::leanh::lean_ctor_get(v_macroStack_1488_, 0);
                        crate::leanh::lean_inc(v_head_1496_);
                        v_after_1497_ = crate::leanh::lean_ctor_get(v_head_1496_, 1);
                        v_isSharedCheck_1512_ =
                            (!crate::leanh::lean_is_exclusive(v_head_1496_)) as u8;
                        if v_isSharedCheck_1512_ == 0 {
                            v_unused_1513_ = crate::leanh::lean_ctor_get(v_head_1496_, 0);
                            crate::leanh::lean_dec(v_unused_1513_);
                            v___x_1499_ = v_head_1496_;
                            v_isShared_1500_ = v_isSharedCheck_1512_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_after_1497_);
                            crate::leanh::lean_dec(v_head_1496_);
                            v___x_1499_ = crate::leanh::lean_box(0);
                            v_isShared_1500_ = v_isSharedCheck_1512_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1501_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__7___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__7___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__7___closed__0);
                if v_isShared_1500_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1499_, 7);
                    crate::leanh::lean_ctor_set(v___x_1499_, 1, v___x_1501_);
                    crate::leanh::lean_ctor_set(v___x_1499_, 0, v_msgData_1487_);
                    v___x_1503_ = v___x_1499_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1511_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1511_, 0, v_msgData_1487_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1511_, 1, v___x_1501_);
                    v___x_1503_ = v_reuseFailAlloc_1511_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1504_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3___redArg___closed__2);
                v___x_1505_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1505_, 0, v___x_1503_);
                crate::leanh::lean_ctor_set(v___x_1505_, 1, v___x_1504_);
                v___x_1506_ = l_Lean_MessageData_ofSyntax(v_after_1497_);
                v___x_1507_ = l_Lean_indentD(v___x_1506_);
                v_msgData_1508_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v_msgData_1508_, 0, v___x_1505_);
                crate::leanh::lean_ctor_set(v_msgData_1508_, 1, v___x_1507_);
                v___x_1509_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3_spec__7(v_msgData_1508_, v_macroStack_1488_);
                v___x_1510_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1510_, 0, v___x_1509_);
                return v___x_1510_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3___redArg___boxed(
    mut v_msgData_1514_: *mut crate::leanh::LeanObject,
    mut v_macroStack_1515_: *mut crate::leanh::LeanObject,
    mut v___y_1516_: *mut crate::leanh::LeanObject,
    mut v___y_1517_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1518_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3___redArg(v_msgData_1514_, v_macroStack_1515_, v___y_1516_);
    crate::leanh::lean_dec_ref(v___y_1516_);
    return v_res_1518_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1___redArg(
    mut v_msg_1519_: *mut crate::leanh::LeanObject,
    mut v___y_1520_: *mut crate::leanh::LeanObject,
    mut v___y_1521_: *mut crate::leanh::LeanObject,
    mut v___y_1522_: *mut crate::leanh::LeanObject,
    mut v___y_1523_: *mut crate::leanh::LeanObject,
    mut v___y_1524_: *mut crate::leanh::LeanObject,
    mut v___y_1525_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1536_: u8 = 0;
    let mut v___x_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1541_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1527_ = crate::leanh::lean_ctor_get(v___y_1524_, 5);
                v___x_1528_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__2(v_msg_1519_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_);
                v_a_1529_ = crate::leanh::lean_ctor_get(v___x_1528_, 0);
                crate::leanh::lean_inc(v_a_1529_);
                crate::leanh::lean_dec_ref(v___x_1528_);
                v_macroStack_1530_ = crate::leanh::lean_ctor_get(v___y_1520_, 1);
                v___x_1531_ = l_Lean_Elab_getBetterRef(v_ref_1527_, v_macroStack_1530_);
                crate::leanh::lean_inc(v_macroStack_1530_);
                v___x_1532_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3___redArg(v_a_1529_, v_macroStack_1530_, v___y_1524_);
                v_a_1533_ = crate::leanh::lean_ctor_get(v___x_1532_, 0);
                v_isSharedCheck_1541_ = (!crate::leanh::lean_is_exclusive(v___x_1532_)) as u8;
                if v_isSharedCheck_1541_ == 0 {
                    v___x_1535_ = v___x_1532_;
                    v_isShared_1536_ = v_isSharedCheck_1541_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1533_);
                    crate::leanh::lean_dec(v___x_1532_);
                    v___x_1535_ = crate::leanh::lean_box(0);
                    v_isShared_1536_ = v_isSharedCheck_1541_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1537_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1537_, 0, v___x_1531_);
                crate::leanh::lean_ctor_set(v___x_1537_, 1, v_a_1533_);
                if v_isShared_1536_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1535_, 1);
                    crate::leanh::lean_ctor_set(v___x_1535_, 0, v___x_1537_);
                    v___x_1539_ = v___x_1535_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1540_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1540_, 0, v___x_1537_);
                    v___x_1539_ = v_reuseFailAlloc_1540_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1539_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1___redArg___boxed(
    mut v_msg_1542_: *mut crate::leanh::LeanObject,
    mut v___y_1543_: *mut crate::leanh::LeanObject,
    mut v___y_1544_: *mut crate::leanh::LeanObject,
    mut v___y_1545_: *mut crate::leanh::LeanObject,
    mut v___y_1546_: *mut crate::leanh::LeanObject,
    mut v___y_1547_: *mut crate::leanh::LeanObject,
    mut v___y_1548_: *mut crate::leanh::LeanObject,
    mut v___y_1549_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1550_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1___redArg(v_msg_1542_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_);
    crate::leanh::lean_dec(v___y_1548_);
    crate::leanh::lean_dec_ref(v___y_1547_);
    crate::leanh::lean_dec(v___y_1546_);
    crate::leanh::lean_dec_ref(v___y_1545_);
    crate::leanh::lean_dec(v___y_1544_);
    crate::leanh::lean_dec_ref(v___y_1543_);
    return v_res_1550_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg(
    mut v_ref_1551_: *mut crate::leanh::LeanObject,
    mut v_msg_1552_: *mut crate::leanh::LeanObject,
    mut v___y_1553_: *mut crate::leanh::LeanObject,
    mut v___y_1554_: *mut crate::leanh::LeanObject,
    mut v___y_1555_: *mut crate::leanh::LeanObject,
    mut v___y_1556_: *mut crate::leanh::LeanObject,
    mut v___y_1557_: *mut crate::leanh::LeanObject,
    mut v___y_1558_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1572_: u8 = 0;
    let mut v_cancelTk_x3f_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1574_: u8 = 0;
    let mut v_inheritedTraceOptions_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fileName_1560_ = crate::leanh::lean_ctor_get(v___y_1557_, 0);
    v_fileMap_1561_ = crate::leanh::lean_ctor_get(v___y_1557_, 1);
    v_options_1562_ = crate::leanh::lean_ctor_get(v___y_1557_, 2);
    v_currRecDepth_1563_ = crate::leanh::lean_ctor_get(v___y_1557_, 3);
    v_maxRecDepth_1564_ = crate::leanh::lean_ctor_get(v___y_1557_, 4);
    v_ref_1565_ = crate::leanh::lean_ctor_get(v___y_1557_, 5);
    v_currNamespace_1566_ = crate::leanh::lean_ctor_get(v___y_1557_, 6);
    v_openDecls_1567_ = crate::leanh::lean_ctor_get(v___y_1557_, 7);
    v_initHeartbeats_1568_ = crate::leanh::lean_ctor_get(v___y_1557_, 8);
    v_maxHeartbeats_1569_ = crate::leanh::lean_ctor_get(v___y_1557_, 9);
    v_quotContext_1570_ = crate::leanh::lean_ctor_get(v___y_1557_, 10);
    v_currMacroScope_1571_ = crate::leanh::lean_ctor_get(v___y_1557_, 11);
    v_diag_1572_ = crate::leanh::lean_ctor_get_uint8(
        v___y_1557_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_1573_ = crate::leanh::lean_ctor_get(v___y_1557_, 12);
    v_suppressElabErrors_1574_ = crate::leanh::lean_ctor_get_uint8(
        v___y_1557_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_1575_ = crate::leanh::lean_ctor_get(v___y_1557_, 13);
    v_ref_1576_ = l_Lean_replaceRef(v_ref_1551_, v_ref_1565_);
    crate::leanh::lean_inc_ref(v_inheritedTraceOptions_1575_);
    crate::leanh::lean_inc(v_cancelTk_x3f_1573_);
    crate::leanh::lean_inc(v_currMacroScope_1571_);
    crate::leanh::lean_inc(v_quotContext_1570_);
    crate::leanh::lean_inc(v_maxHeartbeats_1569_);
    crate::leanh::lean_inc(v_initHeartbeats_1568_);
    crate::leanh::lean_inc(v_openDecls_1567_);
    crate::leanh::lean_inc(v_currNamespace_1566_);
    crate::leanh::lean_inc(v_maxRecDepth_1564_);
    crate::leanh::lean_inc(v_currRecDepth_1563_);
    crate::leanh::lean_inc_ref(v_options_1562_);
    crate::leanh::lean_inc_ref(v_fileMap_1561_);
    crate::leanh::lean_inc_ref(v_fileName_1560_);
    v___x_1577_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_1577_, 0, v_fileName_1560_);
    crate::leanh::lean_ctor_set(v___x_1577_, 1, v_fileMap_1561_);
    crate::leanh::lean_ctor_set(v___x_1577_, 2, v_options_1562_);
    crate::leanh::lean_ctor_set(v___x_1577_, 3, v_currRecDepth_1563_);
    crate::leanh::lean_ctor_set(v___x_1577_, 4, v_maxRecDepth_1564_);
    crate::leanh::lean_ctor_set(v___x_1577_, 5, v_ref_1576_);
    crate::leanh::lean_ctor_set(v___x_1577_, 6, v_currNamespace_1566_);
    crate::leanh::lean_ctor_set(v___x_1577_, 7, v_openDecls_1567_);
    crate::leanh::lean_ctor_set(v___x_1577_, 8, v_initHeartbeats_1568_);
    crate::leanh::lean_ctor_set(v___x_1577_, 9, v_maxHeartbeats_1569_);
    crate::leanh::lean_ctor_set(v___x_1577_, 10, v_quotContext_1570_);
    crate::leanh::lean_ctor_set(v___x_1577_, 11, v_currMacroScope_1571_);
    crate::leanh::lean_ctor_set(v___x_1577_, 12, v_cancelTk_x3f_1573_);
    crate::leanh::lean_ctor_set(v___x_1577_, 13, v_inheritedTraceOptions_1575_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1577_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
        v_diag_1572_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_1577_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_1574_,
    );
    v___x_1578_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1___redArg(v_msg_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___x_1577_, v___y_1558_);
    crate::leanh::lean_dec_ref_known(v___x_1577_, 14);
    return v___x_1578_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg___boxed(
    mut v_ref_1579_: *mut crate::leanh::LeanObject,
    mut v_msg_1580_: *mut crate::leanh::LeanObject,
    mut v___y_1581_: *mut crate::leanh::LeanObject,
    mut v___y_1582_: *mut crate::leanh::LeanObject,
    mut v___y_1583_: *mut crate::leanh::LeanObject,
    mut v___y_1584_: *mut crate::leanh::LeanObject,
    mut v___y_1585_: *mut crate::leanh::LeanObject,
    mut v___y_1586_: *mut crate::leanh::LeanObject,
    mut v___y_1587_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1588_ =
        l_Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg(
            v_ref_1579_,
            v_msg_1580_,
            v___y_1581_,
            v___y_1582_,
            v___y_1583_,
            v___y_1584_,
            v___y_1585_,
            v___y_1586_,
        );
    crate::leanh::lean_dec(v___y_1586_);
    crate::leanh::lean_dec_ref(v___y_1585_);
    crate::leanh::lean_dec(v___y_1584_);
    crate::leanh::lean_dec_ref(v___y_1583_);
    crate::leanh::lean_dec(v___y_1582_);
    crate::leanh::lean_dec_ref(v___y_1581_);
    crate::leanh::lean_dec(v_ref_1579_);
    return v_res_1588_;
}
pub unsafe fn _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1592_ = l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__1;
    v___x_1593_ = l_Lean_stringToMessageData(v___x_1592_);
    return v___x_1593_;
}
pub unsafe fn _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1595_ = l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__3;
    v___x_1596_ = l_Lean_stringToMessageData(v___x_1595_);
    return v___x_1596_;
}
pub unsafe fn _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1598_ = l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__5;
    v___x_1599_ = l_Lean_stringToMessageData(v___x_1598_);
    return v___x_1599_;
}
pub unsafe fn _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1601_ = l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__7;
    v___x_1602_ = l_Lean_stringToMessageData(v___x_1601_);
    return v___x_1602_;
}
pub unsafe fn _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__9() -> u64 {
    let mut v___x_1603_: u8 = 0;
    let mut v___x_1604_: u64 = 0;
    v___x_1603_ = 2;
    v___x_1604_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_1603_);
    return v___x_1604_;
}
pub unsafe fn _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1606_ = l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__10;
    v___x_1607_ = l_Lean_stringToMessageData(v___x_1606_);
    return v___x_1607_;
}
pub unsafe fn l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1(
    mut v___x_1608_: *mut crate::leanh::LeanObject,
    mut v___x_1609_: u8,
    mut v___x_1610_: *mut crate::leanh::LeanObject,
    mut v___f_1611_: *mut crate::leanh::LeanObject,
    mut v___x_1612_: *mut crate::leanh::LeanObject,
    mut v___x_1613_: *mut crate::leanh::LeanObject,
    mut v_stx_1614_: *mut crate::leanh::LeanObject,
    mut v___vars_1615_: *mut crate::leanh::LeanObject,
    mut v___y_1616_: *mut crate::leanh::LeanObject,
    mut v___y_1617_: *mut crate::leanh::LeanObject,
    mut v___y_1618_: *mut crate::leanh::LeanObject,
    mut v___y_1619_: *mut crate::leanh::LeanObject,
    mut v___y_1620_: *mut crate::leanh::LeanObject,
    mut v___y_1621_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: u8 = 0;
    let mut v___x_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: u8 = 0;
    let mut v___x_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: u8 = 0;
    let mut v___x_1649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1657_: u8 = 0;
    let mut v___x_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1672_: u8 = 0;
    let mut v___x_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1680_: u8 = 0;
    let mut v_a_1682_: u8 = 0;
    let mut v___x_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1689_: u8 = 0;
    let mut v___x_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1704_: u8 = 0;
    let mut v_a_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1708_: u8 = 0;
    let mut v___x_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1712_: u8 = 0;
    let mut v___x_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_foApprox_1714_: u8 = 0;
    let mut v_ctxApprox_1715_: u8 = 0;
    let mut v_quasiPatternApprox_1716_: u8 = 0;
    let mut v_constApprox_1717_: u8 = 0;
    let mut v_isDefEqStuckEx_1718_: u8 = 0;
    let mut v_unificationHints_1719_: u8 = 0;
    let mut v_proofIrrelevance_1720_: u8 = 0;
    let mut v_assignSyntheticOpaque_1721_: u8 = 0;
    let mut v_offsetCnstrs_1722_: u8 = 0;
    let mut v_etaStruct_1723_: u8 = 0;
    let mut v_univApprox_1724_: u8 = 0;
    let mut v_iota_1725_: u8 = 0;
    let mut v_beta_1726_: u8 = 0;
    let mut v_proj_1727_: u8 = 0;
    let mut v_zeta_1728_: u8 = 0;
    let mut v_zetaDelta_1729_: u8 = 0;
    let mut v_zetaUnused_1730_: u8 = 0;
    let mut v_zetaHave_1731_: u8 = 0;
    let mut v___x_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1734_: u8 = 0;
    let mut v_trackZetaDelta_1735_: u8 = 0;
    let mut v_zetaDeltaSet_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_1742_: u8 = 0;
    let mut v_inTypeClassResolution_1743_: u8 = 0;
    let mut v_cacheInferType_1744_: u8 = 0;
    let mut v___x_1745_: u8 = 0;
    let mut v_config_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: u64 = 0;
    let mut v___x_1749_: u64 = 0;
    let mut v___x_1750_: u64 = 0;
    let mut v___x_1751_: u64 = 0;
    let mut v___x_1752_: u64 = 0;
    let mut v_key_1753_: u64 = 0;
    let mut v___x_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: u8 = 0;
    let mut v_a_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: u8 = 0;
    let mut v_a_1761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1764_: u8 = 0;
    let mut v___x_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1768_: u8 = 0;
    let mut v_reuseFailAlloc_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1770_: u8 = 0;
    let mut v_isSharedCheck_1771_: u8 = 0;
    let mut v_unused_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1776_: u8 = 0;
    let mut v___x_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1780_: u8 = 0;
    let mut v_a_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1784_: u8 = 0;
    let mut v___x_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1788_: u8 = 0;
    let mut v_isSharedCheck_1789_: u8 = 0;
    let mut v_unused_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1793_: u8 = 0;
    let mut v___x_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1806_: u8 = 0;
    let mut v_unused_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1809_: u8 = 0;
    let mut v_unused_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1814_: u8 = 0;
    let mut v___x_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1818_: u8 = 0;
    let mut v_a_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1822_: u8 = 0;
    let mut v___x_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1826_: u8 = 0;
    let mut v_a_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1830_: u8 = 0;
    let mut v___x_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1834_: u8 = 0;
    let mut v_a_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1838_: u8 = 0;
    let mut v___x_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1842_: u8 = 0;
    let mut v_a_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1846_: u8 = 0;
    let mut v___x_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1850_: u8 = 0;
    let mut v_a_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1854_: u8 = 0;
    let mut v___x_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1858_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1626_ = crate::leanh::lean_box(0);
                v___x_1627_ = crate::leanh::lean_box((v___x_1609_) as usize);
                v___x_1628_ = crate::leanh::lean_box((v___x_1609_) as usize);
                v___x_1629_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_Term_elabTerm___boxed as *mut core::ffi::c_void,
                    11,
                    4,
                );
                crate::leanh::lean_closure_set(v___x_1629_, 0, v___x_1608_);
                crate::leanh::lean_closure_set(v___x_1629_, 1, v___x_1626_);
                crate::leanh::lean_closure_set(v___x_1629_, 2, v___x_1627_);
                crate::leanh::lean_closure_set(v___x_1629_, 3, v___x_1628_);
                v___x_1630_ = 1;
                v___x_1631_ =
                    l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(
                        crate::leanh::lean_box(0),
                        v___x_1629_,
                        v___x_1630_,
                        v___y_1616_,
                        v___y_1617_,
                        v___y_1618_,
                        v___y_1619_,
                        v___y_1620_,
                        v___y_1621_,
                    );
                if crate::leanh::lean_obj_tag(v___x_1631_) == 0 {
                    v_a_1632_ = crate::leanh::lean_ctor_get(v___x_1631_, 0);
                    crate::leanh::lean_inc_n(v_a_1632_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_1631_, 1);
                    crate::leanh::lean_inc(v___y_1621_);
                    crate::leanh::lean_inc_ref(v___y_1620_);
                    crate::leanh::lean_inc(v___y_1619_);
                    crate::leanh::lean_inc_ref(v___y_1618_);
                    v___x_1633_ = lean_infer_type(
                        v_a_1632_,
                        v___y_1618_,
                        v___y_1619_,
                        v___y_1620_,
                        v___y_1621_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1633_) == 0 {
                        v_a_1634_ = crate::leanh::lean_ctor_get(v___x_1633_, 0);
                        crate::leanh::lean_inc_n(v_a_1634_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_1633_, 1);
                        v___x_1635_ = l_Lean_Meta_CheckTactic_mkCheckGoalType(
                            v_a_1632_,
                            v_a_1634_,
                            v___y_1618_,
                            v___y_1619_,
                            v___y_1620_,
                            v___y_1621_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1635_) == 0 {
                            v_a_1636_ = crate::leanh::lean_ctor_get(v___x_1635_, 0);
                            crate::leanh::lean_inc(v_a_1636_);
                            crate::leanh::lean_dec_ref_known(v___x_1635_, 1);
                            v___x_1637_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1637_, 0, v_a_1636_);
                            v___x_1638_ = 0;
                            v___x_1639_ = crate::leanh::lean_box(0);
                            v___x_1640_ = l_Lean_Meta_mkFreshExprMVar(
                                v___x_1637_,
                                v___x_1638_,
                                v___x_1639_,
                                v___y_1618_,
                                v___y_1619_,
                                v___y_1620_,
                                v___y_1621_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_1640_) == 0 {
                                v_a_1641_ = crate::leanh::lean_ctor_get(v___x_1640_, 0);
                                crate::leanh::lean_inc(v_a_1641_);
                                crate::leanh::lean_dec_ref_known(v___x_1640_, 1);
                                v___x_1642_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1642_, 0, v_a_1634_);
                                v___x_1643_ = l_Lean_Elab_Term_elabTerm(
                                    v___x_1610_,
                                    v___x_1642_,
                                    v___x_1609_,
                                    v___x_1609_,
                                    v___y_1616_,
                                    v___y_1617_,
                                    v___y_1618_,
                                    v___y_1619_,
                                    v___y_1620_,
                                    v___y_1621_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_1643_) == 0 {
                                    v_a_1644_ = crate::leanh::lean_ctor_get(v___x_1643_, 0);
                                    crate::leanh::lean_inc(v_a_1644_);
                                    crate::leanh::lean_dec_ref_known(v___x_1643_, 1);
                                    v___x_1645_ = l_Lean_Expr_mvarId_x21(v_a_1641_);
                                    crate::leanh::lean_dec(v_a_1641_);
                                    v___x_1646_ = crate::leanh::lean_box(0);
                                    v___x_1647_ = crate::leanh::lean_box(1);
                                    v___x_1648_ = 0;
                                    v___x_1649_ = l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__0;
                                    v___x_1650_ = crate::leanh::lean_alloc_ctor(0, 8, (11) as u32);
                                    crate::leanh::lean_ctor_set(v___x_1650_, 0, v___x_1626_);
                                    crate::leanh::lean_ctor_set(v___x_1650_, 1, v___x_1646_);
                                    crate::leanh::lean_ctor_set(v___x_1650_, 2, v___x_1626_);
                                    crate::leanh::lean_ctor_set(v___x_1650_, 3, v___f_1611_);
                                    crate::leanh::lean_ctor_set(v___x_1650_, 4, v___x_1647_);
                                    crate::leanh::lean_ctor_set(v___x_1650_, 5, v___x_1647_);
                                    crate::leanh::lean_ctor_set(v___x_1650_, 6, v___x_1626_);
                                    crate::leanh::lean_ctor_set(v___x_1650_, 7, v___x_1649_);
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_1650_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8)
                                            as u32,
                                        v___x_1609_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_1650_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8
                                            + 1) as u32,
                                        v___x_1609_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_1650_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8
                                            + 2) as u32,
                                        v___x_1609_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_1650_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8
                                            + 3) as u32,
                                        v___x_1609_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_1650_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8
                                            + 4) as u32,
                                        v___x_1648_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_1650_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8
                                            + 5) as u32,
                                        v___x_1648_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_1650_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8
                                            + 6) as u32,
                                        v___x_1648_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_1650_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8
                                            + 7) as u32,
                                        v___x_1648_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_1650_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8
                                            + 8) as u32,
                                        v___x_1609_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_1650_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8
                                            + 9) as u32,
                                        v___x_1648_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_1650_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8
                                            + 10) as u32,
                                        v___x_1609_,
                                    );
                                    v___x_1651_ = crate::leanh::lean_alloc_ctor(0, 7, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_1651_, 0, v___x_1612_);
                                    crate::leanh::lean_ctor_set(v___x_1651_, 1, v___x_1647_);
                                    crate::leanh::lean_ctor_set(v___x_1651_, 2, v___x_1646_);
                                    crate::leanh::lean_ctor_set(v___x_1651_, 3, v___x_1646_);
                                    crate::leanh::lean_ctor_set(v___x_1651_, 4, v___x_1646_);
                                    crate::leanh::lean_ctor_set(v___x_1651_, 5, v___x_1647_);
                                    crate::leanh::lean_ctor_set(v___x_1651_, 6, v___x_1646_);
                                    crate::leanh::lean_inc(v___x_1613_);
                                    v___x_1652_ = l_Lean_Elab_runTactic(
                                        v___x_1645_,
                                        v___x_1613_,
                                        v___x_1650_,
                                        v___x_1651_,
                                        v___y_1618_,
                                        v___y_1619_,
                                        v___y_1620_,
                                        v___y_1621_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_1652_) == 0 {
                                        v_a_1653_ = crate::leanh::lean_ctor_get(v___x_1652_, 0);
                                        crate::leanh::lean_inc(v_a_1653_);
                                        crate::leanh::lean_dec_ref_known(v___x_1652_, 1);
                                        v_fst_1654_ = crate::leanh::lean_ctor_get(v_a_1653_, 0);
                                        v_isSharedCheck_1809_ =
                                            (!crate::leanh::lean_is_exclusive(v_a_1653_)) as u8;
                                        if v_isSharedCheck_1809_ == 0 {
                                            v_unused_1810_ =
                                                crate::leanh::lean_ctor_get(v_a_1653_, 1);
                                            crate::leanh::lean_dec(v_unused_1810_);
                                            v___x_1656_ = v_a_1653_;
                                            v_isShared_1657_ = v_isSharedCheck_1809_;
                                            state = 2;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_fst_1654_);
                                            crate::leanh::lean_dec(v_a_1653_);
                                            v___x_1656_ = crate::leanh::lean_box(0);
                                            v_isShared_1657_ = v_isSharedCheck_1809_;
                                            state = 2;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_a_1644_);
                                        crate::leanh::lean_dec(v___x_1613_);
                                        v_a_1811_ = crate::leanh::lean_ctor_get(v___x_1652_, 0);
                                        v_isSharedCheck_1818_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_1652_)) as u8;
                                        if v_isSharedCheck_1818_ == 0 {
                                            v___x_1813_ = v___x_1652_;
                                            v_isShared_1814_ = v_isSharedCheck_1818_;
                                            state = 24;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_1811_);
                                            crate::leanh::lean_dec(v___x_1652_);
                                            v___x_1813_ = crate::leanh::lean_box(0);
                                            v_isShared_1814_ = v_isSharedCheck_1818_;
                                            state = 24;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_1641_);
                                    crate::leanh::lean_dec(v___x_1613_);
                                    crate::leanh::lean_dec(v___x_1612_);
                                    crate::leanh::lean_dec_ref(v___f_1611_);
                                    v_a_1819_ = crate::leanh::lean_ctor_get(v___x_1643_, 0);
                                    v_isSharedCheck_1826_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1643_)) as u8;
                                    if v_isSharedCheck_1826_ == 0 {
                                        v___x_1821_ = v___x_1643_;
                                        v_isShared_1822_ = v_isSharedCheck_1826_;
                                        state = 26;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_1819_);
                                        crate::leanh::lean_dec(v___x_1643_);
                                        v___x_1821_ = crate::leanh::lean_box(0);
                                        v_isShared_1822_ = v_isSharedCheck_1826_;
                                        state = 26;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_1634_);
                                crate::leanh::lean_dec(v___x_1613_);
                                crate::leanh::lean_dec(v___x_1612_);
                                crate::leanh::lean_dec_ref(v___f_1611_);
                                crate::leanh::lean_dec(v___x_1610_);
                                v_a_1827_ = crate::leanh::lean_ctor_get(v___x_1640_, 0);
                                v_isSharedCheck_1834_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1640_)) as u8;
                                if v_isSharedCheck_1834_ == 0 {
                                    v___x_1829_ = v___x_1640_;
                                    v_isShared_1830_ = v_isSharedCheck_1834_;
                                    state = 28;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1827_);
                                    crate::leanh::lean_dec(v___x_1640_);
                                    v___x_1829_ = crate::leanh::lean_box(0);
                                    v_isShared_1830_ = v_isSharedCheck_1834_;
                                    state = 28;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_1634_);
                            crate::leanh::lean_dec(v___x_1613_);
                            crate::leanh::lean_dec(v___x_1612_);
                            crate::leanh::lean_dec_ref(v___f_1611_);
                            crate::leanh::lean_dec(v___x_1610_);
                            v_a_1835_ = crate::leanh::lean_ctor_get(v___x_1635_, 0);
                            v_isSharedCheck_1842_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1635_)) as u8;
                            if v_isSharedCheck_1842_ == 0 {
                                v___x_1837_ = v___x_1635_;
                                v_isShared_1838_ = v_isSharedCheck_1842_;
                                state = 30;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1835_);
                                crate::leanh::lean_dec(v___x_1635_);
                                v___x_1837_ = crate::leanh::lean_box(0);
                                v_isShared_1838_ = v_isSharedCheck_1842_;
                                state = 30;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_1632_);
                        crate::leanh::lean_dec(v___x_1613_);
                        crate::leanh::lean_dec(v___x_1612_);
                        crate::leanh::lean_dec_ref(v___f_1611_);
                        crate::leanh::lean_dec(v___x_1610_);
                        v_a_1843_ = crate::leanh::lean_ctor_get(v___x_1633_, 0);
                        v_isSharedCheck_1850_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1633_)) as u8;
                        if v_isSharedCheck_1850_ == 0 {
                            v___x_1845_ = v___x_1633_;
                            v_isShared_1846_ = v_isSharedCheck_1850_;
                            state = 32;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1843_);
                            crate::leanh::lean_dec(v___x_1633_);
                            v___x_1845_ = crate::leanh::lean_box(0);
                            v_isShared_1846_ = v_isSharedCheck_1850_;
                            state = 32;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1613_);
                    crate::leanh::lean_dec(v___x_1612_);
                    crate::leanh::lean_dec_ref(v___f_1611_);
                    crate::leanh::lean_dec(v___x_1610_);
                    v_a_1851_ = crate::leanh::lean_ctor_get(v___x_1631_, 0);
                    v_isSharedCheck_1858_ = (!crate::leanh::lean_is_exclusive(v___x_1631_)) as u8;
                    if v_isSharedCheck_1858_ == 0 {
                        v___x_1853_ = v___x_1631_;
                        v_isShared_1854_ = v_isSharedCheck_1858_;
                        state = 34;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1851_);
                        crate::leanh::lean_dec(v___x_1631_);
                        v___x_1853_ = crate::leanh::lean_box(0);
                        v_isShared_1854_ = v_isSharedCheck_1858_;
                        state = 34;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1624_ = crate::leanh::lean_box(0);
                v___x_1625_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1625_, 0, v___x_1624_);
                return v___x_1625_;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_fst_1654_) == 0 {
                    v___x_1658_ = l_Lean_MessageData_ofSyntax(v___x_1613_);
                    v___x_1659_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__2_once
                        ),
                        _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__2,
                    );
                    if v_isShared_1657_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_1656_, 7);
                        crate::leanh::lean_ctor_set(v___x_1656_, 1, v___x_1659_);
                        crate::leanh::lean_ctor_set(v___x_1656_, 0, v___x_1658_);
                        v___x_1661_ = v___x_1656_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1667_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1667_, 0, v___x_1658_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1667_, 1, v___x_1659_);
                        v___x_1661_ = v_reuseFailAlloc_1667_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_tail_1668_ = crate::leanh::lean_ctor_get(v_fst_1654_, 1);
                    if crate::leanh::lean_obj_tag(v_tail_1668_) == 0 {
                        crate::leanh::lean_del_object(v___x_1656_);
                        crate::leanh::lean_dec(v___x_1613_);
                        v_head_1669_ = crate::leanh::lean_ctor_get(v_fst_1654_, 0);
                        v_isSharedCheck_1789_ =
                            (!crate::leanh::lean_is_exclusive(v_fst_1654_)) as u8;
                        if v_isSharedCheck_1789_ == 0 {
                            v_unused_1790_ = crate::leanh::lean_ctor_get(v_fst_1654_, 1);
                            crate::leanh::lean_dec(v_unused_1790_);
                            v___x_1671_ = v_fst_1654_;
                            v_isShared_1672_ = v_isSharedCheck_1789_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_head_1669_);
                            crate::leanh::lean_dec(v_fst_1654_);
                            v___x_1671_ = crate::leanh::lean_box(0);
                            v_isShared_1672_ = v_isSharedCheck_1789_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v_isSharedCheck_1806_ =
                            (!crate::leanh::lean_is_exclusive(v_fst_1654_)) as u8;
                        if v_isSharedCheck_1806_ == 0 {
                            v_unused_1807_ = crate::leanh::lean_ctor_get(v_fst_1654_, 1);
                            crate::leanh::lean_dec(v_unused_1807_);
                            v_unused_1808_ = crate::leanh::lean_ctor_get(v_fst_1654_, 0);
                            crate::leanh::lean_dec(v_unused_1808_);
                            v___x_1792_ = v_fst_1654_;
                            v_isShared_1793_ = v_isSharedCheck_1806_;
                            state = 21;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_fst_1654_);
                            v___x_1792_ = crate::leanh::lean_box(0);
                            v_isShared_1793_ = v_isSharedCheck_1806_;
                            state = 21;
                            continue;
                        }
                    }
                }
            }
            3 => {
                v___x_1662_ = l_Lean_indentExpr(v_a_1644_);
                v___x_1663_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1663_, 0, v___x_1661_);
                crate::leanh::lean_ctor_set(v___x_1663_, 1, v___x_1662_);
                v___x_1664_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__4
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__4_once
                    ),
                    _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__4,
                );
                v___x_1665_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1665_, 0, v___x_1663_);
                crate::leanh::lean_ctor_set(v___x_1665_, 1, v___x_1664_);
                v___x_1666_ = l_Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg(v_stx_1614_, v___x_1665_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_);
                return v___x_1666_;
            }
            4 => {
                v___x_1673_ = l_Lean_MVarId_getType(
                    v_head_1669_,
                    v___y_1618_,
                    v___y_1619_,
                    v___y_1620_,
                    v___y_1621_,
                );
                if crate::leanh::lean_obj_tag(v___x_1673_) == 0 {
                    v_a_1674_ = crate::leanh::lean_ctor_get(v___x_1673_, 0);
                    crate::leanh::lean_inc(v_a_1674_);
                    crate::leanh::lean_dec_ref_known(v___x_1673_, 1);
                    v___x_1675_ = l_Lean_Meta_CheckTactic_matchCheckGoalType(
                        v_stx_1614_,
                        v_a_1674_,
                        v___y_1618_,
                        v___y_1619_,
                        v___y_1620_,
                        v___y_1621_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1675_) == 0 {
                        v_a_1676_ = crate::leanh::lean_ctor_get(v___x_1675_, 0);
                        crate::leanh::lean_inc(v_a_1676_);
                        crate::leanh::lean_dec_ref_known(v___x_1675_, 1);
                        v_fst_1677_ = crate::leanh::lean_ctor_get(v_a_1676_, 0);
                        v_isSharedCheck_1771_ = (!crate::leanh::lean_is_exclusive(v_a_1676_)) as u8;
                        if v_isSharedCheck_1771_ == 0 {
                            v_unused_1772_ = crate::leanh::lean_ctor_get(v_a_1676_, 1);
                            crate::leanh::lean_dec(v_unused_1772_);
                            v___x_1679_ = v_a_1676_;
                            v_isShared_1680_ = v_isSharedCheck_1771_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_fst_1677_);
                            crate::leanh::lean_dec(v_a_1676_);
                            v___x_1679_ = crate::leanh::lean_box(0);
                            v_isShared_1680_ = v_isSharedCheck_1771_;
                            state = 5;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_1671_);
                        crate::leanh::lean_dec(v_a_1644_);
                        v_a_1773_ = crate::leanh::lean_ctor_get(v___x_1675_, 0);
                        v_isSharedCheck_1780_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1675_)) as u8;
                        if v_isSharedCheck_1780_ == 0 {
                            v___x_1775_ = v___x_1675_;
                            v_isShared_1776_ = v_isSharedCheck_1780_;
                            state = 17;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1773_);
                            crate::leanh::lean_dec(v___x_1675_);
                            v___x_1775_ = crate::leanh::lean_box(0);
                            v_isShared_1776_ = v_isSharedCheck_1780_;
                            state = 17;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1671_);
                    crate::leanh::lean_dec(v_a_1644_);
                    v_a_1781_ = crate::leanh::lean_ctor_get(v___x_1673_, 0);
                    v_isSharedCheck_1788_ = (!crate::leanh::lean_is_exclusive(v___x_1673_)) as u8;
                    if v_isSharedCheck_1788_ == 0 {
                        v___x_1783_ = v___x_1673_;
                        v_isShared_1784_ = v_isSharedCheck_1788_;
                        state = 19;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1781_);
                        crate::leanh::lean_dec(v___x_1673_);
                        v___x_1783_ = crate::leanh::lean_box(0);
                        v_isShared_1784_ = v_isSharedCheck_1788_;
                        state = 19;
                        continue;
                    }
                }
            }
            5 => {
                v___x_1713_ = l_Lean_Meta_Context_config(v___y_1618_);
                v_foApprox_1714_ = crate::leanh::lean_ctor_get_uint8(v___x_1713_, 0 as u32);
                v_ctxApprox_1715_ = crate::leanh::lean_ctor_get_uint8(v___x_1713_, 1 as u32);
                v_quasiPatternApprox_1716_ =
                    crate::leanh::lean_ctor_get_uint8(v___x_1713_, 2 as u32);
                v_constApprox_1717_ = crate::leanh::lean_ctor_get_uint8(v___x_1713_, 3 as u32);
                v_isDefEqStuckEx_1718_ = crate::leanh::lean_ctor_get_uint8(v___x_1713_, 4 as u32);
                v_unificationHints_1719_ = crate::leanh::lean_ctor_get_uint8(v___x_1713_, 5 as u32);
                v_proofIrrelevance_1720_ = crate::leanh::lean_ctor_get_uint8(v___x_1713_, 6 as u32);
                v_assignSyntheticOpaque_1721_ =
                    crate::leanh::lean_ctor_get_uint8(v___x_1713_, 7 as u32);
                v_offsetCnstrs_1722_ = crate::leanh::lean_ctor_get_uint8(v___x_1713_, 8 as u32);
                v_etaStruct_1723_ = crate::leanh::lean_ctor_get_uint8(v___x_1713_, 10 as u32);
                v_univApprox_1724_ = crate::leanh::lean_ctor_get_uint8(v___x_1713_, 11 as u32);
                v_iota_1725_ = crate::leanh::lean_ctor_get_uint8(v___x_1713_, 12 as u32);
                v_beta_1726_ = crate::leanh::lean_ctor_get_uint8(v___x_1713_, 13 as u32);
                v_proj_1727_ = crate::leanh::lean_ctor_get_uint8(v___x_1713_, 14 as u32);
                v_zeta_1728_ = crate::leanh::lean_ctor_get_uint8(v___x_1713_, 15 as u32);
                v_zetaDelta_1729_ = crate::leanh::lean_ctor_get_uint8(v___x_1713_, 16 as u32);
                v_zetaUnused_1730_ = crate::leanh::lean_ctor_get_uint8(v___x_1713_, 17 as u32);
                v_zetaHave_1731_ = crate::leanh::lean_ctor_get_uint8(v___x_1713_, 18 as u32);
                v_isSharedCheck_1770_ = (!crate::leanh::lean_is_exclusive(v___x_1713_)) as u8;
                if v_isSharedCheck_1770_ == 0 {
                    v___x_1733_ = v___x_1713_;
                    v_isShared_1734_ = v_isSharedCheck_1770_;
                    state = 13;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_1713_);
                    v___x_1733_ = crate::leanh::lean_box(0);
                    v_isShared_1734_ = v_isSharedCheck_1770_;
                    state = 13;
                    continue;
                }
            }
            6 => {
                if v_a_1682_ == 0 {
                    if v___x_1609_ == 0 {
                        crate::leanh::lean_del_object(v___x_1679_);
                        crate::leanh::lean_dec(v_fst_1677_);
                        crate::leanh::lean_del_object(v___x_1671_);
                        crate::leanh::lean_dec(v_a_1644_);
                        state = 1;
                        continue;
                    } else {
                        v___x_1683_ = l_Lean_Meta_addPPExplicitToExposeDiff(
                            v_fst_1677_,
                            v_a_1644_,
                            v___y_1618_,
                            v___y_1619_,
                            v___y_1620_,
                            v___y_1621_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1683_) == 0 {
                            v_a_1684_ = crate::leanh::lean_ctor_get(v___x_1683_, 0);
                            crate::leanh::lean_inc(v_a_1684_);
                            crate::leanh::lean_dec_ref_known(v___x_1683_, 1);
                            v_fst_1685_ = crate::leanh::lean_ctor_get(v_a_1684_, 0);
                            v_snd_1686_ = crate::leanh::lean_ctor_get(v_a_1684_, 1);
                            v_isSharedCheck_1704_ =
                                (!crate::leanh::lean_is_exclusive(v_a_1684_)) as u8;
                            if v_isSharedCheck_1704_ == 0 {
                                v___x_1688_ = v_a_1684_;
                                v_isShared_1689_ = v_isSharedCheck_1704_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_snd_1686_);
                                crate::leanh::lean_inc(v_fst_1685_);
                                crate::leanh::lean_dec(v_a_1684_);
                                v___x_1688_ = crate::leanh::lean_box(0);
                                v_isShared_1689_ = v_isSharedCheck_1704_;
                                state = 7;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_1679_);
                            crate::leanh::lean_del_object(v___x_1671_);
                            v_a_1705_ = crate::leanh::lean_ctor_get(v___x_1683_, 0);
                            v_isSharedCheck_1712_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1683_)) as u8;
                            if v_isSharedCheck_1712_ == 0 {
                                v___x_1707_ = v___x_1683_;
                                v_isShared_1708_ = v_isSharedCheck_1712_;
                                state = 11;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1705_);
                                crate::leanh::lean_dec(v___x_1683_);
                                v___x_1707_ = crate::leanh::lean_box(0);
                                v_isShared_1708_ = v_isSharedCheck_1712_;
                                state = 11;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1679_);
                    crate::leanh::lean_dec(v_fst_1677_);
                    crate::leanh::lean_del_object(v___x_1671_);
                    crate::leanh::lean_dec(v_a_1644_);
                    state = 1;
                    continue;
                }
            }
            7 => {
                v___x_1690_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__6
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__6_once
                    ),
                    _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__6,
                );
                v___x_1691_ = l_Lean_indentExpr(v_fst_1685_);
                if v_isShared_1689_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1688_, 7);
                    crate::leanh::lean_ctor_set(v___x_1688_, 1, v___x_1691_);
                    crate::leanh::lean_ctor_set(v___x_1688_, 0, v___x_1690_);
                    v___x_1693_ = v___x_1688_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1703_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1703_, 0, v___x_1690_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1703_, 1, v___x_1691_);
                    v___x_1693_ = v_reuseFailAlloc_1703_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_1694_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__8
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__8_once
                    ),
                    _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__8,
                );
                if v_isShared_1680_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1679_, 7);
                    crate::leanh::lean_ctor_set(v___x_1679_, 1, v___x_1694_);
                    crate::leanh::lean_ctor_set(v___x_1679_, 0, v___x_1693_);
                    v___x_1696_ = v___x_1679_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1702_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1702_, 0, v___x_1693_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1702_, 1, v___x_1694_);
                    v___x_1696_ = v_reuseFailAlloc_1702_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_1697_ = l_Lean_indentExpr(v_snd_1686_);
                if v_isShared_1672_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1671_, 7);
                    crate::leanh::lean_ctor_set(v___x_1671_, 1, v___x_1697_);
                    crate::leanh::lean_ctor_set(v___x_1671_, 0, v___x_1696_);
                    v___x_1699_ = v___x_1671_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1701_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1701_, 0, v___x_1696_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1701_, 1, v___x_1697_);
                    v___x_1699_ = v_reuseFailAlloc_1701_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_1700_ = l_Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg(v_stx_1614_, v___x_1699_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_);
                return v___x_1700_;
            }
            11 => {
                if v_isShared_1708_ == 0 {
                    v___x_1710_ = v___x_1707_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1711_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1711_, 0, v_a_1705_);
                    v___x_1710_ = v_reuseFailAlloc_1711_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1710_;
            }
            13 => {
                v_trackZetaDelta_1735_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_1618_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_1736_ = crate::leanh::lean_ctor_get(v___y_1618_, 1);
                v_lctx_1737_ = crate::leanh::lean_ctor_get(v___y_1618_, 2);
                v_localInstances_1738_ = crate::leanh::lean_ctor_get(v___y_1618_, 3);
                v_defEqCtx_x3f_1739_ = crate::leanh::lean_ctor_get(v___y_1618_, 4);
                v_synthPendingDepth_1740_ = crate::leanh::lean_ctor_get(v___y_1618_, 5);
                v_canUnfold_x3f_1741_ = crate::leanh::lean_ctor_get(v___y_1618_, 6);
                v_univApprox_1742_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_1618_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_1743_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_1618_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_1744_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_1618_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                );
                v___x_1745_ = 2;
                if v_isShared_1734_ == 0 {
                    v_config_1747_ = v___x_1733_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1769_ = crate::leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1769_,
                        0 as u32,
                        v_foApprox_1714_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1769_,
                        1 as u32,
                        v_ctxApprox_1715_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1769_,
                        2 as u32,
                        v_quasiPatternApprox_1716_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1769_,
                        3 as u32,
                        v_constApprox_1717_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1769_,
                        4 as u32,
                        v_isDefEqStuckEx_1718_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1769_,
                        5 as u32,
                        v_unificationHints_1719_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1769_,
                        6 as u32,
                        v_proofIrrelevance_1720_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1769_,
                        7 as u32,
                        v_assignSyntheticOpaque_1721_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1769_,
                        8 as u32,
                        v_offsetCnstrs_1722_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1769_,
                        10 as u32,
                        v_etaStruct_1723_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1769_,
                        11 as u32,
                        v_univApprox_1724_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1769_,
                        12 as u32,
                        v_iota_1725_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1769_,
                        13 as u32,
                        v_beta_1726_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1769_,
                        14 as u32,
                        v_proj_1727_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1769_,
                        15 as u32,
                        v_zeta_1728_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1769_,
                        16 as u32,
                        v_zetaDelta_1729_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1769_,
                        17 as u32,
                        v_zetaUnused_1730_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1769_,
                        18 as u32,
                        v_zetaHave_1731_,
                    );
                    v_config_1747_ = v_reuseFailAlloc_1769_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                crate::leanh::lean_ctor_set_uint8(v_config_1747_, 9 as u32, v___x_1745_);
                v___x_1748_ = l_Lean_Meta_Context_configKey(v___y_1618_);
                v___x_1749_ = 3u64;
                v___x_1750_ = lean_uint64_shift_right(v___x_1748_, v___x_1749_);
                v___x_1751_ = lean_uint64_shift_left(v___x_1750_, v___x_1749_);
                v___x_1752_ = crate::leanh::lean_uint64_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__9
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__9_once
                    ),
                    _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__9,
                );
                v_key_1753_ = lean_uint64_lor(v___x_1751_, v___x_1752_);
                v___x_1754_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                crate::leanh::lean_ctor_set(v___x_1754_, 0, v_config_1747_);
                crate::leanh::lean_ctor_set_uint64(
                    v___x_1754_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_key_1753_,
                );
                crate::leanh::lean_inc(v_canUnfold_x3f_1741_);
                crate::leanh::lean_inc(v_synthPendingDepth_1740_);
                crate::leanh::lean_inc(v_defEqCtx_x3f_1739_);
                crate::leanh::lean_inc_ref(v_localInstances_1738_);
                crate::leanh::lean_inc_ref(v_lctx_1737_);
                crate::leanh::lean_inc(v_zetaDeltaSet_1736_);
                v___x_1755_ = crate::leanh::lean_alloc_ctor(0, 7, (4) as u32);
                crate::leanh::lean_ctor_set(v___x_1755_, 0, v___x_1754_);
                crate::leanh::lean_ctor_set(v___x_1755_, 1, v_zetaDeltaSet_1736_);
                crate::leanh::lean_ctor_set(v___x_1755_, 2, v_lctx_1737_);
                crate::leanh::lean_ctor_set(v___x_1755_, 3, v_localInstances_1738_);
                crate::leanh::lean_ctor_set(v___x_1755_, 4, v_defEqCtx_x3f_1739_);
                crate::leanh::lean_ctor_set(v___x_1755_, 5, v_synthPendingDepth_1740_);
                crate::leanh::lean_ctor_set(v___x_1755_, 6, v_canUnfold_x3f_1741_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1755_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_1735_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1755_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_1742_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1755_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_1743_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1755_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_1744_,
                );
                crate::leanh::lean_inc(v_a_1644_);
                crate::leanh::lean_inc(v_fst_1677_);
                v___x_1756_ = l_Lean_Meta_isExprDefEq(
                    v_fst_1677_,
                    v_a_1644_,
                    v___x_1755_,
                    v___y_1619_,
                    v___y_1620_,
                    v___y_1621_,
                );
                crate::leanh::lean_dec_ref_known(v___x_1755_, 7);
                if crate::leanh::lean_obj_tag(v___x_1756_) == 0 {
                    v_a_1757_ = crate::leanh::lean_ctor_get(v___x_1756_, 0);
                    crate::leanh::lean_inc(v_a_1757_);
                    crate::leanh::lean_dec_ref_known(v___x_1756_, 1);
                    v___x_1758_ = (crate::leanh::lean_unbox(v_a_1757_) as u8);
                    crate::leanh::lean_dec(v_a_1757_);
                    v_a_1682_ = v___x_1758_;
                    state = 6;
                    continue;
                } else {
                    if crate::leanh::lean_obj_tag(v___x_1756_) == 0 {
                        v_a_1759_ = crate::leanh::lean_ctor_get(v___x_1756_, 0);
                        crate::leanh::lean_inc(v_a_1759_);
                        crate::leanh::lean_dec_ref_known(v___x_1756_, 1);
                        v___x_1760_ = (crate::leanh::lean_unbox(v_a_1759_) as u8);
                        crate::leanh::lean_dec(v_a_1759_);
                        v_a_1682_ = v___x_1760_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_del_object(v___x_1679_);
                        crate::leanh::lean_dec(v_fst_1677_);
                        crate::leanh::lean_del_object(v___x_1671_);
                        crate::leanh::lean_dec(v_a_1644_);
                        v_a_1761_ = crate::leanh::lean_ctor_get(v___x_1756_, 0);
                        v_isSharedCheck_1768_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1756_)) as u8;
                        if v_isSharedCheck_1768_ == 0 {
                            v___x_1763_ = v___x_1756_;
                            v_isShared_1764_ = v_isSharedCheck_1768_;
                            state = 15;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1761_);
                            crate::leanh::lean_dec(v___x_1756_);
                            v___x_1763_ = crate::leanh::lean_box(0);
                            v_isShared_1764_ = v_isSharedCheck_1768_;
                            state = 15;
                            continue;
                        }
                    }
                }
            }
            15 => {
                if v_isShared_1764_ == 0 {
                    v___x_1766_ = v___x_1763_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1767_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1767_, 0, v_a_1761_);
                    v___x_1766_ = v_reuseFailAlloc_1767_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_1766_;
            }
            17 => {
                if v_isShared_1776_ == 0 {
                    v___x_1778_ = v___x_1775_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_1779_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1779_, 0, v_a_1773_);
                    v___x_1778_ = v_reuseFailAlloc_1779_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_1778_;
            }
            19 => {
                if v_isShared_1784_ == 0 {
                    v___x_1786_ = v___x_1783_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_1787_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1787_, 0, v_a_1781_);
                    v___x_1786_ = v_reuseFailAlloc_1787_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_1786_;
            }
            21 => {
                v___x_1794_ = l_Lean_MessageData_ofSyntax(v___x_1613_);
                v___x_1795_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__11
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__11_once
                    ),
                    _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__11,
                );
                if v_isShared_1793_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1792_, 7);
                    crate::leanh::lean_ctor_set(v___x_1792_, 1, v___x_1795_);
                    crate::leanh::lean_ctor_set(v___x_1792_, 0, v___x_1794_);
                    v___x_1797_ = v___x_1792_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_1805_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1805_, 0, v___x_1794_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1805_, 1, v___x_1795_);
                    v___x_1797_ = v_reuseFailAlloc_1805_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                v___x_1798_ = l_Lean_indentExpr(v_a_1644_);
                if v_isShared_1657_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1656_, 7);
                    crate::leanh::lean_ctor_set(v___x_1656_, 1, v___x_1798_);
                    crate::leanh::lean_ctor_set(v___x_1656_, 0, v___x_1797_);
                    v___x_1800_ = v___x_1656_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_1804_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1804_, 0, v___x_1797_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1804_, 1, v___x_1798_);
                    v___x_1800_ = v_reuseFailAlloc_1804_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                v___x_1801_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__4
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__4_once
                    ),
                    _init_l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__4,
                );
                v___x_1802_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1802_, 0, v___x_1800_);
                crate::leanh::lean_ctor_set(v___x_1802_, 1, v___x_1801_);
                v___x_1803_ = l_Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg(v_stx_1614_, v___x_1802_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_);
                return v___x_1803_;
            }
            24 => {
                if v_isShared_1814_ == 0 {
                    v___x_1816_ = v___x_1813_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_1817_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1817_, 0, v_a_1811_);
                    v___x_1816_ = v_reuseFailAlloc_1817_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_1816_;
            }
            26 => {
                if v_isShared_1822_ == 0 {
                    v___x_1824_ = v___x_1821_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_1825_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1825_, 0, v_a_1819_);
                    v___x_1824_ = v_reuseFailAlloc_1825_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_1824_;
            }
            28 => {
                if v_isShared_1830_ == 0 {
                    v___x_1832_ = v___x_1829_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_1833_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1833_, 0, v_a_1827_);
                    v___x_1832_ = v_reuseFailAlloc_1833_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_1832_;
            }
            30 => {
                if v_isShared_1838_ == 0 {
                    v___x_1840_ = v___x_1837_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_1841_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1841_, 0, v_a_1835_);
                    v___x_1840_ = v_reuseFailAlloc_1841_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_1840_;
            }
            32 => {
                if v_isShared_1846_ == 0 {
                    v___x_1848_ = v___x_1845_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_1849_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1849_, 0, v_a_1843_);
                    v___x_1848_ = v_reuseFailAlloc_1849_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_1848_;
            }
            34 => {
                if v_isShared_1854_ == 0 {
                    v___x_1856_ = v___x_1853_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_1857_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1857_, 0, v_a_1851_);
                    v___x_1856_ = v_reuseFailAlloc_1857_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                return v___x_1856_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___boxed(
    mut v___x_1859_: *mut crate::leanh::LeanObject,
    mut v___x_1860_: *mut crate::leanh::LeanObject,
    mut v___x_1861_: *mut crate::leanh::LeanObject,
    mut v___f_1862_: *mut crate::leanh::LeanObject,
    mut v___x_1863_: *mut crate::leanh::LeanObject,
    mut v___x_1864_: *mut crate::leanh::LeanObject,
    mut v_stx_1865_: *mut crate::leanh::LeanObject,
    mut v___vars_1866_: *mut crate::leanh::LeanObject,
    mut v___y_1867_: *mut crate::leanh::LeanObject,
    mut v___y_1868_: *mut crate::leanh::LeanObject,
    mut v___y_1869_: *mut crate::leanh::LeanObject,
    mut v___y_1870_: *mut crate::leanh::LeanObject,
    mut v___y_1871_: *mut crate::leanh::LeanObject,
    mut v___y_1872_: *mut crate::leanh::LeanObject,
    mut v___y_1873_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_11873__boxed_1874_: u8 = 0;
    let mut v_res_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_11873__boxed_1874_ = (crate::leanh::lean_unbox(v___x_1860_) as u8);
    v_res_1875_ = l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1(
        v___x_1859_,
        v___x_11873__boxed_1874_,
        v___x_1861_,
        v___f_1862_,
        v___x_1863_,
        v___x_1864_,
        v_stx_1865_,
        v___vars_1866_,
        v___y_1867_,
        v___y_1868_,
        v___y_1869_,
        v___y_1870_,
        v___y_1871_,
        v___y_1872_,
    );
    crate::leanh::lean_dec(v___y_1872_);
    crate::leanh::lean_dec_ref(v___y_1871_);
    crate::leanh::lean_dec(v___y_1870_);
    crate::leanh::lean_dec_ref(v___y_1869_);
    crate::leanh::lean_dec(v___y_1868_);
    crate::leanh::lean_dec_ref(v___y_1867_);
    crate::leanh::lean_dec_ref(v___vars_1866_);
    crate::leanh::lean_dec(v_stx_1865_);
    return v_res_1875_;
}
pub unsafe fn l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2_spec__3___redArg(
    mut v_env_1876_: *mut crate::leanh::LeanObject,
    mut v___y_1877_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1892_: u8 = 0;
    let mut v___x_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1899_: u8 = 0;
    let mut v_unused_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1879_ = lean_st_ref_take(v___y_1877_);
                v_messages_1880_ = crate::leanh::lean_ctor_get(v___x_1879_, 1);
                v_scopes_1881_ = crate::leanh::lean_ctor_get(v___x_1879_, 2);
                v_usedQuotCtxts_1882_ = crate::leanh::lean_ctor_get(v___x_1879_, 3);
                v_nextMacroScope_1883_ = crate::leanh::lean_ctor_get(v___x_1879_, 4);
                v_maxRecDepth_1884_ = crate::leanh::lean_ctor_get(v___x_1879_, 5);
                v_ngen_1885_ = crate::leanh::lean_ctor_get(v___x_1879_, 6);
                v_auxDeclNGen_1886_ = crate::leanh::lean_ctor_get(v___x_1879_, 7);
                v_infoState_1887_ = crate::leanh::lean_ctor_get(v___x_1879_, 8);
                v_traceState_1888_ = crate::leanh::lean_ctor_get(v___x_1879_, 9);
                v_snapshotTasks_1889_ = crate::leanh::lean_ctor_get(v___x_1879_, 10);
                v_isSharedCheck_1899_ = (!crate::leanh::lean_is_exclusive(v___x_1879_)) as u8;
                if v_isSharedCheck_1899_ == 0 {
                    v_unused_1900_ = crate::leanh::lean_ctor_get(v___x_1879_, 0);
                    crate::leanh::lean_dec(v_unused_1900_);
                    v___x_1891_ = v___x_1879_;
                    v_isShared_1892_ = v_isSharedCheck_1899_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_1889_);
                    crate::leanh::lean_inc(v_traceState_1888_);
                    crate::leanh::lean_inc(v_infoState_1887_);
                    crate::leanh::lean_inc(v_auxDeclNGen_1886_);
                    crate::leanh::lean_inc(v_ngen_1885_);
                    crate::leanh::lean_inc(v_maxRecDepth_1884_);
                    crate::leanh::lean_inc(v_nextMacroScope_1883_);
                    crate::leanh::lean_inc(v_usedQuotCtxts_1882_);
                    crate::leanh::lean_inc(v_scopes_1881_);
                    crate::leanh::lean_inc(v_messages_1880_);
                    crate::leanh::lean_dec(v___x_1879_);
                    v___x_1891_ = crate::leanh::lean_box(0);
                    v_isShared_1892_ = v_isSharedCheck_1899_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1892_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1891_, 0, v_env_1876_);
                    v___x_1894_ = v___x_1891_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1898_ = crate::leanh::lean_alloc_ctor(0, 11, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1898_, 0, v_env_1876_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1898_, 1, v_messages_1880_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1898_, 2, v_scopes_1881_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1898_, 3, v_usedQuotCtxts_1882_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1898_, 4, v_nextMacroScope_1883_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1898_, 5, v_maxRecDepth_1884_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1898_, 6, v_ngen_1885_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1898_, 7, v_auxDeclNGen_1886_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1898_, 8, v_infoState_1887_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1898_, 9, v_traceState_1888_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1898_, 10, v_snapshotTasks_1889_);
                    v___x_1894_ = v_reuseFailAlloc_1898_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1895_ = lean_st_ref_set(v___y_1877_, v___x_1894_);
                v___x_1896_ = crate::leanh::lean_box(0);
                v___x_1897_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1897_, 0, v___x_1896_);
                return v___x_1897_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2_spec__3___redArg___boxed(
    mut v_env_1901_: *mut crate::leanh::LeanObject,
    mut v___y_1902_: *mut crate::leanh::LeanObject,
    mut v___y_1903_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1904_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2_spec__3___redArg(v_env_1901_, v___y_1902_);
    crate::leanh::lean_dec(v___y_1902_);
    return v_res_1904_;
}
pub unsafe fn l_Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2___redArg(
    mut v_env_1905_: *mut crate::leanh::LeanObject,
    mut v_x_1906_: *mut crate::leanh::LeanObject,
    mut v___y_1907_: *mut crate::leanh::LeanObject,
    mut v___y_1908_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1917_: u8 = 0;
    let mut v___x_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1921_: u8 = 0;
    let mut v_unused_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1929_: u8 = 0;
    let mut v___x_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1933_: u8 = 0;
    let mut v_unused_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1910_ = lean_st_ref_get(v___y_1908_);
                v_env_1911_ = crate::leanh::lean_ctor_get(v___x_1910_, 0);
                crate::leanh::lean_inc_ref(v_env_1911_);
                crate::leanh::lean_dec(v___x_1910_);
                v___x_1923_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2_spec__3___redArg(v_env_1905_, v___y_1908_);
                crate::leanh::lean_dec_ref(v___x_1923_);
                crate::leanh::lean_inc(v___y_1908_);
                crate::leanh::lean_inc_ref(v___y_1907_);
                v___x_1924_ = crate::leanh::lean_apply_3(
                    v_x_1906_,
                    v___y_1907_,
                    v___y_1908_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_1924_) == 0 {
                    v_a_1925_ = crate::leanh::lean_ctor_get(v___x_1924_, 0);
                    crate::leanh::lean_inc(v_a_1925_);
                    crate::leanh::lean_dec_ref_known(v___x_1924_, 1);
                    v___x_1926_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2_spec__3___redArg(v_env_1911_, v___y_1908_);
                    v_isSharedCheck_1933_ = (!crate::leanh::lean_is_exclusive(v___x_1926_)) as u8;
                    if v_isSharedCheck_1933_ == 0 {
                        v_unused_1934_ = crate::leanh::lean_ctor_get(v___x_1926_, 0);
                        crate::leanh::lean_dec(v_unused_1934_);
                        v___x_1928_ = v___x_1926_;
                        v_isShared_1929_ = v_isSharedCheck_1933_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_1926_);
                        v___x_1928_ = crate::leanh::lean_box(0);
                        v_isShared_1929_ = v_isSharedCheck_1933_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_1935_ = crate::leanh::lean_ctor_get(v___x_1924_, 0);
                    crate::leanh::lean_inc(v_a_1935_);
                    crate::leanh::lean_dec_ref_known(v___x_1924_, 1);
                    v_a_1913_ = v_a_1935_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1914_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2_spec__3___redArg(v_env_1911_, v___y_1908_);
                v_isSharedCheck_1921_ = (!crate::leanh::lean_is_exclusive(v___x_1914_)) as u8;
                if v_isSharedCheck_1921_ == 0 {
                    v_unused_1922_ = crate::leanh::lean_ctor_get(v___x_1914_, 0);
                    crate::leanh::lean_dec(v_unused_1922_);
                    v___x_1916_ = v___x_1914_;
                    v_isShared_1917_ = v_isSharedCheck_1921_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_1914_);
                    v___x_1916_ = crate::leanh::lean_box(0);
                    v_isShared_1917_ = v_isSharedCheck_1921_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_1917_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1916_, 1);
                    crate::leanh::lean_ctor_set(v___x_1916_, 0, v_a_1913_);
                    v___x_1919_ = v___x_1916_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1920_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1920_, 0, v_a_1913_);
                    v___x_1919_ = v_reuseFailAlloc_1920_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1919_;
            }
            4 => {
                if v_isShared_1929_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1928_, 0, v_a_1925_);
                    v___x_1931_ = v___x_1928_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1932_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1932_, 0, v_a_1925_);
                    v___x_1931_ = v_reuseFailAlloc_1932_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1931_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2___redArg___boxed(
    mut v_env_1936_: *mut crate::leanh::LeanObject,
    mut v_x_1937_: *mut crate::leanh::LeanObject,
    mut v___y_1938_: *mut crate::leanh::LeanObject,
    mut v___y_1939_: *mut crate::leanh::LeanObject,
    mut v___y_1940_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1941_ = l_Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2___redArg(
        v_env_1936_,
        v_x_1937_,
        v___y_1938_,
        v___y_1939_,
    );
    crate::leanh::lean_dec(v___y_1939_);
    crate::leanh::lean_dec_ref(v___y_1938_);
    return v_res_1941_;
}
pub unsafe fn l_Lean_Elab_CheckTactic_elabCheckTactic(
    mut v_stx_1950_: *mut crate::leanh::LeanObject,
    mut v_a_1951_: *mut crate::leanh::LeanObject,
    mut v_a_1952_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: u8 = 0;
    v___x_1954_ = l_Lean_Elab_CheckTactic_elabCheckTactic___closed__3;
    crate::leanh::lean_inc(v_stx_1950_);
    v___x_1955_ = l_Lean_Syntax_isOfKind(v_stx_1950_, v___x_1954_);
    if v___x_1955_ == 0 {
        let mut v___x_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_stx_1950_);
        v___x_1956_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__0___redArg();
        return v___x_1956_;
    } else {
        let mut v___x_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_env_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1957_ = lean_st_ref_get(v_a_1952_);
        v_env_1958_ = crate::leanh::lean_ctor_get(v___x_1957_, 0);
        crate::leanh::lean_inc_ref(v_env_1958_);
        crate::leanh::lean_dec(v___x_1957_);
        v___f_1959_ = l_Lean_Elab_CheckTactic_elabCheckTactic___closed__4;
        v___x_1960_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_1961_ = l_Lean_Syntax_getArg(v_stx_1950_, v___x_1960_);
        v___x_1962_ = crate::leanh::lean_unsigned_to_nat(3);
        v___x_1963_ = l_Lean_Syntax_getArg(v_stx_1950_, v___x_1962_);
        v___x_1964_ = crate::leanh::lean_unsigned_to_nat(5);
        v___x_1965_ = l_Lean_Syntax_getArg(v_stx_1950_, v___x_1964_);
        v___x_1966_ = crate::leanh::lean_box(0);
        v___x_1967_ = crate::leanh::lean_box((v___x_1955_) as usize);
        v___f_1968_ = crate::leanh::lean_alloc_closure(
            l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___boxed as *mut core::ffi::c_void,
            15,
            7,
        );
        crate::leanh::lean_closure_set(v___f_1968_, 0, v___x_1961_);
        crate::leanh::lean_closure_set(v___f_1968_, 1, v___x_1967_);
        crate::leanh::lean_closure_set(v___f_1968_, 2, v___x_1963_);
        crate::leanh::lean_closure_set(v___f_1968_, 3, v___f_1959_);
        crate::leanh::lean_closure_set(v___f_1968_, 4, v___x_1966_);
        crate::leanh::lean_closure_set(v___f_1968_, 5, v___x_1965_);
        crate::leanh::lean_closure_set(v___f_1968_, 6, v_stx_1950_);
        v___x_1969_ = crate::leanh::lean_alloc_closure(
            l_Lean_Elab_Command_runTermElabM___boxed as *mut core::ffi::c_void,
            5,
            2,
        );
        crate::leanh::lean_closure_set(v___x_1969_, 0, crate::leanh::lean_box(0));
        crate::leanh::lean_closure_set(v___x_1969_, 1, v___f_1968_);
        v___x_1970_ = l_Lean_Environment_unlockAsync(v_env_1958_);
        v___x_1971_ =
            l_Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2___redArg(
                v___x_1970_,
                v___x_1969_,
                v_a_1951_,
                v_a_1952_,
            );
        return v___x_1971_;
    }
}
pub unsafe fn l_Lean_Elab_CheckTactic_elabCheckTactic___boxed(
    mut v_stx_1972_: *mut crate::leanh::LeanObject,
    mut v_a_1973_: *mut crate::leanh::LeanObject,
    mut v_a_1974_: *mut crate::leanh::LeanObject,
    mut v_a_1975_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1976_ = l_Lean_Elab_CheckTactic_elabCheckTactic(v_stx_1972_, v_a_1973_, v_a_1974_);
    crate::leanh::lean_dec(v_a_1974_);
    crate::leanh::lean_dec_ref(v_a_1973_);
    return v_res_1976_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1(
    mut v_00_u03b1_1977_: *mut crate::leanh::LeanObject,
    mut v_ref_1978_: *mut crate::leanh::LeanObject,
    mut v_msg_1979_: *mut crate::leanh::LeanObject,
    mut v___y_1980_: *mut crate::leanh::LeanObject,
    mut v___y_1981_: *mut crate::leanh::LeanObject,
    mut v___y_1982_: *mut crate::leanh::LeanObject,
    mut v___y_1983_: *mut crate::leanh::LeanObject,
    mut v___y_1984_: *mut crate::leanh::LeanObject,
    mut v___y_1985_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1987_ =
        l_Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg(
            v_ref_1978_,
            v_msg_1979_,
            v___y_1980_,
            v___y_1981_,
            v___y_1982_,
            v___y_1983_,
            v___y_1984_,
            v___y_1985_,
        );
    return v___x_1987_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1___boxed(
    mut v_00_u03b1_1988_: *mut crate::leanh::LeanObject,
    mut v_ref_1989_: *mut crate::leanh::LeanObject,
    mut v_msg_1990_: *mut crate::leanh::LeanObject,
    mut v___y_1991_: *mut crate::leanh::LeanObject,
    mut v___y_1992_: *mut crate::leanh::LeanObject,
    mut v___y_1993_: *mut crate::leanh::LeanObject,
    mut v___y_1994_: *mut crate::leanh::LeanObject,
    mut v___y_1995_: *mut crate::leanh::LeanObject,
    mut v___y_1996_: *mut crate::leanh::LeanObject,
    mut v___y_1997_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1998_ = l_Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1(
        v_00_u03b1_1988_,
        v_ref_1989_,
        v_msg_1990_,
        v___y_1991_,
        v___y_1992_,
        v___y_1993_,
        v___y_1994_,
        v___y_1995_,
        v___y_1996_,
    );
    crate::leanh::lean_dec(v___y_1996_);
    crate::leanh::lean_dec_ref(v___y_1995_);
    crate::leanh::lean_dec(v___y_1994_);
    crate::leanh::lean_dec_ref(v___y_1993_);
    crate::leanh::lean_dec(v___y_1992_);
    crate::leanh::lean_dec_ref(v___y_1991_);
    crate::leanh::lean_dec(v_ref_1989_);
    return v_res_1998_;
}
pub unsafe fn l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2_spec__3(
    mut v_env_1999_: *mut crate::leanh::LeanObject,
    mut v___y_2000_: *mut crate::leanh::LeanObject,
    mut v___y_2001_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2003_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2_spec__3___redArg(v_env_1999_, v___y_2001_);
    return v___x_2003_;
}
pub unsafe fn l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2_spec__3___boxed(
    mut v_env_2004_: *mut crate::leanh::LeanObject,
    mut v___y_2005_: *mut crate::leanh::LeanObject,
    mut v___y_2006_: *mut crate::leanh::LeanObject,
    mut v___y_2007_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2008_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2_spec__3(v_env_2004_, v___y_2005_, v___y_2006_);
    crate::leanh::lean_dec(v___y_2006_);
    crate::leanh::lean_dec_ref(v___y_2005_);
    return v_res_2008_;
}
pub unsafe fn l_Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2(
    mut v_00_u03b1_2009_: *mut crate::leanh::LeanObject,
    mut v_env_2010_: *mut crate::leanh::LeanObject,
    mut v_x_2011_: *mut crate::leanh::LeanObject,
    mut v___y_2012_: *mut crate::leanh::LeanObject,
    mut v___y_2013_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2015_ = l_Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2___redArg(
        v_env_2010_,
        v_x_2011_,
        v___y_2012_,
        v___y_2013_,
    );
    return v___x_2015_;
}
pub unsafe fn l_Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2___boxed(
    mut v_00_u03b1_2016_: *mut crate::leanh::LeanObject,
    mut v_env_2017_: *mut crate::leanh::LeanObject,
    mut v_x_2018_: *mut crate::leanh::LeanObject,
    mut v___y_2019_: *mut crate::leanh::LeanObject,
    mut v___y_2020_: *mut crate::leanh::LeanObject,
    mut v___y_2021_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2022_ = l_Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2(
        v_00_u03b1_2016_,
        v_env_2017_,
        v_x_2018_,
        v___y_2019_,
        v___y_2020_,
    );
    crate::leanh::lean_dec(v___y_2020_);
    crate::leanh::lean_dec_ref(v___y_2019_);
    return v_res_2022_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1(
    mut v_00_u03b1_2023_: *mut crate::leanh::LeanObject,
    mut v_msg_2024_: *mut crate::leanh::LeanObject,
    mut v___y_2025_: *mut crate::leanh::LeanObject,
    mut v___y_2026_: *mut crate::leanh::LeanObject,
    mut v___y_2027_: *mut crate::leanh::LeanObject,
    mut v___y_2028_: *mut crate::leanh::LeanObject,
    mut v___y_2029_: *mut crate::leanh::LeanObject,
    mut v___y_2030_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2032_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1___redArg(v_msg_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_);
    return v___x_2032_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1___boxed(
    mut v_00_u03b1_2033_: *mut crate::leanh::LeanObject,
    mut v_msg_2034_: *mut crate::leanh::LeanObject,
    mut v___y_2035_: *mut crate::leanh::LeanObject,
    mut v___y_2036_: *mut crate::leanh::LeanObject,
    mut v___y_2037_: *mut crate::leanh::LeanObject,
    mut v___y_2038_: *mut crate::leanh::LeanObject,
    mut v___y_2039_: *mut crate::leanh::LeanObject,
    mut v___y_2040_: *mut crate::leanh::LeanObject,
    mut v___y_2041_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2042_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1(v_00_u03b1_2033_, v_msg_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_);
    crate::leanh::lean_dec(v___y_2040_);
    crate::leanh::lean_dec_ref(v___y_2039_);
    crate::leanh::lean_dec(v___y_2038_);
    crate::leanh::lean_dec_ref(v___y_2037_);
    crate::leanh::lean_dec(v___y_2036_);
    crate::leanh::lean_dec_ref(v___y_2035_);
    return v_res_2042_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3(
    mut v_msgData_2043_: *mut crate::leanh::LeanObject,
    mut v_macroStack_2044_: *mut crate::leanh::LeanObject,
    mut v___y_2045_: *mut crate::leanh::LeanObject,
    mut v___y_2046_: *mut crate::leanh::LeanObject,
    mut v___y_2047_: *mut crate::leanh::LeanObject,
    mut v___y_2048_: *mut crate::leanh::LeanObject,
    mut v___y_2049_: *mut crate::leanh::LeanObject,
    mut v___y_2050_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2052_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3___redArg(v_msgData_2043_, v_macroStack_2044_, v___y_2049_);
    return v___x_2052_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3___boxed(
    mut v_msgData_2053_: *mut crate::leanh::LeanObject,
    mut v_macroStack_2054_: *mut crate::leanh::LeanObject,
    mut v___y_2055_: *mut crate::leanh::LeanObject,
    mut v___y_2056_: *mut crate::leanh::LeanObject,
    mut v___y_2057_: *mut crate::leanh::LeanObject,
    mut v___y_2058_: *mut crate::leanh::LeanObject,
    mut v___y_2059_: *mut crate::leanh::LeanObject,
    mut v___y_2060_: *mut crate::leanh::LeanObject,
    mut v___y_2061_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2062_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1_spec__1_spec__3(v_msgData_2053_, v_macroStack_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_);
    crate::leanh::lean_dec(v___y_2060_);
    crate::leanh::lean_dec_ref(v___y_2059_);
    crate::leanh::lean_dec(v___y_2058_);
    crate::leanh::lean_dec_ref(v___y_2057_);
    crate::leanh::lean_dec(v___y_2056_);
    crate::leanh::lean_dec_ref(v___y_2055_);
    return v_res_2062_;
}
pub unsafe fn l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2072_ = l_Lean_Elab_Command_commandElabAttribute;
    v___x_2073_ = l_Lean_Elab_CheckTactic_elabCheckTactic___closed__3;
    v___x_2074_ = l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__3;
    v___x_2075_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_CheckTactic_elabCheckTactic___boxed as *mut core::ffi::c_void,
        4,
        0,
    );
    v___x_2076_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_2072_,
        v___x_2073_,
        v___x_2074_,
        v___x_2075_,
    );
    return v___x_2076_;
}
pub unsafe fn l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___boxed(
    mut v_a_2077_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2078_ = l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1();
    return v_res_2078_;
}
pub unsafe fn l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2105_ = l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1___closed__3;
    v___x_2106_ = l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___closed__6;
    v___x_2107_ = l_Lean_addBuiltinDeclarationRanges(v___x_2105_, v___x_2106_);
    return v___x_2107_;
}
pub unsafe fn l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3___boxed(
    mut v_a_2108_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2109_ = l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3();
    return v_res_2109_;
}
pub unsafe fn l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__1___redArg(
    mut v_a_2110_: *mut crate::leanh::LeanObject,
    mut v___y_2111_: *mut crate::leanh::LeanObject,
    mut v___y_2112_: *mut crate::leanh::LeanObject,
    mut v___y_2113_: *mut crate::leanh::LeanObject,
    mut v___y_2114_: *mut crate::leanh::LeanObject,
    mut v___y_2115_: *mut crate::leanh::LeanObject,
    mut v___y_2116_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2118_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(
        v_a_2110_,
        v___y_2111_,
        v___y_2112_,
        v___y_2113_,
        v___y_2114_,
        v___y_2115_,
        v___y_2116_,
    );
    return v___x_2118_;
}
pub unsafe fn l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__1___redArg___boxed(
    mut v_a_2119_: *mut crate::leanh::LeanObject,
    mut v___y_2120_: *mut crate::leanh::LeanObject,
    mut v___y_2121_: *mut crate::leanh::LeanObject,
    mut v___y_2122_: *mut crate::leanh::LeanObject,
    mut v___y_2123_: *mut crate::leanh::LeanObject,
    mut v___y_2124_: *mut crate::leanh::LeanObject,
    mut v___y_2125_: *mut crate::leanh::LeanObject,
    mut v___y_2126_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2127_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__1___redArg(v_a_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_);
    crate::leanh::lean_dec(v___y_2125_);
    crate::leanh::lean_dec_ref(v___y_2124_);
    crate::leanh::lean_dec(v___y_2123_);
    crate::leanh::lean_dec_ref(v___y_2122_);
    crate::leanh::lean_dec(v___y_2121_);
    crate::leanh::lean_dec_ref(v___y_2120_);
    return v_res_2127_;
}
pub unsafe fn l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__1(
    mut v_00_u03b1_2128_: *mut crate::leanh::LeanObject,
    mut v_a_2129_: *mut crate::leanh::LeanObject,
    mut v___y_2130_: *mut crate::leanh::LeanObject,
    mut v___y_2131_: *mut crate::leanh::LeanObject,
    mut v___y_2132_: *mut crate::leanh::LeanObject,
    mut v___y_2133_: *mut crate::leanh::LeanObject,
    mut v___y_2134_: *mut crate::leanh::LeanObject,
    mut v___y_2135_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2137_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(
        v_a_2129_,
        v___y_2130_,
        v___y_2131_,
        v___y_2132_,
        v___y_2133_,
        v___y_2134_,
        v___y_2135_,
    );
    return v___x_2137_;
}
pub unsafe fn l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__1___boxed(
    mut v_00_u03b1_2138_: *mut crate::leanh::LeanObject,
    mut v_a_2139_: *mut crate::leanh::LeanObject,
    mut v___y_2140_: *mut crate::leanh::LeanObject,
    mut v___y_2141_: *mut crate::leanh::LeanObject,
    mut v___y_2142_: *mut crate::leanh::LeanObject,
    mut v___y_2143_: *mut crate::leanh::LeanObject,
    mut v___y_2144_: *mut crate::leanh::LeanObject,
    mut v___y_2145_: *mut crate::leanh::LeanObject,
    mut v___y_2146_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2147_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__1(v_00_u03b1_2138_, v_a_2139_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_);
    crate::leanh::lean_dec(v___y_2145_);
    crate::leanh::lean_dec_ref(v___y_2144_);
    crate::leanh::lean_dec(v___y_2143_);
    crate::leanh::lean_dec_ref(v___y_2142_);
    crate::leanh::lean_dec(v___y_2141_);
    crate::leanh::lean_dec_ref(v___y_2140_);
    return v_res_2147_;
}
pub unsafe fn l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__1(
    mut v___x_2148_: *mut crate::leanh::LeanObject,
    mut v___x_2149_: *mut crate::leanh::LeanObject,
    mut v___x_2150_: *mut crate::leanh::LeanObject,
    mut v___x_2151_: *mut crate::leanh::LeanObject,
    mut v___y_2152_: *mut crate::leanh::LeanObject,
    mut v___y_2153_: *mut crate::leanh::LeanObject,
    mut v___y_2154_: *mut crate::leanh::LeanObject,
    mut v___y_2155_: *mut crate::leanh::LeanObject,
    mut v___y_2156_: *mut crate::leanh::LeanObject,
    mut v___y_2157_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2163_: u8 = 0;
    let mut v___x_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2168_: u8 = 0;
    let mut v_a_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2172_: u8 = 0;
    let mut v___x_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2176_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2159_ = l_Lean_Elab_runTactic(
                    v___x_2148_,
                    v___x_2149_,
                    v___x_2150_,
                    v___x_2151_,
                    v___y_2154_,
                    v___y_2155_,
                    v___y_2156_,
                    v___y_2157_,
                );
                if crate::leanh::lean_obj_tag(v___x_2159_) == 0 {
                    v_a_2160_ = crate::leanh::lean_ctor_get(v___x_2159_, 0);
                    v_isSharedCheck_2168_ = (!crate::leanh::lean_is_exclusive(v___x_2159_)) as u8;
                    if v_isSharedCheck_2168_ == 0 {
                        v___x_2162_ = v___x_2159_;
                        v_isShared_2163_ = v_isSharedCheck_2168_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2160_);
                        crate::leanh::lean_dec(v___x_2159_);
                        v___x_2162_ = crate::leanh::lean_box(0);
                        v_isShared_2163_ = v_isSharedCheck_2168_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2169_ = crate::leanh::lean_ctor_get(v___x_2159_, 0);
                    v_isSharedCheck_2176_ = (!crate::leanh::lean_is_exclusive(v___x_2159_)) as u8;
                    if v_isSharedCheck_2176_ == 0 {
                        v___x_2171_ = v___x_2159_;
                        v_isShared_2172_ = v_isSharedCheck_2176_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2169_);
                        crate::leanh::lean_dec(v___x_2159_);
                        v___x_2171_ = crate::leanh::lean_box(0);
                        v_isShared_2172_ = v_isSharedCheck_2176_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2164_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2164_, 0, v_a_2160_);
                if v_isShared_2163_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2162_, 0, v___x_2164_);
                    v___x_2166_ = v___x_2162_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2167_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2167_, 0, v___x_2164_);
                    v___x_2166_ = v_reuseFailAlloc_2167_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2166_;
            }
            3 => {
                if v_isShared_2172_ == 0 {
                    v___x_2174_ = v___x_2171_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2175_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2175_, 0, v_a_2169_);
                    v___x_2174_ = v_reuseFailAlloc_2175_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2174_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__1___boxed(
    mut v___x_2177_: *mut crate::leanh::LeanObject,
    mut v___x_2178_: *mut crate::leanh::LeanObject,
    mut v___x_2179_: *mut crate::leanh::LeanObject,
    mut v___x_2180_: *mut crate::leanh::LeanObject,
    mut v___y_2181_: *mut crate::leanh::LeanObject,
    mut v___y_2182_: *mut crate::leanh::LeanObject,
    mut v___y_2183_: *mut crate::leanh::LeanObject,
    mut v___y_2184_: *mut crate::leanh::LeanObject,
    mut v___y_2185_: *mut crate::leanh::LeanObject,
    mut v___y_2186_: *mut crate::leanh::LeanObject,
    mut v___y_2187_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2188_ = l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__1(
        v___x_2177_,
        v___x_2178_,
        v___x_2179_,
        v___x_2180_,
        v___y_2181_,
        v___y_2182_,
        v___y_2183_,
        v___y_2184_,
        v___y_2185_,
        v___y_2186_,
    );
    crate::leanh::lean_dec(v___y_2186_);
    crate::leanh::lean_dec_ref(v___y_2185_);
    crate::leanh::lean_dec(v___y_2184_);
    crate::leanh::lean_dec_ref(v___y_2183_);
    crate::leanh::lean_dec(v___y_2182_);
    crate::leanh::lean_dec_ref(v___y_2181_);
    return v_res_2188_;
}
pub unsafe fn l_List_foldlM___at___00List_foldlM___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0___redArg(
    mut v_stx_2189_: *mut crate::leanh::LeanObject,
    mut v_x_2190_: *mut crate::leanh::LeanObject,
    mut v_x_2191_: *mut crate::leanh::LeanObject,
    mut v___y_2192_: *mut crate::leanh::LeanObject,
    mut v___y_2193_: *mut crate::leanh::LeanObject,
    mut v___y_2194_: *mut crate::leanh::LeanObject,
    mut v___y_2195_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2207_: u8 = 0;
    let mut v___x_2208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2213_: u8 = 0;
    let mut v_unused_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2218_: u8 = 0;
    let mut v___x_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2222_: u8 = 0;
    let mut v_a_2223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2226_: u8 = 0;
    let mut v___x_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2230_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2191_) == 0 {
                    v___x_2197_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2197_, 0, v_x_2190_);
                    return v___x_2197_;
                } else {
                    v_head_2198_ = crate::leanh::lean_ctor_get(v_x_2191_, 0);
                    crate::leanh::lean_inc(v_head_2198_);
                    v_tail_2199_ = crate::leanh::lean_ctor_get(v_x_2191_, 1);
                    crate::leanh::lean_inc(v_tail_2199_);
                    crate::leanh::lean_dec_ref_known(v_x_2191_, 2);
                    v___x_2200_ = l_Lean_MVarId_getType(
                        v_head_2198_,
                        v___y_2192_,
                        v___y_2193_,
                        v___y_2194_,
                        v___y_2195_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2200_) == 0 {
                        v_a_2201_ = crate::leanh::lean_ctor_get(v___x_2200_, 0);
                        crate::leanh::lean_inc(v_a_2201_);
                        crate::leanh::lean_dec_ref_known(v___x_2200_, 1);
                        v___x_2202_ = l_Lean_Meta_CheckTactic_matchCheckGoalType(
                            v_stx_2189_,
                            v_a_2201_,
                            v___y_2192_,
                            v___y_2193_,
                            v___y_2194_,
                            v___y_2195_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_2202_) == 0 {
                            v_a_2203_ = crate::leanh::lean_ctor_get(v___x_2202_, 0);
                            crate::leanh::lean_inc(v_a_2203_);
                            crate::leanh::lean_dec_ref_known(v___x_2202_, 1);
                            v_fst_2204_ = crate::leanh::lean_ctor_get(v_a_2203_, 0);
                            v_isSharedCheck_2213_ =
                                (!crate::leanh::lean_is_exclusive(v_a_2203_)) as u8;
                            if v_isSharedCheck_2213_ == 0 {
                                v_unused_2214_ = crate::leanh::lean_ctor_get(v_a_2203_, 1);
                                crate::leanh::lean_dec(v_unused_2214_);
                                v___x_2206_ = v_a_2203_;
                                v_isShared_2207_ = v_isSharedCheck_2213_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_fst_2204_);
                                crate::leanh::lean_dec(v_a_2203_);
                                v___x_2206_ = crate::leanh::lean_box(0);
                                v_isShared_2207_ = v_isSharedCheck_2213_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_tail_2199_);
                            crate::leanh::lean_dec_ref(v_x_2190_);
                            v_a_2215_ = crate::leanh::lean_ctor_get(v___x_2202_, 0);
                            v_isSharedCheck_2222_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2202_)) as u8;
                            if v_isSharedCheck_2222_ == 0 {
                                v___x_2217_ = v___x_2202_;
                                v_isShared_2218_ = v_isSharedCheck_2222_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2215_);
                                crate::leanh::lean_dec(v___x_2202_);
                                v___x_2217_ = crate::leanh::lean_box(0);
                                v_isShared_2218_ = v_isSharedCheck_2222_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_tail_2199_);
                        crate::leanh::lean_dec_ref(v_x_2190_);
                        v_a_2223_ = crate::leanh::lean_ctor_get(v___x_2200_, 0);
                        v_isSharedCheck_2230_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2200_)) as u8;
                        if v_isSharedCheck_2230_ == 0 {
                            v___x_2225_ = v___x_2200_;
                            v_isShared_2226_ = v_isSharedCheck_2230_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2223_);
                            crate::leanh::lean_dec(v___x_2200_);
                            v___x_2225_ = crate::leanh::lean_box(0);
                            v_isShared_2226_ = v_isSharedCheck_2230_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2208_ = l_Lean_indentExpr(v_fst_2204_);
                if v_isShared_2207_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2206_, 7);
                    crate::leanh::lean_ctor_set(v___x_2206_, 1, v___x_2208_);
                    crate::leanh::lean_ctor_set(v___x_2206_, 0, v_x_2190_);
                    v___x_2210_ = v___x_2206_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2212_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2212_, 0, v_x_2190_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2212_, 1, v___x_2208_);
                    v___x_2210_ = v_reuseFailAlloc_2212_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_x_2190_ = v___x_2210_;
                v_x_2191_ = v_tail_2199_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_2218_ == 0 {
                    v___x_2220_ = v___x_2217_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2221_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2221_, 0, v_a_2215_);
                    v___x_2220_ = v_reuseFailAlloc_2221_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2220_;
            }
            5 => {
                if v_isShared_2226_ == 0 {
                    v___x_2228_ = v___x_2225_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2229_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2229_, 0, v_a_2223_);
                    v___x_2228_ = v_reuseFailAlloc_2229_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2228_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldlM___at___00List_foldlM___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0___redArg___boxed(
    mut v_stx_2231_: *mut crate::leanh::LeanObject,
    mut v_x_2232_: *mut crate::leanh::LeanObject,
    mut v_x_2233_: *mut crate::leanh::LeanObject,
    mut v___y_2234_: *mut crate::leanh::LeanObject,
    mut v___y_2235_: *mut crate::leanh::LeanObject,
    mut v___y_2236_: *mut crate::leanh::LeanObject,
    mut v___y_2237_: *mut crate::leanh::LeanObject,
    mut v___y_2238_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2239_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0___redArg(v_stx_2231_, v_x_2232_, v_x_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_);
    crate::leanh::lean_dec(v___y_2237_);
    crate::leanh::lean_dec_ref(v___y_2236_);
    crate::leanh::lean_dec(v___y_2235_);
    crate::leanh::lean_dec_ref(v___y_2234_);
    crate::leanh::lean_dec(v_stx_2231_);
    return v_res_2239_;
}
pub unsafe fn l_List_foldlM___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0(
    mut v_stx_2240_: *mut crate::leanh::LeanObject,
    mut v_x_2241_: *mut crate::leanh::LeanObject,
    mut v_x_2242_: *mut crate::leanh::LeanObject,
    mut v___y_2243_: *mut crate::leanh::LeanObject,
    mut v___y_2244_: *mut crate::leanh::LeanObject,
    mut v___y_2245_: *mut crate::leanh::LeanObject,
    mut v___y_2246_: *mut crate::leanh::LeanObject,
    mut v___y_2247_: *mut crate::leanh::LeanObject,
    mut v___y_2248_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2260_: u8 = 0;
    let mut v___x_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2266_: u8 = 0;
    let mut v_unused_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2271_: u8 = 0;
    let mut v___x_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2275_: u8 = 0;
    let mut v_a_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2279_: u8 = 0;
    let mut v___x_2281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2283_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2242_) == 0 {
                    v___x_2250_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2250_, 0, v_x_2241_);
                    return v___x_2250_;
                } else {
                    v_head_2251_ = crate::leanh::lean_ctor_get(v_x_2242_, 0);
                    crate::leanh::lean_inc(v_head_2251_);
                    v_tail_2252_ = crate::leanh::lean_ctor_get(v_x_2242_, 1);
                    crate::leanh::lean_inc(v_tail_2252_);
                    crate::leanh::lean_dec_ref_known(v_x_2242_, 2);
                    v___x_2253_ = l_Lean_MVarId_getType(
                        v_head_2251_,
                        v___y_2245_,
                        v___y_2246_,
                        v___y_2247_,
                        v___y_2248_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2253_) == 0 {
                        v_a_2254_ = crate::leanh::lean_ctor_get(v___x_2253_, 0);
                        crate::leanh::lean_inc(v_a_2254_);
                        crate::leanh::lean_dec_ref_known(v___x_2253_, 1);
                        v___x_2255_ = l_Lean_Meta_CheckTactic_matchCheckGoalType(
                            v_stx_2240_,
                            v_a_2254_,
                            v___y_2245_,
                            v___y_2246_,
                            v___y_2247_,
                            v___y_2248_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_2255_) == 0 {
                            v_a_2256_ = crate::leanh::lean_ctor_get(v___x_2255_, 0);
                            crate::leanh::lean_inc(v_a_2256_);
                            crate::leanh::lean_dec_ref_known(v___x_2255_, 1);
                            v_fst_2257_ = crate::leanh::lean_ctor_get(v_a_2256_, 0);
                            v_isSharedCheck_2266_ =
                                (!crate::leanh::lean_is_exclusive(v_a_2256_)) as u8;
                            if v_isSharedCheck_2266_ == 0 {
                                v_unused_2267_ = crate::leanh::lean_ctor_get(v_a_2256_, 1);
                                crate::leanh::lean_dec(v_unused_2267_);
                                v___x_2259_ = v_a_2256_;
                                v_isShared_2260_ = v_isSharedCheck_2266_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_fst_2257_);
                                crate::leanh::lean_dec(v_a_2256_);
                                v___x_2259_ = crate::leanh::lean_box(0);
                                v_isShared_2260_ = v_isSharedCheck_2266_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_tail_2252_);
                            crate::leanh::lean_dec_ref(v_x_2241_);
                            v_a_2268_ = crate::leanh::lean_ctor_get(v___x_2255_, 0);
                            v_isSharedCheck_2275_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2255_)) as u8;
                            if v_isSharedCheck_2275_ == 0 {
                                v___x_2270_ = v___x_2255_;
                                v_isShared_2271_ = v_isSharedCheck_2275_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2268_);
                                crate::leanh::lean_dec(v___x_2255_);
                                v___x_2270_ = crate::leanh::lean_box(0);
                                v_isShared_2271_ = v_isSharedCheck_2275_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_tail_2252_);
                        crate::leanh::lean_dec_ref(v_x_2241_);
                        v_a_2276_ = crate::leanh::lean_ctor_get(v___x_2253_, 0);
                        v_isSharedCheck_2283_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2253_)) as u8;
                        if v_isSharedCheck_2283_ == 0 {
                            v___x_2278_ = v___x_2253_;
                            v_isShared_2279_ = v_isSharedCheck_2283_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2276_);
                            crate::leanh::lean_dec(v___x_2253_);
                            v___x_2278_ = crate::leanh::lean_box(0);
                            v_isShared_2279_ = v_isSharedCheck_2283_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2261_ = l_Lean_indentExpr(v_fst_2257_);
                if v_isShared_2260_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2259_, 7);
                    crate::leanh::lean_ctor_set(v___x_2259_, 1, v___x_2261_);
                    crate::leanh::lean_ctor_set(v___x_2259_, 0, v_x_2241_);
                    v___x_2263_ = v___x_2259_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2265_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2265_, 0, v_x_2241_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2265_, 1, v___x_2261_);
                    v___x_2263_ = v_reuseFailAlloc_2265_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2264_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0___redArg(v_stx_2240_, v___x_2263_, v_tail_2252_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_);
                return v___x_2264_;
            }
            3 => {
                if v_isShared_2271_ == 0 {
                    v___x_2273_ = v___x_2270_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2274_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2274_, 0, v_a_2268_);
                    v___x_2273_ = v_reuseFailAlloc_2274_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2273_;
            }
            5 => {
                if v_isShared_2279_ == 0 {
                    v___x_2281_ = v___x_2278_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2282_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2282_, 0, v_a_2276_);
                    v___x_2281_ = v_reuseFailAlloc_2282_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2281_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldlM___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0___boxed(
    mut v_stx_2284_: *mut crate::leanh::LeanObject,
    mut v_x_2285_: *mut crate::leanh::LeanObject,
    mut v_x_2286_: *mut crate::leanh::LeanObject,
    mut v___y_2287_: *mut crate::leanh::LeanObject,
    mut v___y_2288_: *mut crate::leanh::LeanObject,
    mut v___y_2289_: *mut crate::leanh::LeanObject,
    mut v___y_2290_: *mut crate::leanh::LeanObject,
    mut v___y_2291_: *mut crate::leanh::LeanObject,
    mut v___y_2292_: *mut crate::leanh::LeanObject,
    mut v___y_2293_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2294_ = l_List_foldlM___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0(
        v_stx_2284_,
        v_x_2285_,
        v_x_2286_,
        v___y_2287_,
        v___y_2288_,
        v___y_2289_,
        v___y_2290_,
        v___y_2291_,
        v___y_2292_,
    );
    crate::leanh::lean_dec(v___y_2292_);
    crate::leanh::lean_dec_ref(v___y_2291_);
    crate::leanh::lean_dec(v___y_2290_);
    crate::leanh::lean_dec_ref(v___y_2289_);
    crate::leanh::lean_dec(v___y_2288_);
    crate::leanh::lean_dec_ref(v___y_2287_);
    crate::leanh::lean_dec(v_stx_2284_);
    return v_res_2294_;
}
pub unsafe fn _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2296_ = l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__0;
    v___x_2297_ = l_Lean_stringToMessageData(v___x_2296_);
    return v___x_2297_;
}
pub unsafe fn _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2299_ = l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__2;
    v___x_2300_ = l_Lean_stringToMessageData(v___x_2299_);
    return v___x_2300_;
}
pub unsafe fn _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2302_ = l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__4;
    v___x_2303_ = l_Lean_stringToMessageData(v___x_2302_);
    return v___x_2303_;
}
pub unsafe fn _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2305_ = l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__6;
    v___x_2306_ = l_Lean_stringToMessageData(v___x_2305_);
    return v___x_2306_;
}
pub unsafe fn l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0(
    mut v___x_2307_: *mut crate::leanh::LeanObject,
    mut v___x_2308_: u8,
    mut v___x_2309_: *mut crate::leanh::LeanObject,
    mut v_stx_2310_: *mut crate::leanh::LeanObject,
    mut v___f_2311_: *mut crate::leanh::LeanObject,
    mut v___x_2312_: *mut crate::leanh::LeanObject,
    mut v___vars_2313_: *mut crate::leanh::LeanObject,
    mut v___y_2314_: *mut crate::leanh::LeanObject,
    mut v___y_2315_: *mut crate::leanh::LeanObject,
    mut v___y_2316_: *mut crate::leanh::LeanObject,
    mut v___y_2317_: *mut crate::leanh::LeanObject,
    mut v___y_2318_: *mut crate::leanh::LeanObject,
    mut v___y_2319_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2331_: u8 = 0;
    let mut v___x_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2346_: u8 = 0;
    let mut v___x_2347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2354_: u8 = 0;
    let mut v___x_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2371_: u8 = 0;
    let mut v_unused_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2376_: u8 = 0;
    let mut v___x_2378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2380_: u8 = 0;
    let mut v_a_2381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2384_: u8 = 0;
    let mut v___x_2386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2388_: u8 = 0;
    let mut v_isSharedCheck_2389_: u8 = 0;
    let mut v_unused_2390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2405_: u8 = 0;
    let mut v___x_2407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2409_: u8 = 0;
    let mut v_reuseFailAlloc_2410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2411_: u8 = 0;
    let mut v_unused_2412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2416_: u8 = 0;
    let mut v___x_2418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2420_: u8 = 0;
    let mut v___x_2421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: u8 = 0;
    let mut v___x_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: u8 = 0;
    let mut v___x_2437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2444_: u8 = 0;
    let mut v___x_2445_: u8 = 0;
    let mut v___x_2446_: u8 = 0;
    let mut v_a_2447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2450_: u8 = 0;
    let mut v___x_2452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2454_: u8 = 0;
    let mut v_a_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2458_: u8 = 0;
    let mut v___x_2460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2462_: u8 = 0;
    let mut v_a_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2466_: u8 = 0;
    let mut v___x_2468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2470_: u8 = 0;
    let mut v_a_2471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2474_: u8 = 0;
    let mut v___x_2476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2478_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2421_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v___x_2307_);
                v___x_2422_ = l_Lean_Elab_Term_elabTerm(
                    v___x_2307_,
                    v___x_2421_,
                    v___x_2308_,
                    v___x_2308_,
                    v___y_2314_,
                    v___y_2315_,
                    v___y_2316_,
                    v___y_2317_,
                    v___y_2318_,
                    v___y_2319_,
                );
                if crate::leanh::lean_obj_tag(v___x_2422_) == 0 {
                    v_a_2423_ = crate::leanh::lean_ctor_get(v___x_2422_, 0);
                    crate::leanh::lean_inc_n(v_a_2423_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_2422_, 1);
                    crate::leanh::lean_inc(v___y_2319_);
                    crate::leanh::lean_inc_ref(v___y_2318_);
                    crate::leanh::lean_inc(v___y_2317_);
                    crate::leanh::lean_inc_ref(v___y_2316_);
                    v___x_2424_ = lean_infer_type(
                        v_a_2423_,
                        v___y_2316_,
                        v___y_2317_,
                        v___y_2318_,
                        v___y_2319_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2424_) == 0 {
                        v_a_2425_ = crate::leanh::lean_ctor_get(v___x_2424_, 0);
                        crate::leanh::lean_inc(v_a_2425_);
                        crate::leanh::lean_dec_ref_known(v___x_2424_, 1);
                        v___x_2426_ = l_Lean_Meta_CheckTactic_mkCheckGoalType(
                            v_a_2423_,
                            v_a_2425_,
                            v___y_2316_,
                            v___y_2317_,
                            v___y_2318_,
                            v___y_2319_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_2426_) == 0 {
                            v_a_2427_ = crate::leanh::lean_ctor_get(v___x_2426_, 0);
                            crate::leanh::lean_inc(v_a_2427_);
                            crate::leanh::lean_dec_ref_known(v___x_2426_, 1);
                            v___x_2428_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2428_, 0, v_a_2427_);
                            v___x_2429_ = 0;
                            v___x_2430_ = crate::leanh::lean_box(0);
                            v___x_2431_ = l_Lean_Meta_mkFreshExprMVar(
                                v___x_2428_,
                                v___x_2429_,
                                v___x_2430_,
                                v___y_2316_,
                                v___y_2317_,
                                v___y_2318_,
                                v___y_2319_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_2431_) == 0 {
                                v_a_2432_ = crate::leanh::lean_ctor_get(v___x_2431_, 0);
                                crate::leanh::lean_inc(v_a_2432_);
                                crate::leanh::lean_dec_ref_known(v___x_2431_, 1);
                                v___x_2433_ = l_Lean_Expr_mvarId_x21(v_a_2432_);
                                crate::leanh::lean_dec(v_a_2432_);
                                v___x_2434_ = crate::leanh::lean_box(0);
                                v___x_2435_ = crate::leanh::lean_box(1);
                                v___x_2436_ = 0;
                                v___x_2437_ =
                                    l_Lean_Elab_CheckTactic_elabCheckTactic___lam__1___closed__0;
                                v___x_2438_ = crate::leanh::lean_alloc_ctor(0, 8, (11) as u32);
                                crate::leanh::lean_ctor_set(v___x_2438_, 0, v___x_2421_);
                                crate::leanh::lean_ctor_set(v___x_2438_, 1, v___x_2434_);
                                crate::leanh::lean_ctor_set(v___x_2438_, 2, v___x_2421_);
                                crate::leanh::lean_ctor_set(v___x_2438_, 3, v___f_2311_);
                                crate::leanh::lean_ctor_set(v___x_2438_, 4, v___x_2435_);
                                crate::leanh::lean_ctor_set(v___x_2438_, 5, v___x_2435_);
                                crate::leanh::lean_ctor_set(v___x_2438_, 6, v___x_2421_);
                                crate::leanh::lean_ctor_set(v___x_2438_, 7, v___x_2437_);
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_2438_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8)
                                        as u32,
                                    v___x_2308_,
                                );
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_2438_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 1)
                                        as u32,
                                    v___x_2308_,
                                );
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_2438_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 2)
                                        as u32,
                                    v___x_2308_,
                                );
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_2438_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 3)
                                        as u32,
                                    v___x_2308_,
                                );
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_2438_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 4)
                                        as u32,
                                    v___x_2436_,
                                );
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_2438_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 5)
                                        as u32,
                                    v___x_2436_,
                                );
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_2438_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 6)
                                        as u32,
                                    v___x_2436_,
                                );
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_2438_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 7)
                                        as u32,
                                    v___x_2436_,
                                );
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_2438_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 8)
                                        as u32,
                                    v___x_2308_,
                                );
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_2438_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 9)
                                        as u32,
                                    v___x_2436_,
                                );
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_2438_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 10)
                                        as u32,
                                    v___x_2308_,
                                );
                                v___x_2439_ = crate::leanh::lean_alloc_ctor(0, 7, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2439_, 0, v___x_2312_);
                                crate::leanh::lean_ctor_set(v___x_2439_, 1, v___x_2435_);
                                crate::leanh::lean_ctor_set(v___x_2439_, 2, v___x_2434_);
                                crate::leanh::lean_ctor_set(v___x_2439_, 3, v___x_2434_);
                                crate::leanh::lean_ctor_set(v___x_2439_, 4, v___x_2434_);
                                crate::leanh::lean_ctor_set(v___x_2439_, 5, v___x_2435_);
                                crate::leanh::lean_ctor_set(v___x_2439_, 6, v___x_2434_);
                                crate::leanh::lean_inc(v___x_2309_);
                                v___f_2440_ = crate::leanh::lean_alloc_closure(
                                    l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__1___boxed
                                        as *mut core::ffi::c_void,
                                    11,
                                    4,
                                );
                                crate::leanh::lean_closure_set(v___f_2440_, 0, v___x_2433_);
                                crate::leanh::lean_closure_set(v___f_2440_, 1, v___x_2309_);
                                crate::leanh::lean_closure_set(v___f_2440_, 2, v___x_2438_);
                                crate::leanh::lean_closure_set(v___f_2440_, 3, v___x_2439_);
                                v___x_2441_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(
                                    v___f_2440_,
                                    v___y_2314_,
                                    v___y_2315_,
                                    v___y_2316_,
                                    v___y_2317_,
                                    v___y_2318_,
                                    v___y_2319_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_2441_) == 0 {
                                    v___y_2325_ = v___x_2441_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_a_2442_ = crate::leanh::lean_ctor_get(v___x_2441_, 0);
                                    crate::leanh::lean_inc(v_a_2442_);
                                    v___x_2445_ = l_Lean_Exception_isInterrupt(v_a_2442_);
                                    if v___x_2445_ == 0 {
                                        v___x_2446_ = l_Lean_Exception_isRuntime(v_a_2442_);
                                        v___y_2444_ = v___x_2446_;
                                        state = 19;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v_a_2442_);
                                        v___y_2444_ = v___x_2445_;
                                        state = 19;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v___x_2312_);
                                crate::leanh::lean_dec_ref(v___f_2311_);
                                crate::leanh::lean_dec(v___x_2309_);
                                crate::leanh::lean_dec(v___x_2307_);
                                v_a_2447_ = crate::leanh::lean_ctor_get(v___x_2431_, 0);
                                v_isSharedCheck_2454_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2431_)) as u8;
                                if v_isSharedCheck_2454_ == 0 {
                                    v___x_2449_ = v___x_2431_;
                                    v_isShared_2450_ = v_isSharedCheck_2454_;
                                    state = 20;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2447_);
                                    crate::leanh::lean_dec(v___x_2431_);
                                    v___x_2449_ = crate::leanh::lean_box(0);
                                    v_isShared_2450_ = v_isSharedCheck_2454_;
                                    state = 20;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_2312_);
                            crate::leanh::lean_dec_ref(v___f_2311_);
                            crate::leanh::lean_dec(v___x_2309_);
                            crate::leanh::lean_dec(v___x_2307_);
                            v_a_2455_ = crate::leanh::lean_ctor_get(v___x_2426_, 0);
                            v_isSharedCheck_2462_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2426_)) as u8;
                            if v_isSharedCheck_2462_ == 0 {
                                v___x_2457_ = v___x_2426_;
                                v_isShared_2458_ = v_isSharedCheck_2462_;
                                state = 22;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2455_);
                                crate::leanh::lean_dec(v___x_2426_);
                                v___x_2457_ = crate::leanh::lean_box(0);
                                v_isShared_2458_ = v_isSharedCheck_2462_;
                                state = 22;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2423_);
                        crate::leanh::lean_dec(v___x_2312_);
                        crate::leanh::lean_dec_ref(v___f_2311_);
                        crate::leanh::lean_dec(v___x_2309_);
                        crate::leanh::lean_dec(v___x_2307_);
                        v_a_2463_ = crate::leanh::lean_ctor_get(v___x_2424_, 0);
                        v_isSharedCheck_2470_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2424_)) as u8;
                        if v_isSharedCheck_2470_ == 0 {
                            v___x_2465_ = v___x_2424_;
                            v_isShared_2466_ = v_isSharedCheck_2470_;
                            state = 24;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2463_);
                            crate::leanh::lean_dec(v___x_2424_);
                            v___x_2465_ = crate::leanh::lean_box(0);
                            v_isShared_2466_ = v_isSharedCheck_2470_;
                            state = 24;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2312_);
                    crate::leanh::lean_dec_ref(v___f_2311_);
                    crate::leanh::lean_dec(v___x_2309_);
                    crate::leanh::lean_dec(v___x_2307_);
                    v_a_2471_ = crate::leanh::lean_ctor_get(v___x_2422_, 0);
                    v_isSharedCheck_2478_ = (!crate::leanh::lean_is_exclusive(v___x_2422_)) as u8;
                    if v_isSharedCheck_2478_ == 0 {
                        v___x_2473_ = v___x_2422_;
                        v_isShared_2474_ = v_isSharedCheck_2478_;
                        state = 26;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2471_);
                        crate::leanh::lean_dec(v___x_2422_);
                        v___x_2473_ = crate::leanh::lean_box(0);
                        v_isShared_2474_ = v_isSharedCheck_2478_;
                        state = 26;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2322_ = crate::leanh::lean_box(0);
                v___x_2323_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2323_, 0, v___x_2322_);
                return v___x_2323_;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v___y_2325_) == 0 {
                    v_a_2326_ = crate::leanh::lean_ctor_get(v___y_2325_, 0);
                    crate::leanh::lean_inc(v_a_2326_);
                    crate::leanh::lean_dec_ref_known(v___y_2325_, 1);
                    if crate::leanh::lean_obj_tag(v_a_2326_) == 0 {
                        crate::leanh::lean_dec(v___x_2309_);
                        crate::leanh::lean_dec(v___x_2307_);
                        state = 1;
                        continue;
                    } else {
                        v_val_2327_ = crate::leanh::lean_ctor_get(v_a_2326_, 0);
                        crate::leanh::lean_inc(v_val_2327_);
                        crate::leanh::lean_dec_ref_known(v_a_2326_, 1);
                        v_fst_2328_ = crate::leanh::lean_ctor_get(v_val_2327_, 0);
                        v_isSharedCheck_2411_ =
                            (!crate::leanh::lean_is_exclusive(v_val_2327_)) as u8;
                        if v_isSharedCheck_2411_ == 0 {
                            v_unused_2412_ = crate::leanh::lean_ctor_get(v_val_2327_, 1);
                            crate::leanh::lean_dec(v_unused_2412_);
                            v___x_2330_ = v_val_2327_;
                            v_isShared_2331_ = v_isSharedCheck_2411_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_fst_2328_);
                            crate::leanh::lean_dec(v_val_2327_);
                            v___x_2330_ = crate::leanh::lean_box(0);
                            v_isShared_2331_ = v_isSharedCheck_2411_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2309_);
                    crate::leanh::lean_dec(v___x_2307_);
                    v_a_2413_ = crate::leanh::lean_ctor_get(v___y_2325_, 0);
                    v_isSharedCheck_2420_ = (!crate::leanh::lean_is_exclusive(v___y_2325_)) as u8;
                    if v_isSharedCheck_2420_ == 0 {
                        v___x_2415_ = v___y_2325_;
                        v_isShared_2416_ = v_isSharedCheck_2420_;
                        state = 17;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2413_);
                        crate::leanh::lean_dec(v___y_2325_);
                        v___x_2415_ = crate::leanh::lean_box(0);
                        v_isShared_2416_ = v_isSharedCheck_2420_;
                        state = 17;
                        continue;
                    }
                }
            }
            3 => {
                if crate::leanh::lean_obj_tag(v_fst_2328_) == 0 {
                    v___x_2332_ = l_Lean_MessageData_ofSyntax(v___x_2309_);
                    v___x_2333_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__1_once), _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__1);
                    if v_isShared_2331_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_2330_, 7);
                        crate::leanh::lean_ctor_set(v___x_2330_, 1, v___x_2333_);
                        crate::leanh::lean_ctor_set(v___x_2330_, 0, v___x_2332_);
                        v___x_2335_ = v___x_2330_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2341_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2341_, 0, v___x_2332_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2341_, 1, v___x_2333_);
                        v___x_2335_ = v_reuseFailAlloc_2341_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_tail_2342_ = crate::leanh::lean_ctor_get(v_fst_2328_, 1);
                    if crate::leanh::lean_obj_tag(v_tail_2342_) == 0 {
                        v_head_2343_ = crate::leanh::lean_ctor_get(v_fst_2328_, 0);
                        v_isSharedCheck_2389_ =
                            (!crate::leanh::lean_is_exclusive(v_fst_2328_)) as u8;
                        if v_isSharedCheck_2389_ == 0 {
                            v_unused_2390_ = crate::leanh::lean_ctor_get(v_fst_2328_, 1);
                            crate::leanh::lean_dec(v_unused_2390_);
                            v___x_2345_ = v_fst_2328_;
                            v_isShared_2346_ = v_isSharedCheck_2389_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_head_2343_);
                            crate::leanh::lean_dec(v_fst_2328_);
                            v___x_2345_ = crate::leanh::lean_box(0);
                            v_isShared_2346_ = v_isSharedCheck_2389_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v___x_2391_ = l_Lean_MessageData_ofSyntax(v___x_2309_);
                        v___x_2392_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__1_once), _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__1);
                        if v_isShared_2331_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_2330_, 7);
                            crate::leanh::lean_ctor_set(v___x_2330_, 1, v___x_2392_);
                            crate::leanh::lean_ctor_set(v___x_2330_, 0, v___x_2391_);
                            v___x_2394_ = v___x_2330_;
                            state = 14;
                            continue;
                        } else {
                            v_reuseFailAlloc_2410_ =
                                crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2410_, 0, v___x_2391_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2410_, 1, v___x_2392_);
                            v___x_2394_ = v_reuseFailAlloc_2410_;
                            state = 14;
                            continue;
                        }
                    }
                }
            }
            4 => {
                v___x_2336_ = l_Lean_MessageData_ofSyntax(v___x_2307_);
                v___x_2337_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2337_, 0, v___x_2335_);
                crate::leanh::lean_ctor_set(v___x_2337_, 1, v___x_2336_);
                v___x_2338_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__3_once
                    ),
                    _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__3,
                );
                v___x_2339_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2339_, 0, v___x_2337_);
                crate::leanh::lean_ctor_set(v___x_2339_, 1, v___x_2338_);
                v___x_2340_ = l_Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg(v_stx_2310_, v___x_2339_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_);
                return v___x_2340_;
            }
            5 => {
                v___x_2347_ = l_Lean_MVarId_getType(
                    v_head_2343_,
                    v___y_2316_,
                    v___y_2317_,
                    v___y_2318_,
                    v___y_2319_,
                );
                if crate::leanh::lean_obj_tag(v___x_2347_) == 0 {
                    v_a_2348_ = crate::leanh::lean_ctor_get(v___x_2347_, 0);
                    crate::leanh::lean_inc(v_a_2348_);
                    crate::leanh::lean_dec_ref_known(v___x_2347_, 1);
                    v___x_2349_ = l_Lean_Meta_CheckTactic_matchCheckGoalType(
                        v_stx_2310_,
                        v_a_2348_,
                        v___y_2316_,
                        v___y_2317_,
                        v___y_2318_,
                        v___y_2319_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2349_) == 0 {
                        v_a_2350_ = crate::leanh::lean_ctor_get(v___x_2349_, 0);
                        crate::leanh::lean_inc(v_a_2350_);
                        crate::leanh::lean_dec_ref_known(v___x_2349_, 1);
                        v_fst_2351_ = crate::leanh::lean_ctor_get(v_a_2350_, 0);
                        v_isSharedCheck_2371_ = (!crate::leanh::lean_is_exclusive(v_a_2350_)) as u8;
                        if v_isSharedCheck_2371_ == 0 {
                            v_unused_2372_ = crate::leanh::lean_ctor_get(v_a_2350_, 1);
                            crate::leanh::lean_dec(v_unused_2372_);
                            v___x_2353_ = v_a_2350_;
                            v_isShared_2354_ = v_isSharedCheck_2371_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_fst_2351_);
                            crate::leanh::lean_dec(v_a_2350_);
                            v___x_2353_ = crate::leanh::lean_box(0);
                            v_isShared_2354_ = v_isSharedCheck_2371_;
                            state = 6;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_2345_);
                        crate::leanh::lean_del_object(v___x_2330_);
                        crate::leanh::lean_dec(v___x_2309_);
                        crate::leanh::lean_dec(v___x_2307_);
                        v_a_2373_ = crate::leanh::lean_ctor_get(v___x_2349_, 0);
                        v_isSharedCheck_2380_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2349_)) as u8;
                        if v_isSharedCheck_2380_ == 0 {
                            v___x_2375_ = v___x_2349_;
                            v_isShared_2376_ = v_isSharedCheck_2380_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2373_);
                            crate::leanh::lean_dec(v___x_2349_);
                            v___x_2375_ = crate::leanh::lean_box(0);
                            v_isShared_2376_ = v_isSharedCheck_2380_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2345_);
                    crate::leanh::lean_del_object(v___x_2330_);
                    crate::leanh::lean_dec(v___x_2309_);
                    crate::leanh::lean_dec(v___x_2307_);
                    v_a_2381_ = crate::leanh::lean_ctor_get(v___x_2347_, 0);
                    v_isSharedCheck_2388_ = (!crate::leanh::lean_is_exclusive(v___x_2347_)) as u8;
                    if v_isSharedCheck_2388_ == 0 {
                        v___x_2383_ = v___x_2347_;
                        v_isShared_2384_ = v_isSharedCheck_2388_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2381_);
                        crate::leanh::lean_dec(v___x_2347_);
                        v___x_2383_ = crate::leanh::lean_box(0);
                        v_isShared_2384_ = v_isSharedCheck_2388_;
                        state = 12;
                        continue;
                    }
                }
            }
            6 => {
                v___x_2355_ = l_Lean_indentExpr(v_fst_2351_);
                v___x_2356_ = l_Lean_MessageData_ofSyntax(v___x_2309_);
                v___x_2357_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__1_once
                    ),
                    _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__1,
                );
                if v_isShared_2354_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2353_, 7);
                    crate::leanh::lean_ctor_set(v___x_2353_, 1, v___x_2357_);
                    crate::leanh::lean_ctor_set(v___x_2353_, 0, v___x_2356_);
                    v___x_2359_ = v___x_2353_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2370_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2370_, 0, v___x_2356_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2370_, 1, v___x_2357_);
                    v___x_2359_ = v_reuseFailAlloc_2370_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_2360_ = l_Lean_MessageData_ofSyntax(v___x_2307_);
                if v_isShared_2346_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2345_, 7);
                    crate::leanh::lean_ctor_set(v___x_2345_, 1, v___x_2360_);
                    crate::leanh::lean_ctor_set(v___x_2345_, 0, v___x_2359_);
                    v___x_2362_ = v___x_2345_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2369_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2369_, 0, v___x_2359_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2369_, 1, v___x_2360_);
                    v___x_2362_ = v_reuseFailAlloc_2369_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2363_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__5
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__5_once
                    ),
                    _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__5,
                );
                if v_isShared_2331_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2330_, 7);
                    crate::leanh::lean_ctor_set(v___x_2330_, 1, v___x_2363_);
                    crate::leanh::lean_ctor_set(v___x_2330_, 0, v___x_2362_);
                    v___x_2365_ = v___x_2330_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2368_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2368_, 0, v___x_2362_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2368_, 1, v___x_2363_);
                    v___x_2365_ = v_reuseFailAlloc_2368_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_2366_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2366_, 0, v___x_2365_);
                crate::leanh::lean_ctor_set(v___x_2366_, 1, v___x_2355_);
                v___x_2367_ = l_Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg(v_stx_2310_, v___x_2366_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_);
                return v___x_2367_;
            }
            10 => {
                if v_isShared_2376_ == 0 {
                    v___x_2378_ = v___x_2375_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2379_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2379_, 0, v_a_2373_);
                    v___x_2378_ = v_reuseFailAlloc_2379_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2378_;
            }
            12 => {
                if v_isShared_2384_ == 0 {
                    v___x_2386_ = v___x_2383_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2387_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2387_, 0, v_a_2381_);
                    v___x_2386_ = v_reuseFailAlloc_2387_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_2386_;
            }
            14 => {
                v___x_2395_ = l_Lean_MessageData_ofSyntax(v___x_2307_);
                v___x_2396_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2396_, 0, v___x_2394_);
                crate::leanh::lean_ctor_set(v___x_2396_, 1, v___x_2395_);
                v___x_2397_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__7
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__7_once
                    ),
                    _init_l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___closed__7,
                );
                v___x_2398_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2398_, 0, v___x_2396_);
                crate::leanh::lean_ctor_set(v___x_2398_, 1, v___x_2397_);
                v___x_2399_ =
                    l_List_foldlM___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0(
                        v_stx_2310_,
                        v___x_2398_,
                        v_fst_2328_,
                        v___y_2314_,
                        v___y_2315_,
                        v___y_2316_,
                        v___y_2317_,
                        v___y_2318_,
                        v___y_2319_,
                    );
                if crate::leanh::lean_obj_tag(v___x_2399_) == 0 {
                    v_a_2400_ = crate::leanh::lean_ctor_get(v___x_2399_, 0);
                    crate::leanh::lean_inc(v_a_2400_);
                    crate::leanh::lean_dec_ref_known(v___x_2399_, 1);
                    v___x_2401_ = l_Lean_throwErrorAt___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__1___redArg(v_stx_2310_, v_a_2400_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_);
                    return v___x_2401_;
                } else {
                    v_a_2402_ = crate::leanh::lean_ctor_get(v___x_2399_, 0);
                    v_isSharedCheck_2409_ = (!crate::leanh::lean_is_exclusive(v___x_2399_)) as u8;
                    if v_isSharedCheck_2409_ == 0 {
                        v___x_2404_ = v___x_2399_;
                        v_isShared_2405_ = v_isSharedCheck_2409_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2402_);
                        crate::leanh::lean_dec(v___x_2399_);
                        v___x_2404_ = crate::leanh::lean_box(0);
                        v_isShared_2405_ = v_isSharedCheck_2409_;
                        state = 15;
                        continue;
                    }
                }
            }
            15 => {
                if v_isShared_2405_ == 0 {
                    v___x_2407_ = v___x_2404_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2408_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2408_, 0, v_a_2402_);
                    v___x_2407_ = v_reuseFailAlloc_2408_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_2407_;
            }
            17 => {
                if v_isShared_2416_ == 0 {
                    v___x_2418_ = v___x_2415_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2419_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2419_, 0, v_a_2413_);
                    v___x_2418_ = v_reuseFailAlloc_2419_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_2418_;
            }
            19 => {
                if v___y_2444_ == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_2441_, 1);
                    crate::leanh::lean_dec(v___x_2309_);
                    crate::leanh::lean_dec(v___x_2307_);
                    state = 1;
                    continue;
                } else {
                    v___y_2325_ = v___x_2441_;
                    state = 2;
                    continue;
                }
            }
            20 => {
                if v_isShared_2450_ == 0 {
                    v___x_2452_ = v___x_2449_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_2453_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2453_, 0, v_a_2447_);
                    v___x_2452_ = v_reuseFailAlloc_2453_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_2452_;
            }
            22 => {
                if v_isShared_2458_ == 0 {
                    v___x_2460_ = v___x_2457_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_2461_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2461_, 0, v_a_2455_);
                    v___x_2460_ = v_reuseFailAlloc_2461_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_2460_;
            }
            24 => {
                if v_isShared_2466_ == 0 {
                    v___x_2468_ = v___x_2465_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_2469_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2469_, 0, v_a_2463_);
                    v___x_2468_ = v_reuseFailAlloc_2469_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_2468_;
            }
            26 => {
                if v_isShared_2474_ == 0 {
                    v___x_2476_ = v___x_2473_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_2477_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2477_, 0, v_a_2471_);
                    v___x_2476_ = v_reuseFailAlloc_2477_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_2476_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___boxed(
    mut v___x_2479_: *mut crate::leanh::LeanObject,
    mut v___x_2480_: *mut crate::leanh::LeanObject,
    mut v___x_2481_: *mut crate::leanh::LeanObject,
    mut v_stx_2482_: *mut crate::leanh::LeanObject,
    mut v___f_2483_: *mut crate::leanh::LeanObject,
    mut v___x_2484_: *mut crate::leanh::LeanObject,
    mut v___vars_2485_: *mut crate::leanh::LeanObject,
    mut v___y_2486_: *mut crate::leanh::LeanObject,
    mut v___y_2487_: *mut crate::leanh::LeanObject,
    mut v___y_2488_: *mut crate::leanh::LeanObject,
    mut v___y_2489_: *mut crate::leanh::LeanObject,
    mut v___y_2490_: *mut crate::leanh::LeanObject,
    mut v___y_2491_: *mut crate::leanh::LeanObject,
    mut v___y_2492_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7169__boxed_2493_: u8 = 0;
    let mut v_res_2494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7169__boxed_2493_ = (crate::leanh::lean_unbox(v___x_2480_) as u8);
    v_res_2494_ = l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0(
        v___x_2479_,
        v___x_7169__boxed_2493_,
        v___x_2481_,
        v_stx_2482_,
        v___f_2483_,
        v___x_2484_,
        v___vars_2485_,
        v___y_2486_,
        v___y_2487_,
        v___y_2488_,
        v___y_2489_,
        v___y_2490_,
        v___y_2491_,
    );
    crate::leanh::lean_dec(v___y_2491_);
    crate::leanh::lean_dec_ref(v___y_2490_);
    crate::leanh::lean_dec(v___y_2489_);
    crate::leanh::lean_dec_ref(v___y_2488_);
    crate::leanh::lean_dec(v___y_2487_);
    crate::leanh::lean_dec_ref(v___y_2486_);
    crate::leanh::lean_dec_ref(v___vars_2485_);
    crate::leanh::lean_dec(v_stx_2482_);
    return v_res_2494_;
}
pub unsafe fn l_Lean_Elab_CheckTactic_elabCheckTacticFailure(
    mut v_stx_2500_: *mut crate::leanh::LeanObject,
    mut v_a_2501_: *mut crate::leanh::LeanObject,
    mut v_a_2502_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2505_: u8 = 0;
    v___x_2504_ = l_Lean_Elab_CheckTactic_elabCheckTacticFailure___closed__1;
    crate::leanh::lean_inc(v_stx_2500_);
    v___x_2505_ = l_Lean_Syntax_isOfKind(v_stx_2500_, v___x_2504_);
    if v___x_2505_ == 0 {
        let mut v___x_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_stx_2500_);
        v___x_2506_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__0___redArg();
        return v___x_2506_;
    } else {
        let mut v___x_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_env_2508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2507_ = lean_st_ref_get(v_a_2502_);
        v_env_2508_ = crate::leanh::lean_ctor_get(v___x_2507_, 0);
        crate::leanh::lean_inc_ref(v_env_2508_);
        crate::leanh::lean_dec(v___x_2507_);
        v___f_2509_ = l_Lean_Elab_CheckTactic_elabCheckTactic___closed__4;
        v___x_2510_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_2511_ = l_Lean_Syntax_getArg(v_stx_2500_, v___x_2510_);
        v___x_2512_ = crate::leanh::lean_unsigned_to_nat(3);
        v___x_2513_ = l_Lean_Syntax_getArg(v_stx_2500_, v___x_2512_);
        v___x_2514_ = crate::leanh::lean_box(0);
        v___x_2515_ = crate::leanh::lean_box((v___x_2505_) as usize);
        v___f_2516_ = crate::leanh::lean_alloc_closure(
            l_Lean_Elab_CheckTactic_elabCheckTacticFailure___lam__0___boxed
                as *mut core::ffi::c_void,
            14,
            6,
        );
        crate::leanh::lean_closure_set(v___f_2516_, 0, v___x_2511_);
        crate::leanh::lean_closure_set(v___f_2516_, 1, v___x_2515_);
        crate::leanh::lean_closure_set(v___f_2516_, 2, v___x_2513_);
        crate::leanh::lean_closure_set(v___f_2516_, 3, v_stx_2500_);
        crate::leanh::lean_closure_set(v___f_2516_, 4, v___f_2509_);
        crate::leanh::lean_closure_set(v___f_2516_, 5, v___x_2514_);
        v___x_2517_ = crate::leanh::lean_alloc_closure(
            l_Lean_Elab_Command_runTermElabM___boxed as *mut core::ffi::c_void,
            5,
            2,
        );
        crate::leanh::lean_closure_set(v___x_2517_, 0, crate::leanh::lean_box(0));
        crate::leanh::lean_closure_set(v___x_2517_, 1, v___f_2516_);
        v___x_2518_ = l_Lean_Environment_unlockAsync(v_env_2508_);
        v___x_2519_ =
            l_Lean_withEnv___at___00Lean_Elab_CheckTactic_elabCheckTactic_spec__2___redArg(
                v___x_2518_,
                v___x_2517_,
                v_a_2501_,
                v_a_2502_,
            );
        return v___x_2519_;
    }
}
pub unsafe fn l_Lean_Elab_CheckTactic_elabCheckTacticFailure___boxed(
    mut v_stx_2520_: *mut crate::leanh::LeanObject,
    mut v_a_2521_: *mut crate::leanh::LeanObject,
    mut v_a_2522_: *mut crate::leanh::LeanObject,
    mut v_a_2523_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2524_ = l_Lean_Elab_CheckTactic_elabCheckTacticFailure(v_stx_2520_, v_a_2521_, v_a_2522_);
    crate::leanh::lean_dec(v_a_2522_);
    crate::leanh::lean_dec_ref(v_a_2521_);
    return v_res_2524_;
}
pub unsafe fn l_List_foldlM___at___00List_foldlM___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0(
    mut v_stx_2525_: *mut crate::leanh::LeanObject,
    mut v_x_2526_: *mut crate::leanh::LeanObject,
    mut v_x_2527_: *mut crate::leanh::LeanObject,
    mut v___y_2528_: *mut crate::leanh::LeanObject,
    mut v___y_2529_: *mut crate::leanh::LeanObject,
    mut v___y_2530_: *mut crate::leanh::LeanObject,
    mut v___y_2531_: *mut crate::leanh::LeanObject,
    mut v___y_2532_: *mut crate::leanh::LeanObject,
    mut v___y_2533_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2535_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0___redArg(v_stx_2525_, v_x_2526_, v_x_2527_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_);
    return v___x_2535_;
}
pub unsafe fn l_List_foldlM___at___00List_foldlM___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0___boxed(
    mut v_stx_2536_: *mut crate::leanh::LeanObject,
    mut v_x_2537_: *mut crate::leanh::LeanObject,
    mut v_x_2538_: *mut crate::leanh::LeanObject,
    mut v___y_2539_: *mut crate::leanh::LeanObject,
    mut v___y_2540_: *mut crate::leanh::LeanObject,
    mut v___y_2541_: *mut crate::leanh::LeanObject,
    mut v___y_2542_: *mut crate::leanh::LeanObject,
    mut v___y_2543_: *mut crate::leanh::LeanObject,
    mut v___y_2544_: *mut crate::leanh::LeanObject,
    mut v___y_2545_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2546_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Elab_CheckTactic_elabCheckTacticFailure_spec__0_spec__0(v_stx_2536_, v_x_2537_, v_x_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_);
    crate::leanh::lean_dec(v___y_2544_);
    crate::leanh::lean_dec_ref(v___y_2543_);
    crate::leanh::lean_dec(v___y_2542_);
    crate::leanh::lean_dec_ref(v___y_2541_);
    crate::leanh::lean_dec(v___y_2540_);
    crate::leanh::lean_dec_ref(v___y_2539_);
    crate::leanh::lean_dec(v_stx_2536_);
    return v_res_2546_;
}
pub unsafe fn l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2554_ = l_Lean_Elab_Command_commandElabAttribute;
    v___x_2555_ = l_Lean_Elab_CheckTactic_elabCheckTacticFailure___closed__1;
    v___x_2556_ = l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1___closed__1;
    v___x_2557_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_CheckTactic_elabCheckTacticFailure___boxed as *mut core::ffi::c_void,
        4,
        0,
    );
    v___x_2558_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_2554_,
        v___x_2555_,
        v___x_2556_,
        v___x_2557_,
    );
    return v___x_2558_;
}
pub unsafe fn l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1___boxed(
    mut v_a_2559_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2560_ = l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1();
    return v_res_2560_;
}
pub unsafe fn l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2587_ = l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1___closed__1;
    v___x_2588_ = l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___closed__6;
    v___x_2589_ = l_Lean_addBuiltinDeclarationRanges(v___x_2587_, v___x_2588_);
    return v___x_2589_;
}
pub unsafe fn l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3___boxed(
    mut v_a_2590_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2591_ = l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3();
    return v_res_2591_;
}
pub unsafe fn _init_l_Lean_Elab_CheckTactic_expandCheckSimp___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2616_ = l_Array_mkArray0(crate::leanh::lean_box(0));
    return v___x_2616_;
}
pub unsafe fn l_Lean_Elab_CheckTactic_expandCheckSimp(
    mut v_stx_2617_: *mut crate::leanh::LeanObject,
    mut v_a_2618_: *mut crate::leanh::LeanObject,
    mut v_a_2619_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2621_: u8 = 0;
    v___x_2620_ = l_Lean_Elab_CheckTactic_expandCheckSimp___closed__1;
    crate::leanh::lean_inc(v_stx_2617_);
    v___x_2621_ = l_Lean_Syntax_isOfKind(v_stx_2617_, v___x_2620_);
    if v___x_2621_ == 0 {
        let mut v___x_2622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_stx_2617_);
        v___x_2622_ = l_Lean_Macro_throwUnsupported___redArg(v_a_2619_);
        return v___x_2622_;
    } else {
        let mut v_ref_2623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2628_: u8 = 0;
        let mut v___x_2629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_ref_2623_ = crate::leanh::lean_ctor_get(v_a_2618_, 5);
        v___x_2624_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_2625_ = l_Lean_Syntax_getArg(v_stx_2617_, v___x_2624_);
        v___x_2626_ = crate::leanh::lean_unsigned_to_nat(3);
        v___x_2627_ = l_Lean_Syntax_getArg(v_stx_2617_, v___x_2626_);
        crate::leanh::lean_dec(v_stx_2617_);
        v___x_2628_ = 0;
        v___x_2629_ = l_Lean_SourceInfo_fromRef(v_ref_2623_, v___x_2628_);
        v___x_2630_ = l_Lean_Elab_CheckTactic_elabCheckTactic___closed__3;
        v___x_2631_ = l_Lean_Elab_CheckTactic_expandCheckSimp___closed__2;
        crate::leanh::lean_inc_n(v___x_2629_, 7);
        v___x_2632_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2632_, 0, v___x_2629_);
        crate::leanh::lean_ctor_set(v___x_2632_, 1, v___x_2631_);
        v___x_2633_ = l_Lean_Elab_CheckTactic_expandCheckSimp___closed__3;
        v___x_2634_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2634_, 0, v___x_2629_);
        crate::leanh::lean_ctor_set(v___x_2634_, 1, v___x_2633_);
        v___x_2635_ = l_Lean_Elab_CheckTactic_expandCheckSimp___closed__4;
        v___x_2636_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2636_, 0, v___x_2629_);
        crate::leanh::lean_ctor_set(v___x_2636_, 1, v___x_2635_);
        v___x_2637_ = l_Lean_Elab_CheckTactic_expandCheckSimp___closed__6;
        v___x_2638_ = l_Lean_Elab_CheckTactic_expandCheckSimp___closed__7;
        v___x_2639_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2639_, 0, v___x_2629_);
        crate::leanh::lean_ctor_set(v___x_2639_, 1, v___x_2637_);
        v___x_2640_ = l_Lean_Elab_CheckTactic_expandCheckSimp___closed__9;
        v___x_2641_ = l_Lean_Elab_CheckTactic_expandCheckSimp___closed__11;
        v___x_2642_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__12),
            core::ptr::addr_of_mut!(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__12_once),
            _init_l_Lean_Elab_CheckTactic_expandCheckSimp___closed__12,
        );
        v___x_2643_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2643_, 0, v___x_2629_);
        crate::leanh::lean_ctor_set(v___x_2643_, 1, v___x_2641_);
        crate::leanh::lean_ctor_set(v___x_2643_, 2, v___x_2642_);
        crate::leanh::lean_inc_ref_n(v___x_2643_, 4);
        v___x_2644_ = l_Lean_Syntax_node1(v___x_2629_, v___x_2640_, v___x_2643_);
        v___x_2645_ = l_Lean_Syntax_node6(
            v___x_2629_,
            v___x_2638_,
            v___x_2639_,
            v___x_2644_,
            v___x_2643_,
            v___x_2643_,
            v___x_2643_,
            v___x_2643_,
        );
        v___x_2646_ = l_Lean_Syntax_node6(
            v___x_2629_,
            v___x_2630_,
            v___x_2632_,
            v___x_2625_,
            v___x_2634_,
            v___x_2627_,
            v___x_2636_,
            v___x_2645_,
        );
        v___x_2647_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2647_, 0, v___x_2646_);
        crate::leanh::lean_ctor_set(v___x_2647_, 1, v_a_2619_);
        return v___x_2647_;
    }
}
pub unsafe fn l_Lean_Elab_CheckTactic_expandCheckSimp___boxed(
    mut v_stx_2648_: *mut crate::leanh::LeanObject,
    mut v_a_2649_: *mut crate::leanh::LeanObject,
    mut v_a_2650_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2651_ = l_Lean_Elab_CheckTactic_expandCheckSimp(v_stx_2648_, v_a_2649_, v_a_2650_);
    crate::leanh::lean_dec_ref(v_a_2649_);
    return v_res_2651_;
}
pub unsafe fn l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2659_ = l_Lean_Elab_macroAttribute;
    v___x_2660_ = l_Lean_Elab_CheckTactic_expandCheckSimp___closed__1;
    v___x_2661_ = l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___closed__1;
    v___x_2662_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_CheckTactic_expandCheckSimp___boxed as *mut core::ffi::c_void,
        3,
        0,
    );
    v___x_2663_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_2659_,
        v___x_2660_,
        v___x_2661_,
        v___x_2662_,
    );
    return v___x_2663_;
}
pub unsafe fn l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___boxed(
    mut v_a_2664_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2665_ = l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1();
    return v_res_2665_;
}
pub unsafe fn l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2692_ = l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1___closed__1;
    v___x_2693_ = l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___closed__6;
    v___x_2694_ = l_Lean_addBuiltinDeclarationRanges(v___x_2692_, v___x_2693_);
    return v___x_2694_;
}
pub unsafe fn l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3___boxed(
    mut v_a_2695_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2696_ = l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3();
    return v_res_2696_;
}
pub unsafe fn l_Lean_Elab_CheckTactic_expandCheckSimpFailure(
    mut v_stx_2703_: *mut crate::leanh::LeanObject,
    mut v_a_2704_: *mut crate::leanh::LeanObject,
    mut v_a_2705_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2707_: u8 = 0;
    v___x_2706_ = l_Lean_Elab_CheckTactic_expandCheckSimpFailure___closed__1;
    crate::leanh::lean_inc(v_stx_2703_);
    v___x_2707_ = l_Lean_Syntax_isOfKind(v_stx_2703_, v___x_2706_);
    if v___x_2707_ == 0 {
        let mut v___x_2708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_stx_2703_);
        v___x_2708_ = l_Lean_Macro_throwUnsupported___redArg(v_a_2705_);
        return v___x_2708_;
    } else {
        let mut v_ref_2709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2712_: u8 = 0;
        let mut v___x_2713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_ref_2709_ = crate::leanh::lean_ctor_get(v_a_2704_, 5);
        v___x_2710_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_2711_ = l_Lean_Syntax_getArg(v_stx_2703_, v___x_2710_);
        crate::leanh::lean_dec(v_stx_2703_);
        v___x_2712_ = 0;
        v___x_2713_ = l_Lean_SourceInfo_fromRef(v_ref_2709_, v___x_2712_);
        v___x_2714_ = l_Lean_Elab_CheckTactic_elabCheckTacticFailure___closed__1;
        v___x_2715_ = l_Lean_Elab_CheckTactic_expandCheckSimpFailure___closed__2;
        crate::leanh::lean_inc_n(v___x_2713_, 6);
        v___x_2716_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2716_, 0, v___x_2713_);
        crate::leanh::lean_ctor_set(v___x_2716_, 1, v___x_2715_);
        v___x_2717_ = l_Lean_Elab_CheckTactic_expandCheckSimp___closed__4;
        v___x_2718_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2718_, 0, v___x_2713_);
        crate::leanh::lean_ctor_set(v___x_2718_, 1, v___x_2717_);
        v___x_2719_ = l_Lean_Elab_CheckTactic_expandCheckSimp___closed__6;
        v___x_2720_ = l_Lean_Elab_CheckTactic_expandCheckSimp___closed__7;
        v___x_2721_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2721_, 0, v___x_2713_);
        crate::leanh::lean_ctor_set(v___x_2721_, 1, v___x_2719_);
        v___x_2722_ = l_Lean_Elab_CheckTactic_expandCheckSimp___closed__9;
        v___x_2723_ = l_Lean_Elab_CheckTactic_expandCheckSimp___closed__11;
        v___x_2724_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__12),
            core::ptr::addr_of_mut!(l_Lean_Elab_CheckTactic_expandCheckSimp___closed__12_once),
            _init_l_Lean_Elab_CheckTactic_expandCheckSimp___closed__12,
        );
        v___x_2725_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2725_, 0, v___x_2713_);
        crate::leanh::lean_ctor_set(v___x_2725_, 1, v___x_2723_);
        crate::leanh::lean_ctor_set(v___x_2725_, 2, v___x_2724_);
        crate::leanh::lean_inc_ref_n(v___x_2725_, 4);
        v___x_2726_ = l_Lean_Syntax_node1(v___x_2713_, v___x_2722_, v___x_2725_);
        v___x_2727_ = l_Lean_Syntax_node6(
            v___x_2713_,
            v___x_2720_,
            v___x_2721_,
            v___x_2726_,
            v___x_2725_,
            v___x_2725_,
            v___x_2725_,
            v___x_2725_,
        );
        v___x_2728_ = l_Lean_Syntax_node4(
            v___x_2713_,
            v___x_2714_,
            v___x_2716_,
            v___x_2711_,
            v___x_2718_,
            v___x_2727_,
        );
        v___x_2729_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2729_, 0, v___x_2728_);
        crate::leanh::lean_ctor_set(v___x_2729_, 1, v_a_2705_);
        return v___x_2729_;
    }
}
pub unsafe fn l_Lean_Elab_CheckTactic_expandCheckSimpFailure___boxed(
    mut v_stx_2730_: *mut crate::leanh::LeanObject,
    mut v_a_2731_: *mut crate::leanh::LeanObject,
    mut v_a_2732_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2733_ = l_Lean_Elab_CheckTactic_expandCheckSimpFailure(v_stx_2730_, v_a_2731_, v_a_2732_);
    crate::leanh::lean_dec_ref(v_a_2731_);
    return v_res_2733_;
}
pub unsafe fn l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2741_ = l_Lean_Elab_macroAttribute;
    v___x_2742_ = l_Lean_Elab_CheckTactic_expandCheckSimpFailure___closed__1;
    v___x_2743_ = l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1___closed__1;
    v___x_2744_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_CheckTactic_expandCheckSimpFailure___boxed as *mut core::ffi::c_void,
        3,
        0,
    );
    v___x_2745_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_2741_,
        v___x_2742_,
        v___x_2743_,
        v___x_2744_,
    );
    return v___x_2745_;
}
pub unsafe fn l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1___boxed(
    mut v_a_2746_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2747_ = l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1();
    return v_res_2747_;
}
pub unsafe fn l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2774_ = l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1___closed__1;
    v___x_2775_ = l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___closed__6;
    v___x_2776_ = l_Lean_addBuiltinDeclarationRanges(v___x_2774_, v___x_2775_);
    return v___x_2776_;
}
pub unsafe fn l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3___boxed(
    mut v_a_2777_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2778_ = l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3();
    return v_res_2778_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_CheckTactic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Tactic_ElabTerm(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Command(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Meta(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_CheckTactic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTactic___regBuiltin_Lean_Elab_CheckTactic_elabCheckTactic_declRange__3();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_elabCheckTacticFailure___regBuiltin_Lean_Elab_CheckTactic_elabCheckTacticFailure_declRange__3();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimp___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimp_declRange__3();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_CheckTactic_0__Lean_Elab_CheckTactic_expandCheckSimpFailure___regBuiltin_Lean_Elab_CheckTactic_expandCheckSimpFailure_declRange__3();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_CheckTactic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_CheckTactic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Tactic_ElabTerm(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Command(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Meta(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_CheckTactic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_CheckTactic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_CheckTactic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_CheckTactic(builtin);
}
