// Lean compiler output
// Module: Lean.Elab.Tactic.BVDecide.BVCheck
// Imports: Lean.Elab.Tactic.BVDecide.BVDecide Lean.Meta.Tactic.TryThis Lean.Meta.Tactic.BVDecide.TacticContext Lean.Meta.Tactic.BVDecide.Normalize
use crate::ffi::{lean_st_ref_get, lean_st_ref_set, lean_st_ref_take, lean_string_dec_eq};
use crate::r#gen::Init::Meta::Defs::l_Lean_TSyntax_getString;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr4, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_getPos_x3f,
    l_Lean_Syntax_getTailPos_x3f, l_Lean_Syntax_isOfKind, l_Lean_Syntax_node2, l_Lean_replaceRef,
};
use crate::r#gen::Init::System::FilePath::{l_System_FilePath_join, l_System_FilePath_parent};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::Position::l_Lean_FileMap_toPosition;
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::Tactic::BVDecide::BVDecide::{
    initialize_Lean_Elab_Tactic_BVDecide_BVDecide,
    runtime_initialize_Lean_Elab_Tactic_BVDecide_BVDecide,
};
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    l_Lean_Elab_Tactic_getMainGoal___redArg, l_Lean_Elab_Tactic_replaceMainGoal___redArg,
    l_Lean_Elab_Tactic_tacticElabAttribute, l_Lean_Elab_Tactic_withMainContext___redArg,
};
use crate::r#gen::Lean::Elab::Util::{l_Lean_Elab_getBetterRef, l_Lean_Elab_pp_macroStack};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Log::{
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed, l_Lean_warningAsError,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_hasSyntheticSorry, l_Lean_MessageData_hasTag, l_Lean_MessageData_nil,
    l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofSyntax, l_Lean_MessageLog_add,
    l_Lean_indentD, l_Lean_instBEqMessageSeverity_beq, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Tactic::BVDecide::Attr::l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg;
use crate::r#gen::Lean::Meta::Tactic::BVDecide::Normalize::{
    initialize_Lean_Meta_Tactic_BVDecide_Normalize,
    l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize,
    runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize,
};
use crate::r#gen::Lean::Meta::Tactic::BVDecide::Prover::Basic::l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg;
use crate::r#gen::Lean::Meta::Tactic::BVDecide::Prover::Bitblast::l_Lean_Meta_Tactic_BVDecide_lratChecker___boxed;
use crate::r#gen::Lean::Meta::Tactic::BVDecide::TacticContext::{
    initialize_Lean_Meta_Tactic_BVDecide_TacticContext,
    l_Lean_Meta_Tactic_BVDecide_TacticContext_new,
    runtime_initialize_Lean_Meta_Tactic_BVDecide_TacticContext,
};
use crate::r#gen::Lean::Meta::Tactic::TryThis::{
    initialize_Lean_Meta_Tactic_TryThis, l_Lean_Meta_Tactic_TryThis_addSuggestion,
    runtime_initialize_Lean_Meta_Tactic_TryThis,
};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__1_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__2_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg___closed__0_value: crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__0_value:
    crate::leanh::LeanStringObject<37> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 37,
    m_capacity: 37,
    m_length: 36,
    m_data: [
        99, 97, 110, 110, 111, 116, 32, 99, 111, 109, 112, 117, 116, 101, 32, 112, 97, 114, 101,
        110, 116, 32, 100, 105, 114, 101, 99, 116, 111, 114, 121, 32, 111, 102, 32, 96, 0,
    ],
};
static mut l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__2_value:
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
    m_data: [96, 0],
};
static mut l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__2_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [117, 110, 115, 111, 108, 118, 101, 100, 71, 111, 97, 108, 115, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__3_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 121, 110, 116, 104, 80, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__4_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 101, 97, 110, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__5_value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 110, 100, 117, 99, 116, 105, 111, 110, 87, 105, 116, 104, 78, 111, 65, 108, 116, 115, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__6_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [95, 110, 97, 109, 101, 100, 69, 114, 114, 111, 114, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__7_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___closed__0_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<94> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 94,
    m_capacity: 94,
    m_length: 93,
    m_data: [
        84, 104, 105, 115, 32, 103, 111, 97, 108, 32, 99, 97, 110, 32, 98, 101, 32, 99, 108, 111,
        115, 101, 100, 32, 98, 121, 32, 111, 110, 108, 121, 32, 97, 112, 112, 108, 121, 105, 110,
        103, 32, 98, 118, 95, 110, 111, 114, 109, 97, 108, 105, 122, 101, 44, 32, 110, 111, 32,
        110, 101, 101, 100, 32, 116, 111, 32, 107, 101, 101, 112, 32, 116, 104, 101, 32, 76, 82,
        65, 84, 32, 112, 114, 111, 111, 102, 32, 97, 114, 111, 117, 110, 100, 46, 0,
    ],
};
static mut l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__2_value:
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
    m_data: [98, 118, 95, 110, 111, 114, 109, 97, 108, 105, 122, 101, 0],
};
static mut l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__3_value:
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
    m_data: [116, 97, 99, 116, 105, 99, 0],
};
static mut l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__4_value:
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
            l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__3_value
        ) as *mut crate::leanh::LeanObject,
        16145843736367156323 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__5_value:
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
    m_data: [98, 118, 78, 111, 114, 109, 97, 108, 105, 122, 101, 0],
};
static mut l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__6_value:
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
    m_data: [84, 114, 121, 32, 116, 104, 105, 115, 58, 0],
};
static mut l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__0_value:
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
static mut l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__1_value:
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
static mut l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__2_value:
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
    m_data: [98, 118, 67, 104, 101, 99, 107, 0],
};
static mut l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__3_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__3_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__3_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__3_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__3_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__2_value)
            as *mut crate::leanh::LeanObject,
        6595225419433550061 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__4_value:
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
static mut l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__4_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__5_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__5_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__5_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__5_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__5_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__5_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__5_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__4_value)
            as *mut crate::leanh::LeanObject,
        3488656302031949961 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__6_value:
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
    m_data: [115, 116, 114, 0],
};
static mut l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__7_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__6_value)
            as *mut crate::leanh::LeanObject,
        9232979286016572671 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1___closed__0_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [66, 86, 68, 101, 99, 105, 100, 101, 0]};
static mut l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1___closed__1_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [66, 86, 67, 104, 101, 99, 107, 0]};
static mut l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1___closed__2_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [101, 118, 97, 108, 66, 118, 67, 104, 101, 99, 107, 0]};
static mut l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1___closed__2_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,12733524109236233889 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1___closed__3_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1___closed__3_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1___closed__0_value) as *mut crate::leanh::LeanObject,11988787035136614332 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1___closed__3_value_aux_4: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1___closed__3_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1___closed__1_value) as *mut crate::leanh::LeanObject,16103818036193806685 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1___closed__3_value_aux_4) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1___closed__2_value) as *mut crate::leanh::LeanObject,6427436024425481910 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__0(
    mut v_msgData_733_: *mut crate::leanh::LeanObject,
    mut v___y_734_: *mut crate::leanh::LeanObject,
    mut v___y_735_: *mut crate::leanh::LeanObject,
    mut v___y_736_: *mut crate::leanh::LeanObject,
    mut v___y_737_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_739_ = lean_st_ref_get(v___y_737_);
    v_env_740_ = crate::leanh::lean_ctor_get(v___x_739_, 0);
    crate::leanh::lean_inc_ref(v_env_740_);
    crate::leanh::lean_dec(v___x_739_);
    v___x_741_ = lean_st_ref_get(v___y_735_);
    v_mctx_742_ = crate::leanh::lean_ctor_get(v___x_741_, 0);
    crate::leanh::lean_inc_ref(v_mctx_742_);
    crate::leanh::lean_dec(v___x_741_);
    v_lctx_743_ = crate::leanh::lean_ctor_get(v___y_734_, 2);
    v_options_744_ = crate::leanh::lean_ctor_get(v___y_736_, 2);
    crate::leanh::lean_inc_ref(v_options_744_);
    crate::leanh::lean_inc_ref(v_lctx_743_);
    v___x_745_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_745_, 0, v_env_740_);
    crate::leanh::lean_ctor_set(v___x_745_, 1, v_mctx_742_);
    crate::leanh::lean_ctor_set(v___x_745_, 2, v_lctx_743_);
    crate::leanh::lean_ctor_set(v___x_745_, 3, v_options_744_);
    v___x_746_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_746_, 0, v___x_745_);
    crate::leanh::lean_ctor_set(v___x_746_, 1, v_msgData_733_);
    v___x_747_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_747_, 0, v___x_746_);
    return v___x_747_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__0___boxed(
    mut v_msgData_748_: *mut crate::leanh::LeanObject,
    mut v___y_749_: *mut crate::leanh::LeanObject,
    mut v___y_750_: *mut crate::leanh::LeanObject,
    mut v___y_751_: *mut crate::leanh::LeanObject,
    mut v___y_752_: *mut crate::leanh::LeanObject,
    mut v___y_753_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_754_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__0(v_msgData_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_);
    crate::leanh::lean_dec(v___y_752_);
    crate::leanh::lean_dec_ref(v___y_751_);
    crate::leanh::lean_dec(v___y_750_);
    crate::leanh::lean_dec_ref(v___y_749_);
    return v_res_754_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_755_ = crate::leanh::lean_box(1);
    v___x_756_ = l_Lean_MessageData_ofFormat(v___x_755_);
    return v___x_756_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_760_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__2;
    v___x_761_ = l_Lean_MessageData_ofFormat(v___x_760_);
    return v___x_761_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3(
    mut v_x_762_: *mut crate::leanh::LeanObject,
    mut v_x_763_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_768_: u8 = 0;
    let mut v_before_769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_772_: u8 = 0;
    let mut v___x_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_785_: u8 = 0;
    let mut v_unused_786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_787_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_763_) == 0 {
                    return v_x_762_;
                } else {
                    v_head_764_ = crate::leanh::lean_ctor_get(v_x_763_, 0);
                    v_tail_765_ = crate::leanh::lean_ctor_get(v_x_763_, 1);
                    v_isSharedCheck_787_ = (!crate::leanh::lean_is_exclusive(v_x_763_)) as u8;
                    if v_isSharedCheck_787_ == 0 {
                        v___x_767_ = v_x_763_;
                        v_isShared_768_ = v_isSharedCheck_787_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_765_);
                        crate::leanh::lean_inc(v_head_764_);
                        crate::leanh::lean_dec(v_x_763_);
                        v___x_767_ = crate::leanh::lean_box(0);
                        v_isShared_768_ = v_isSharedCheck_787_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_769_ = crate::leanh::lean_ctor_get(v_head_764_, 0);
                v_isSharedCheck_785_ = (!crate::leanh::lean_is_exclusive(v_head_764_)) as u8;
                if v_isSharedCheck_785_ == 0 {
                    v_unused_786_ = crate::leanh::lean_ctor_get(v_head_764_, 1);
                    crate::leanh::lean_dec(v_unused_786_);
                    v___x_771_ = v_head_764_;
                    v_isShared_772_ = v_isSharedCheck_785_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_before_769_);
                    crate::leanh::lean_dec(v_head_764_);
                    v___x_771_ = crate::leanh::lean_box(0);
                    v_isShared_772_ = v_isSharedCheck_785_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_773_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__0);
                if v_isShared_772_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_771_, 7);
                    crate::leanh::lean_ctor_set(v___x_771_, 1, v___x_773_);
                    crate::leanh::lean_ctor_set(v___x_771_, 0, v_x_762_);
                    v___x_775_ = v___x_771_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_784_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_784_, 0, v_x_762_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_784_, 1, v___x_773_);
                    v___x_775_ = v_reuseFailAlloc_784_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_776_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__3);
                if v_isShared_768_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_767_, 7);
                    crate::leanh::lean_ctor_set(v___x_767_, 1, v___x_776_);
                    crate::leanh::lean_ctor_set(v___x_767_, 0, v___x_775_);
                    v___x_778_ = v___x_767_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_783_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_783_, 0, v___x_775_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_783_, 1, v___x_776_);
                    v___x_778_ = v_reuseFailAlloc_783_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_779_ = l_Lean_MessageData_ofSyntax(v_before_769_);
                v___x_780_ = l_Lean_indentD(v___x_779_);
                v___x_781_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_781_, 0, v___x_778_);
                crate::leanh::lean_ctor_set(v___x_781_, 1, v___x_780_);
                v_x_762_ = v___x_781_;
                v_x_763_ = v_tail_765_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__2(
    mut v_opts_788_: *mut crate::leanh::LeanObject,
    mut v_opt_789_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_790_ = crate::leanh::lean_ctor_get(v_opt_789_, 0);
    v_defValue_791_ = crate::leanh::lean_ctor_get(v_opt_789_, 1);
    v_map_792_ = crate::leanh::lean_ctor_get(v_opts_788_, 0);
    v___x_793_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_792_,
            v_name_790_,
        );
    if crate::leanh::lean_obj_tag(v___x_793_) == 0 {
        let mut v___x_794_: u8 = 0;
        v___x_794_ = (crate::leanh::lean_unbox(v_defValue_791_) as u8);
        return v___x_794_;
    } else {
        let mut v_val_795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_795_ = crate::leanh::lean_ctor_get(v___x_793_, 0);
        crate::leanh::lean_inc(v_val_795_);
        crate::leanh::lean_dec_ref_known(v___x_793_, 1);
        if crate::leanh::lean_obj_tag(v_val_795_) == 1 {
            let mut v_v_796_: u8 = 0;
            v_v_796_ = crate::leanh::lean_ctor_get_uint8(v_val_795_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_795_, 0);
            return v_v_796_;
        } else {
            let mut v___x_797_: u8 = 0;
            crate::leanh::lean_dec(v_val_795_);
            v___x_797_ = (crate::leanh::lean_unbox(v_defValue_791_) as u8);
            return v___x_797_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__2___boxed(
    mut v_opts_798_: *mut crate::leanh::LeanObject,
    mut v_opt_799_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_800_: u8 = 0;
    let mut v_r_801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_800_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__2(v_opts_798_, v_opt_799_);
    crate::leanh::lean_dec_ref(v_opt_799_);
    crate::leanh::lean_dec_ref(v_opts_798_);
    v_r_801_ = crate::leanh::lean_box((v_res_800_) as usize);
    return v_r_801_;
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_805_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg___closed__1;
    v___x_806_ = l_Lean_MessageData_ofFormat(v___x_805_);
    return v___x_806_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg(
    mut v_msgData_807_: *mut crate::leanh::LeanObject,
    mut v_macroStack_808_: *mut crate::leanh::LeanObject,
    mut v___y_809_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_813_: u8 = 0;
    let mut v___x_814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_after_817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_820_: u8 = 0;
    let mut v___x_821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgData_828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_832_: u8 = 0;
    let mut v_unused_833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_811_ = crate::leanh::lean_ctor_get(v___y_809_, 2);
                v___x_812_ = l_Lean_Elab_pp_macroStack;
                v___x_813_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__2(v_options_811_, v___x_812_);
                if v___x_813_ == 0 {
                    crate::leanh::lean_dec(v_macroStack_808_);
                    v___x_814_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_814_, 0, v_msgData_807_);
                    return v___x_814_;
                } else {
                    if crate::leanh::lean_obj_tag(v_macroStack_808_) == 0 {
                        v___x_815_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_815_, 0, v_msgData_807_);
                        return v___x_815_;
                    } else {
                        v_head_816_ = crate::leanh::lean_ctor_get(v_macroStack_808_, 0);
                        crate::leanh::lean_inc(v_head_816_);
                        v_after_817_ = crate::leanh::lean_ctor_get(v_head_816_, 1);
                        v_isSharedCheck_832_ =
                            (!crate::leanh::lean_is_exclusive(v_head_816_)) as u8;
                        if v_isSharedCheck_832_ == 0 {
                            v_unused_833_ = crate::leanh::lean_ctor_get(v_head_816_, 0);
                            crate::leanh::lean_dec(v_unused_833_);
                            v___x_819_ = v_head_816_;
                            v_isShared_820_ = v_isSharedCheck_832_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_after_817_);
                            crate::leanh::lean_dec(v_head_816_);
                            v___x_819_ = crate::leanh::lean_box(0);
                            v_isShared_820_ = v_isSharedCheck_832_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_821_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3___closed__0);
                if v_isShared_820_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_819_, 7);
                    crate::leanh::lean_ctor_set(v___x_819_, 1, v___x_821_);
                    crate::leanh::lean_ctor_set(v___x_819_, 0, v_msgData_807_);
                    v___x_823_ = v___x_819_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_831_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_831_, 0, v_msgData_807_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_831_, 1, v___x_821_);
                    v___x_823_ = v_reuseFailAlloc_831_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_824_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg___closed__2);
                v___x_825_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_825_, 0, v___x_823_);
                crate::leanh::lean_ctor_set(v___x_825_, 1, v___x_824_);
                v___x_826_ = l_Lean_MessageData_ofSyntax(v_after_817_);
                v___x_827_ = l_Lean_indentD(v___x_826_);
                v_msgData_828_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v_msgData_828_, 0, v___x_825_);
                crate::leanh::lean_ctor_set(v_msgData_828_, 1, v___x_827_);
                v___x_829_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__3(v_msgData_828_, v_macroStack_808_);
                v___x_830_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_830_, 0, v___x_829_);
                return v___x_830_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg___boxed(
    mut v_msgData_834_: *mut crate::leanh::LeanObject,
    mut v_macroStack_835_: *mut crate::leanh::LeanObject,
    mut v___y_836_: *mut crate::leanh::LeanObject,
    mut v___y_837_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_838_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg(v_msgData_834_, v_macroStack_835_, v___y_836_);
    crate::leanh::lean_dec_ref(v___y_836_);
    return v_res_838_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0___redArg(
    mut v_msg_839_: *mut crate::leanh::LeanObject,
    mut v___y_840_: *mut crate::leanh::LeanObject,
    mut v___y_841_: *mut crate::leanh::LeanObject,
    mut v___y_842_: *mut crate::leanh::LeanObject,
    mut v___y_843_: *mut crate::leanh::LeanObject,
    mut v___y_844_: *mut crate::leanh::LeanObject,
    mut v___y_845_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_856_: u8 = 0;
    let mut v___x_857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_861_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_847_ = crate::leanh::lean_ctor_get(v___y_844_, 5);
                v___x_848_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__0(v_msg_839_, v___y_842_, v___y_843_, v___y_844_, v___y_845_);
                v_a_849_ = crate::leanh::lean_ctor_get(v___x_848_, 0);
                crate::leanh::lean_inc(v_a_849_);
                crate::leanh::lean_dec_ref(v___x_848_);
                v_macroStack_850_ = crate::leanh::lean_ctor_get(v___y_840_, 1);
                v___x_851_ = l_Lean_Elab_getBetterRef(v_ref_847_, v_macroStack_850_);
                crate::leanh::lean_inc(v_macroStack_850_);
                v___x_852_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg(v_a_849_, v_macroStack_850_, v___y_844_);
                v_a_853_ = crate::leanh::lean_ctor_get(v___x_852_, 0);
                v_isSharedCheck_861_ = (!crate::leanh::lean_is_exclusive(v___x_852_)) as u8;
                if v_isSharedCheck_861_ == 0 {
                    v___x_855_ = v___x_852_;
                    v_isShared_856_ = v_isSharedCheck_861_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_853_);
                    crate::leanh::lean_dec(v___x_852_);
                    v___x_855_ = crate::leanh::lean_box(0);
                    v_isShared_856_ = v_isSharedCheck_861_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_857_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_857_, 0, v___x_851_);
                crate::leanh::lean_ctor_set(v___x_857_, 1, v_a_853_);
                if v_isShared_856_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_855_, 1);
                    crate::leanh::lean_ctor_set(v___x_855_, 0, v___x_857_);
                    v___x_859_ = v___x_855_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_860_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_860_, 0, v___x_857_);
                    v___x_859_ = v_reuseFailAlloc_860_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_859_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0___redArg___boxed(
    mut v_msg_862_: *mut crate::leanh::LeanObject,
    mut v___y_863_: *mut crate::leanh::LeanObject,
    mut v___y_864_: *mut crate::leanh::LeanObject,
    mut v___y_865_: *mut crate::leanh::LeanObject,
    mut v___y_866_: *mut crate::leanh::LeanObject,
    mut v___y_867_: *mut crate::leanh::LeanObject,
    mut v___y_868_: *mut crate::leanh::LeanObject,
    mut v___y_869_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_870_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0___redArg(
            v_msg_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_,
        );
    crate::leanh::lean_dec(v___y_868_);
    crate::leanh::lean_dec_ref(v___y_867_);
    crate::leanh::lean_dec(v___y_866_);
    crate::leanh::lean_dec_ref(v___y_865_);
    crate::leanh::lean_dec(v___y_864_);
    crate::leanh::lean_dec_ref(v___y_863_);
    return v_res_870_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_872_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__0;
    v___x_873_ = l_Lean_stringToMessageData(v___x_872_);
    return v___x_873_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_875_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__2;
    v___x_876_ = l_Lean_stringToMessageData(v___x_875_);
    return v___x_876_;
}
pub unsafe fn l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir(
    mut v_a_877_: *mut crate::leanh::LeanObject,
    mut v_a_878_: *mut crate::leanh::LeanObject,
    mut v_a_879_: *mut crate::leanh::LeanObject,
    mut v_a_880_: *mut crate::leanh::LeanObject,
    mut v_a_881_: *mut crate::leanh::LeanObject,
    mut v_a_882_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_889_: u8 = 0;
    let mut v___x_891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_893_: u8 = 0;
    let mut v___x_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_884_ = crate::leanh::lean_ctor_get(v_a_881_, 0);
                crate::leanh::lean_inc_ref(v_fileName_884_);
                v___x_885_ = l_System_FilePath_parent(v_fileName_884_);
                if crate::leanh::lean_obj_tag(v___x_885_) == 1 {
                    v_val_886_ = crate::leanh::lean_ctor_get(v___x_885_, 0);
                    v_isSharedCheck_893_ = (!crate::leanh::lean_is_exclusive(v___x_885_)) as u8;
                    if v_isSharedCheck_893_ == 0 {
                        v___x_888_ = v___x_885_;
                        v_isShared_889_ = v_isSharedCheck_893_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_886_);
                        crate::leanh::lean_dec(v___x_885_);
                        v___x_888_ = crate::leanh::lean_box(0);
                        v_isShared_889_ = v_isSharedCheck_893_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_885_);
                    v___x_894_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__1_once
                        ),
                        _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__1,
                    );
                    crate::leanh::lean_inc_ref(v_fileName_884_);
                    v___x_895_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_895_, 0, v_fileName_884_);
                    v___x_896_ = l_Lean_MessageData_ofFormat(v___x_895_);
                    v___x_897_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_897_, 0, v___x_894_);
                    crate::leanh::lean_ctor_set(v___x_897_, 1, v___x_896_);
                    v___x_898_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__3_once
                        ),
                        _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___closed__3,
                    );
                    v___x_899_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_899_, 0, v___x_897_);
                    crate::leanh::lean_ctor_set(v___x_899_, 1, v___x_898_);
                    v___x_900_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0___redArg(v___x_899_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_);
                    return v___x_900_;
                }
            }
            1 => {
                if v_isShared_889_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_888_, 0);
                    v___x_891_ = v___x_888_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_892_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_892_, 0, v_val_886_);
                    v___x_891_ = v_reuseFailAlloc_892_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_891_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir___boxed(
    mut v_a_901_: *mut crate::leanh::LeanObject,
    mut v_a_902_: *mut crate::leanh::LeanObject,
    mut v_a_903_: *mut crate::leanh::LeanObject,
    mut v_a_904_: *mut crate::leanh::LeanObject,
    mut v_a_905_: *mut crate::leanh::LeanObject,
    mut v_a_906_: *mut crate::leanh::LeanObject,
    mut v_a_907_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_908_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir(
        v_a_901_, v_a_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_,
    );
    crate::leanh::lean_dec(v_a_906_);
    crate::leanh::lean_dec_ref(v_a_905_);
    crate::leanh::lean_dec(v_a_904_);
    crate::leanh::lean_dec_ref(v_a_903_);
    crate::leanh::lean_dec(v_a_902_);
    crate::leanh::lean_dec_ref(v_a_901_);
    return v_res_908_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0(
    mut v_00_u03b1_909_: *mut crate::leanh::LeanObject,
    mut v_msg_910_: *mut crate::leanh::LeanObject,
    mut v___y_911_: *mut crate::leanh::LeanObject,
    mut v___y_912_: *mut crate::leanh::LeanObject,
    mut v___y_913_: *mut crate::leanh::LeanObject,
    mut v___y_914_: *mut crate::leanh::LeanObject,
    mut v___y_915_: *mut crate::leanh::LeanObject,
    mut v___y_916_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_918_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0___redArg(
            v_msg_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_,
        );
    return v___x_918_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0___boxed(
    mut v_00_u03b1_919_: *mut crate::leanh::LeanObject,
    mut v_msg_920_: *mut crate::leanh::LeanObject,
    mut v___y_921_: *mut crate::leanh::LeanObject,
    mut v___y_922_: *mut crate::leanh::LeanObject,
    mut v___y_923_: *mut crate::leanh::LeanObject,
    mut v___y_924_: *mut crate::leanh::LeanObject,
    mut v___y_925_: *mut crate::leanh::LeanObject,
    mut v___y_926_: *mut crate::leanh::LeanObject,
    mut v___y_927_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_928_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0(
        v_00_u03b1_919_,
        v_msg_920_,
        v___y_921_,
        v___y_922_,
        v___y_923_,
        v___y_924_,
        v___y_925_,
        v___y_926_,
    );
    crate::leanh::lean_dec(v___y_926_);
    crate::leanh::lean_dec_ref(v___y_925_);
    crate::leanh::lean_dec(v___y_924_);
    crate::leanh::lean_dec_ref(v___y_923_);
    crate::leanh::lean_dec(v___y_922_);
    crate::leanh::lean_dec_ref(v___y_921_);
    return v_res_928_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1(
    mut v_msgData_929_: *mut crate::leanh::LeanObject,
    mut v_macroStack_930_: *mut crate::leanh::LeanObject,
    mut v___y_931_: *mut crate::leanh::LeanObject,
    mut v___y_932_: *mut crate::leanh::LeanObject,
    mut v___y_933_: *mut crate::leanh::LeanObject,
    mut v___y_934_: *mut crate::leanh::LeanObject,
    mut v___y_935_: *mut crate::leanh::LeanObject,
    mut v___y_936_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_938_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___redArg(v_msgData_929_, v_macroStack_930_, v___y_935_);
    return v___x_938_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1___boxed(
    mut v_msgData_939_: *mut crate::leanh::LeanObject,
    mut v_macroStack_940_: *mut crate::leanh::LeanObject,
    mut v___y_941_: *mut crate::leanh::LeanObject,
    mut v___y_942_: *mut crate::leanh::LeanObject,
    mut v___y_943_: *mut crate::leanh::LeanObject,
    mut v___y_944_: *mut crate::leanh::LeanObject,
    mut v___y_945_: *mut crate::leanh::LeanObject,
    mut v___y_946_: *mut crate::leanh::LeanObject,
    mut v___y_947_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_948_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1(v_msgData_939_, v_macroStack_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_);
    crate::leanh::lean_dec(v___y_946_);
    crate::leanh::lean_dec_ref(v___y_945_);
    crate::leanh::lean_dec(v___y_944_);
    crate::leanh::lean_dec_ref(v___y_943_);
    crate::leanh::lean_dec(v___y_942_);
    crate::leanh::lean_dec_ref(v___y_941_);
    return v_res_948_;
}
pub unsafe fn l_Lean_Elab_Tactic_BVDecide_BVCheck_mkContext(
    mut v_lratPath_949_: *mut crate::leanh::LeanObject,
    mut v_cfg_950_: *mut crate::leanh::LeanObject,
    mut v_a_951_: *mut crate::leanh::LeanObject,
    mut v_a_952_: *mut crate::leanh::LeanObject,
    mut v_a_953_: *mut crate::leanh::LeanObject,
    mut v_a_954_: *mut crate::leanh::LeanObject,
    mut v_a_955_: *mut crate::leanh::LeanObject,
    mut v_a_956_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_965_: u8 = 0;
    let mut v___x_967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_969_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_958_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir(
                    v_a_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_,
                );
                if crate::leanh::lean_obj_tag(v___x_958_) == 0 {
                    v_a_959_ = crate::leanh::lean_ctor_get(v___x_958_, 0);
                    crate::leanh::lean_inc(v_a_959_);
                    crate::leanh::lean_dec_ref_known(v___x_958_, 1);
                    v___x_960_ = l_System_FilePath_join(v_a_959_, v_lratPath_949_);
                    v___x_961_ = l_Lean_Meta_Tactic_BVDecide_TacticContext_new(
                        v___x_960_, v_cfg_950_, v_a_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_,
                        v_a_956_,
                    );
                    return v___x_961_;
                } else {
                    crate::leanh::lean_dec_ref(v_cfg_950_);
                    crate::leanh::lean_dec_ref(v_lratPath_949_);
                    v_a_962_ = crate::leanh::lean_ctor_get(v___x_958_, 0);
                    v_isSharedCheck_969_ = (!crate::leanh::lean_is_exclusive(v___x_958_)) as u8;
                    if v_isSharedCheck_969_ == 0 {
                        v___x_964_ = v___x_958_;
                        v_isShared_965_ = v_isSharedCheck_969_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_962_);
                        crate::leanh::lean_dec(v___x_958_);
                        v___x_964_ = crate::leanh::lean_box(0);
                        v_isShared_965_ = v_isSharedCheck_969_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_965_ == 0 {
                    v___x_967_ = v___x_964_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_968_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_968_, 0, v_a_962_);
                    v___x_967_ = v_reuseFailAlloc_968_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_967_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_BVDecide_BVCheck_mkContext___boxed(
    mut v_lratPath_970_: *mut crate::leanh::LeanObject,
    mut v_cfg_971_: *mut crate::leanh::LeanObject,
    mut v_a_972_: *mut crate::leanh::LeanObject,
    mut v_a_973_: *mut crate::leanh::LeanObject,
    mut v_a_974_: *mut crate::leanh::LeanObject,
    mut v_a_975_: *mut crate::leanh::LeanObject,
    mut v_a_976_: *mut crate::leanh::LeanObject,
    mut v_a_977_: *mut crate::leanh::LeanObject,
    mut v_a_978_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_979_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_mkContext(
        v_lratPath_970_,
        v_cfg_971_,
        v_a_972_,
        v_a_973_,
        v_a_974_,
        v_a_975_,
        v_a_976_,
        v_a_977_,
    );
    crate::leanh::lean_dec(v_a_977_);
    crate::leanh::lean_dec_ref(v_a_976_);
    crate::leanh::lean_dec(v_a_975_);
    crate::leanh::lean_dec_ref(v_a_974_);
    crate::leanh::lean_dec(v_a_973_);
    crate::leanh::lean_dec_ref(v_a_972_);
    return v_res_979_;
}
pub unsafe fn l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck(
    mut v_g_980_: *mut crate::leanh::LeanObject,
    mut v_ctx_981_: *mut crate::leanh::LeanObject,
    mut v_a_982_: *mut crate::leanh::LeanObject,
    mut v_a_983_: *mut crate::leanh::LeanObject,
    mut v_a_984_: *mut crate::leanh::LeanObject,
    mut v_a_985_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_991_: u8 = 0;
    let mut v___x_992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_996_: u8 = 0;
    let mut v_unused_997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1001_: u8 = 0;
    let mut v___x_1003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1005_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_987_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Meta_Tactic_BVDecide_lratChecker___boxed as *mut core::ffi::c_void,
                    9,
                    1,
                );
                crate::leanh::lean_closure_set(v___x_987_, 0, v_ctx_981_);
                v___x_988_ = l_Lean_Meta_Tactic_BVDecide_closeWithBVReflection___redArg(
                    v_g_980_, v___x_987_, v_a_982_, v_a_983_, v_a_984_, v_a_985_,
                );
                if crate::leanh::lean_obj_tag(v___x_988_) == 0 {
                    v_isSharedCheck_996_ = (!crate::leanh::lean_is_exclusive(v___x_988_)) as u8;
                    if v_isSharedCheck_996_ == 0 {
                        v_unused_997_ = crate::leanh::lean_ctor_get(v___x_988_, 0);
                        crate::leanh::lean_dec(v_unused_997_);
                        v___x_990_ = v___x_988_;
                        v_isShared_991_ = v_isSharedCheck_996_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_988_);
                        v___x_990_ = crate::leanh::lean_box(0);
                        v_isShared_991_ = v_isSharedCheck_996_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_998_ = crate::leanh::lean_ctor_get(v___x_988_, 0);
                    v_isSharedCheck_1005_ = (!crate::leanh::lean_is_exclusive(v___x_988_)) as u8;
                    if v_isSharedCheck_1005_ == 0 {
                        v___x_1000_ = v___x_988_;
                        v_isShared_1001_ = v_isSharedCheck_1005_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_998_);
                        crate::leanh::lean_dec(v___x_988_);
                        v___x_1000_ = crate::leanh::lean_box(0);
                        v_isShared_1001_ = v_isSharedCheck_1005_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_992_ = crate::leanh::lean_box(0);
                if v_isShared_991_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_990_, 0, v___x_992_);
                    v___x_994_ = v___x_990_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_995_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_995_, 0, v___x_992_);
                    v___x_994_ = v_reuseFailAlloc_995_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_994_;
            }
            3 => {
                if v_isShared_1001_ == 0 {
                    v___x_1003_ = v___x_1000_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1004_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1004_, 0, v_a_998_);
                    v___x_1003_ = v_reuseFailAlloc_1004_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1003_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck___boxed(
    mut v_g_1006_: *mut crate::leanh::LeanObject,
    mut v_ctx_1007_: *mut crate::leanh::LeanObject,
    mut v_a_1008_: *mut crate::leanh::LeanObject,
    mut v_a_1009_: *mut crate::leanh::LeanObject,
    mut v_a_1010_: *mut crate::leanh::LeanObject,
    mut v_a_1011_: *mut crate::leanh::LeanObject,
    mut v_a_1012_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1013_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck(
        v_g_1006_,
        v_ctx_1007_,
        v_a_1008_,
        v_a_1009_,
        v_a_1010_,
        v_a_1011_,
    );
    crate::leanh::lean_dec(v_a_1011_);
    crate::leanh::lean_dec_ref(v_a_1010_);
    crate::leanh::lean_dec(v_a_1009_);
    crate::leanh::lean_dec_ref(v_a_1008_);
    return v_res_1013_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1014_ = crate::leanh::lean_box(0);
    v___x_1015_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_1016_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1016_, 0, v___x_1015_);
    crate::leanh::lean_ctor_set(v___x_1016_, 1, v___x_1014_);
    return v___x_1016_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__0___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1018_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__0___redArg___closed__0);
    v___x_1019_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1019_, 0, v___x_1018_);
    return v___x_1019_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__0___redArg___boxed(
    mut v___y_1020_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1021_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__0___redArg();
    return v_res_1021_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__0(
    mut v_00_u03b1_1022_: *mut crate::leanh::LeanObject,
    mut v___y_1023_: *mut crate::leanh::LeanObject,
    mut v___y_1024_: *mut crate::leanh::LeanObject,
    mut v___y_1025_: *mut crate::leanh::LeanObject,
    mut v___y_1026_: *mut crate::leanh::LeanObject,
    mut v___y_1027_: *mut crate::leanh::LeanObject,
    mut v___y_1028_: *mut crate::leanh::LeanObject,
    mut v___y_1029_: *mut crate::leanh::LeanObject,
    mut v___y_1030_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1032_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__0___redArg();
    return v___x_1032_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__0___boxed(
    mut v_00_u03b1_1033_: *mut crate::leanh::LeanObject,
    mut v___y_1034_: *mut crate::leanh::LeanObject,
    mut v___y_1035_: *mut crate::leanh::LeanObject,
    mut v___y_1036_: *mut crate::leanh::LeanObject,
    mut v___y_1037_: *mut crate::leanh::LeanObject,
    mut v___y_1038_: *mut crate::leanh::LeanObject,
    mut v___y_1039_: *mut crate::leanh::LeanObject,
    mut v___y_1040_: *mut crate::leanh::LeanObject,
    mut v___y_1041_: *mut crate::leanh::LeanObject,
    mut v___y_1042_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1043_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__0(v_00_u03b1_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_);
    crate::leanh::lean_dec(v___y_1041_);
    crate::leanh::lean_dec_ref(v___y_1040_);
    crate::leanh::lean_dec(v___y_1039_);
    crate::leanh::lean_dec_ref(v___y_1038_);
    crate::leanh::lean_dec(v___y_1037_);
    crate::leanh::lean_dec_ref(v___y_1036_);
    crate::leanh::lean_dec(v___y_1035_);
    crate::leanh::lean_dec_ref(v___y_1034_);
    return v_res_1043_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0(
    mut v___y_1052_: u8,
    mut v_suppressElabErrors_1053_: u8,
    mut v_x_1054_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_1054_) == 1 {
        let mut v_pre_1055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_pre_1055_ = crate::leanh::lean_ctor_get(v_x_1054_, 0);
        match crate::leanh::lean_obj_tag(v_pre_1055_) {
            1 => {
                let mut v_pre_1056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_pre_1056_ = crate::leanh::lean_ctor_get(v_pre_1055_, 0);
                match crate::leanh::lean_obj_tag(v_pre_1056_) {
                    0 => {
                        let mut v_str_1057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v_str_1058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1060_: u8 = 0;
                        v_str_1057_ = crate::leanh::lean_ctor_get(v_x_1054_, 1);
                        v_str_1058_ = crate::leanh::lean_ctor_get(v_pre_1055_, 1);
                        v___x_1059_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__0;
                        v___x_1060_ = lean_string_dec_eq(v_str_1058_, v___x_1059_);
                        if v___x_1060_ == 0 {
                            let mut v___x_1061_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1062_: u8 = 0;
                            v___x_1061_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__1;
                            v___x_1062_ = lean_string_dec_eq(v_str_1058_, v___x_1061_);
                            if v___x_1062_ == 0 {
                                return v___y_1052_;
                            } else {
                                let mut v___x_1063_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_1064_: u8 = 0;
                                v___x_1063_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__2;
                                v___x_1064_ = lean_string_dec_eq(v_str_1057_, v___x_1063_);
                                if v___x_1064_ == 0 {
                                    return v___y_1052_;
                                } else {
                                    return v_suppressElabErrors_1053_;
                                }
                            }
                        } else {
                            let mut v___x_1065_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1066_: u8 = 0;
                            v___x_1065_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__3;
                            v___x_1066_ = lean_string_dec_eq(v_str_1057_, v___x_1065_);
                            if v___x_1066_ == 0 {
                                return v___y_1052_;
                            } else {
                                return v_suppressElabErrors_1053_;
                            }
                        }
                    }
                    1 => {
                        let mut v_pre_1067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v_pre_1067_ = crate::leanh::lean_ctor_get(v_pre_1056_, 0);
                        if crate::leanh::lean_obj_tag(v_pre_1067_) == 0 {
                            let mut v_str_1068_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_1069_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_1070_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1071_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1072_: u8 = 0;
                            v_str_1068_ = crate::leanh::lean_ctor_get(v_x_1054_, 1);
                            v_str_1069_ = crate::leanh::lean_ctor_get(v_pre_1055_, 1);
                            v_str_1070_ = crate::leanh::lean_ctor_get(v_pre_1056_, 1);
                            v___x_1071_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__4;
                            v___x_1072_ = lean_string_dec_eq(v_str_1070_, v___x_1071_);
                            if v___x_1072_ == 0 {
                                return v___y_1052_;
                            } else {
                                let mut v___x_1073_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_1074_: u8 = 0;
                                v___x_1073_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__5;
                                v___x_1074_ = lean_string_dec_eq(v_str_1069_, v___x_1073_);
                                if v___x_1074_ == 0 {
                                    return v___y_1052_;
                                } else {
                                    let mut v___x_1075_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_1076_: u8 = 0;
                                    v___x_1075_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__6;
                                    v___x_1076_ = lean_string_dec_eq(v_str_1068_, v___x_1075_);
                                    if v___x_1076_ == 0 {
                                        return v___y_1052_;
                                    } else {
                                        return v_suppressElabErrors_1053_;
                                    }
                                }
                            }
                        } else {
                            return v___y_1052_;
                        }
                    }
                    _ => {
                        return v___y_1052_;
                    }
                }
            }
            0 => {
                let mut v_str_1077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1079_: u8 = 0;
                v_str_1077_ = crate::leanh::lean_ctor_get(v_x_1054_, 1);
                v___x_1078_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__7;
                v___x_1079_ = lean_string_dec_eq(v_str_1077_, v___x_1078_);
                if v___x_1079_ == 0 {
                    return v___y_1052_;
                } else {
                    return v_suppressElabErrors_1053_;
                }
            }
            _ => {
                return v___y_1052_;
            }
        }
    } else {
        return v___y_1052_;
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___boxed(
    mut v___y_1080_: *mut crate::leanh::LeanObject,
    mut v_suppressElabErrors_1081_: *mut crate::leanh::LeanObject,
    mut v_x_1082_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_6540__boxed_1083_: u8 = 0;
    let mut v_suppressElabErrors_boxed_1084_: u8 = 0;
    let mut v_res_1085_: u8 = 0;
    let mut v_r_1086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_6540__boxed_1083_ = (crate::leanh::lean_unbox(v___y_1080_) as u8);
    v_suppressElabErrors_boxed_1084_ = (crate::leanh::lean_unbox(v_suppressElabErrors_1081_) as u8);
    v_res_1085_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0(v___y_6540__boxed_1083_, v_suppressElabErrors_boxed_1084_, v_x_1082_);
    crate::leanh::lean_dec(v_x_1082_);
    v_r_1086_ = crate::leanh::lean_box((v_res_1085_) as usize);
    return v_r_1086_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2(
    mut v_ref_1088_: *mut crate::leanh::LeanObject,
    mut v_msgData_1089_: *mut crate::leanh::LeanObject,
    mut v_severity_1090_: u8,
    mut v_isSilent_1091_: u8,
    mut v___y_1092_: *mut crate::leanh::LeanObject,
    mut v___y_1093_: *mut crate::leanh::LeanObject,
    mut v___y_1094_: *mut crate::leanh::LeanObject,
    mut v___y_1095_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1101_: u8 = 0;
    let mut v___y_1102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1103_: u8 = 0;
    let mut v___y_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1121_: u8 = 0;
    let mut v___x_1122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1132_: u8 = 0;
    let mut v___y_1134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1136_: u8 = 0;
    let mut v___y_1137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1139_: u8 = 0;
    let mut v___y_1140_: u8 = 0;
    let mut v___y_1141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1147_: u8 = 0;
    let mut v___x_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: u8 = 0;
    let mut v___x_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1157_: u8 = 0;
    let mut v___y_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1161_: u8 = 0;
    let mut v___y_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1164_: u8 = 0;
    let mut v___y_1165_: u8 = 0;
    let mut v___y_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1174_: u8 = 0;
    let mut v___y_1175_: u8 = 0;
    let mut v___y_1176_: u8 = 0;
    let mut v_ref_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1181_: u8 = 0;
    let mut v___y_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1187_: u8 = 0;
    let mut v___y_1188_: u8 = 0;
    let mut v___y_1189_: u8 = 0;
    let mut v___y_1191_: u8 = 0;
    let mut v_fileName_1192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1196_: u8 = 0;
    let mut v___x_1197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: u8 = 0;
    let mut v___x_1201_: u8 = 0;
    let mut v___x_1202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: u8 = 0;
    let mut v___x_1204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: u8 = 0;
    let mut v___x_1207_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1181_ = 2;
                v___x_1206_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1090_, v___x_1181_);
                if v___x_1206_ == 0 {
                    v___y_1191_ = v___x_1206_;
                    state = 10;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_msgData_1089_);
                    v___x_1207_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1089_);
                    v___y_1191_ = v___x_1207_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_1107_ = lean_st_ref_take(v___y_1106_);
                v_currNamespace_1108_ = crate::leanh::lean_ctor_get(v___y_1105_, 6);
                v_openDecls_1109_ = crate::leanh::lean_ctor_get(v___y_1105_, 7);
                v_env_1110_ = crate::leanh::lean_ctor_get(v___x_1107_, 0);
                v_nextMacroScope_1111_ = crate::leanh::lean_ctor_get(v___x_1107_, 1);
                v_ngen_1112_ = crate::leanh::lean_ctor_get(v___x_1107_, 2);
                v_auxDeclNGen_1113_ = crate::leanh::lean_ctor_get(v___x_1107_, 3);
                v_traceState_1114_ = crate::leanh::lean_ctor_get(v___x_1107_, 4);
                v_cache_1115_ = crate::leanh::lean_ctor_get(v___x_1107_, 5);
                v_messages_1116_ = crate::leanh::lean_ctor_get(v___x_1107_, 6);
                v_infoState_1117_ = crate::leanh::lean_ctor_get(v___x_1107_, 7);
                v_snapshotTasks_1118_ = crate::leanh::lean_ctor_get(v___x_1107_, 8);
                v_isSharedCheck_1132_ = (!crate::leanh::lean_is_exclusive(v___x_1107_)) as u8;
                if v_isSharedCheck_1132_ == 0 {
                    v___x_1120_ = v___x_1107_;
                    v_isShared_1121_ = v_isSharedCheck_1132_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_1118_);
                    crate::leanh::lean_inc(v_infoState_1117_);
                    crate::leanh::lean_inc(v_messages_1116_);
                    crate::leanh::lean_inc(v_cache_1115_);
                    crate::leanh::lean_inc(v_traceState_1114_);
                    crate::leanh::lean_inc(v_auxDeclNGen_1113_);
                    crate::leanh::lean_inc(v_ngen_1112_);
                    crate::leanh::lean_inc(v_nextMacroScope_1111_);
                    crate::leanh::lean_inc(v_env_1110_);
                    crate::leanh::lean_dec(v___x_1107_);
                    v___x_1120_ = crate::leanh::lean_box(0);
                    v_isShared_1121_ = v_isSharedCheck_1132_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v_openDecls_1109_);
                crate::leanh::lean_inc(v_currNamespace_1108_);
                v___x_1122_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1122_, 0, v_currNamespace_1108_);
                crate::leanh::lean_ctor_set(v___x_1122_, 1, v_openDecls_1109_);
                v___x_1123_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1123_, 0, v___x_1122_);
                crate::leanh::lean_ctor_set(v___x_1123_, 1, v___y_1102_);
                crate::leanh::lean_inc_ref(v___y_1100_);
                crate::leanh::lean_inc_ref(v___y_1098_);
                v___x_1124_ = crate::leanh::lean_alloc_ctor(0, 5, (3) as u32);
                crate::leanh::lean_ctor_set(v___x_1124_, 0, v___y_1098_);
                crate::leanh::lean_ctor_set(v___x_1124_, 1, v___y_1099_);
                crate::leanh::lean_ctor_set(v___x_1124_, 2, v___y_1104_);
                crate::leanh::lean_ctor_set(v___x_1124_, 3, v___y_1100_);
                crate::leanh::lean_ctor_set(v___x_1124_, 4, v___x_1123_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1124_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    v___y_1103_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1124_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
                    v___y_1101_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1124_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 2) as u32,
                    v_isSilent_1091_,
                );
                v___x_1125_ = l_Lean_MessageLog_add(v___x_1124_, v_messages_1116_);
                if v_isShared_1121_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1120_, 6, v___x_1125_);
                    v___x_1127_ = v___x_1120_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1131_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1131_, 0, v_env_1110_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1131_, 1, v_nextMacroScope_1111_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1131_, 2, v_ngen_1112_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1131_, 3, v_auxDeclNGen_1113_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1131_, 4, v_traceState_1114_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1131_, 5, v_cache_1115_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1131_, 6, v___x_1125_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1131_, 7, v_infoState_1117_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1131_, 8, v_snapshotTasks_1118_);
                    v___x_1127_ = v_reuseFailAlloc_1131_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1128_ = lean_st_ref_set(v___y_1106_, v___x_1127_);
                v___x_1129_ = crate::leanh::lean_box(0);
                v___x_1130_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1130_, 0, v___x_1129_);
                return v___x_1130_;
            }
            4 => {
                v___x_1142_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_1089_,
                    );
                v___x_1143_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__0(v___x_1142_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_);
                v_a_1144_ = crate::leanh::lean_ctor_get(v___x_1143_, 0);
                v_isSharedCheck_1157_ = (!crate::leanh::lean_is_exclusive(v___x_1143_)) as u8;
                if v_isSharedCheck_1157_ == 0 {
                    v___x_1146_ = v___x_1143_;
                    v_isShared_1147_ = v_isSharedCheck_1157_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1144_);
                    crate::leanh::lean_dec(v___x_1143_);
                    v___x_1146_ = crate::leanh::lean_box(0);
                    v_isShared_1147_ = v_isSharedCheck_1157_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_inc_ref_n(v___y_1138_, 2);
                v___x_1148_ = l_Lean_FileMap_toPosition(v___y_1138_, v___y_1137_);
                crate::leanh::lean_dec(v___y_1137_);
                v___x_1149_ = l_Lean_FileMap_toPosition(v___y_1138_, v___y_1141_);
                crate::leanh::lean_dec(v___y_1141_);
                v___x_1150_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1150_, 0, v___x_1149_);
                v___x_1151_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___closed__0;
                if v___y_1140_ == 0 {
                    crate::leanh::lean_del_object(v___x_1146_);
                    crate::leanh::lean_dec_ref(v___y_1134_);
                    v___y_1098_ = v___y_1135_;
                    v___y_1099_ = v___x_1148_;
                    v___y_1100_ = v___x_1151_;
                    v___y_1101_ = v___y_1136_;
                    v___y_1102_ = v_a_1144_;
                    v___y_1103_ = v___y_1139_;
                    v___y_1104_ = v___x_1150_;
                    v___y_1105_ = v___y_1094_;
                    v___y_1106_ = v___y_1095_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1144_);
                    v___x_1152_ = l_Lean_MessageData_hasTag(v___y_1134_, v_a_1144_);
                    if v___x_1152_ == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_1150_, 1);
                        crate::leanh::lean_dec_ref(v___x_1148_);
                        crate::leanh::lean_dec(v_a_1144_);
                        v___x_1153_ = crate::leanh::lean_box(0);
                        if v_isShared_1147_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1146_, 0, v___x_1153_);
                            v___x_1155_ = v___x_1146_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_1156_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1156_, 0, v___x_1153_);
                            v___x_1155_ = v_reuseFailAlloc_1156_;
                            state = 6;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_1146_);
                        v___y_1098_ = v___y_1135_;
                        v___y_1099_ = v___x_1148_;
                        v___y_1100_ = v___x_1151_;
                        v___y_1101_ = v___y_1136_;
                        v___y_1102_ = v_a_1144_;
                        v___y_1103_ = v___y_1139_;
                        v___y_1104_ = v___x_1150_;
                        v___y_1105_ = v___y_1094_;
                        v___y_1106_ = v___y_1095_;
                        state = 1;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_1155_;
            }
            7 => {
                v___x_1167_ = l_Lean_Syntax_getTailPos_x3f(v___y_1163_, v___y_1164_);
                crate::leanh::lean_dec(v___y_1163_);
                if crate::leanh::lean_obj_tag(v___x_1167_) == 0 {
                    crate::leanh::lean_inc(v___y_1166_);
                    v___y_1134_ = v___y_1159_;
                    v___y_1135_ = v___y_1160_;
                    v___y_1136_ = v___y_1161_;
                    v___y_1137_ = v___y_1166_;
                    v___y_1138_ = v___y_1162_;
                    v___y_1139_ = v___y_1164_;
                    v___y_1140_ = v___y_1165_;
                    v___y_1141_ = v___y_1166_;
                    state = 4;
                    continue;
                } else {
                    v_val_1168_ = crate::leanh::lean_ctor_get(v___x_1167_, 0);
                    crate::leanh::lean_inc(v_val_1168_);
                    crate::leanh::lean_dec_ref_known(v___x_1167_, 1);
                    v___y_1134_ = v___y_1159_;
                    v___y_1135_ = v___y_1160_;
                    v___y_1136_ = v___y_1161_;
                    v___y_1137_ = v___y_1166_;
                    v___y_1138_ = v___y_1162_;
                    v___y_1139_ = v___y_1164_;
                    v___y_1140_ = v___y_1165_;
                    v___y_1141_ = v_val_1168_;
                    state = 4;
                    continue;
                }
            }
            8 => {
                v_ref_1177_ = l_Lean_replaceRef(v_ref_1088_, v___y_1173_);
                v___x_1178_ = l_Lean_Syntax_getPos_x3f(v_ref_1177_, v___y_1174_);
                if crate::leanh::lean_obj_tag(v___x_1178_) == 0 {
                    v___x_1179_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_1159_ = v___y_1170_;
                    v___y_1160_ = v___y_1171_;
                    v___y_1161_ = v___y_1176_;
                    v___y_1162_ = v___y_1172_;
                    v___y_1163_ = v_ref_1177_;
                    v___y_1164_ = v___y_1174_;
                    v___y_1165_ = v___y_1175_;
                    v___y_1166_ = v___x_1179_;
                    state = 7;
                    continue;
                } else {
                    v_val_1180_ = crate::leanh::lean_ctor_get(v___x_1178_, 0);
                    crate::leanh::lean_inc(v_val_1180_);
                    crate::leanh::lean_dec_ref_known(v___x_1178_, 1);
                    v___y_1159_ = v___y_1170_;
                    v___y_1160_ = v___y_1171_;
                    v___y_1161_ = v___y_1176_;
                    v___y_1162_ = v___y_1172_;
                    v___y_1163_ = v_ref_1177_;
                    v___y_1164_ = v___y_1174_;
                    v___y_1165_ = v___y_1175_;
                    v___y_1166_ = v_val_1180_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                if v___y_1189_ == 0 {
                    v___y_1170_ = v___y_1184_;
                    v___y_1171_ = v___y_1183_;
                    v___y_1172_ = v___y_1186_;
                    v___y_1173_ = v___y_1185_;
                    v___y_1174_ = v___y_1188_;
                    v___y_1175_ = v___y_1187_;
                    v___y_1176_ = v_severity_1090_;
                    state = 8;
                    continue;
                } else {
                    v___y_1170_ = v___y_1184_;
                    v___y_1171_ = v___y_1183_;
                    v___y_1172_ = v___y_1186_;
                    v___y_1173_ = v___y_1185_;
                    v___y_1174_ = v___y_1188_;
                    v___y_1175_ = v___y_1187_;
                    v___y_1176_ = v___x_1181_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                if v___y_1191_ == 0 {
                    v_fileName_1192_ = crate::leanh::lean_ctor_get(v___y_1094_, 0);
                    v_fileMap_1193_ = crate::leanh::lean_ctor_get(v___y_1094_, 1);
                    v_options_1194_ = crate::leanh::lean_ctor_get(v___y_1094_, 2);
                    v_ref_1195_ = crate::leanh::lean_ctor_get(v___y_1094_, 5);
                    v_suppressElabErrors_1196_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_1094_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    );
                    v___x_1197_ = crate::leanh::lean_box((v___y_1191_) as usize);
                    v___x_1198_ = crate::leanh::lean_box((v_suppressElabErrors_1196_) as usize);
                    v___f_1199_ = crate::leanh::lean_alloc_closure(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    crate::leanh::lean_closure_set(v___f_1199_, 0, v___x_1197_);
                    crate::leanh::lean_closure_set(v___f_1199_, 1, v___x_1198_);
                    v___x_1200_ = 1;
                    v___x_1201_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1090_, v___x_1200_);
                    if v___x_1201_ == 0 {
                        v___y_1183_ = v_fileName_1192_;
                        v___y_1184_ = v___f_1199_;
                        v___y_1185_ = v_ref_1195_;
                        v___y_1186_ = v_fileMap_1193_;
                        v___y_1187_ = v_suppressElabErrors_1196_;
                        v___y_1188_ = v___y_1191_;
                        v___y_1189_ = v___x_1201_;
                        state = 9;
                        continue;
                    } else {
                        v___x_1202_ = l_Lean_warningAsError;
                        v___x_1203_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir_spec__0_spec__1_spec__2(v_options_1194_, v___x_1202_);
                        v___y_1183_ = v_fileName_1192_;
                        v___y_1184_ = v___f_1199_;
                        v___y_1185_ = v_ref_1195_;
                        v___y_1186_ = v_fileMap_1193_;
                        v___y_1187_ = v_suppressElabErrors_1196_;
                        v___y_1188_ = v___y_1191_;
                        v___y_1189_ = v___x_1203_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_msgData_1089_);
                    v___x_1204_ = crate::leanh::lean_box(0);
                    v___x_1205_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1205_, 0, v___x_1204_);
                    return v___x_1205_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___boxed(
    mut v_ref_1208_: *mut crate::leanh::LeanObject,
    mut v_msgData_1209_: *mut crate::leanh::LeanObject,
    mut v_severity_1210_: *mut crate::leanh::LeanObject,
    mut v_isSilent_1211_: *mut crate::leanh::LeanObject,
    mut v___y_1212_: *mut crate::leanh::LeanObject,
    mut v___y_1213_: *mut crate::leanh::LeanObject,
    mut v___y_1214_: *mut crate::leanh::LeanObject,
    mut v___y_1215_: *mut crate::leanh::LeanObject,
    mut v___y_1216_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_1217_: u8 = 0;
    let mut v_isSilent_boxed_1218_: u8 = 0;
    let mut v_res_1219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_1217_ = (crate::leanh::lean_unbox(v_severity_1210_) as u8);
    v_isSilent_boxed_1218_ = (crate::leanh::lean_unbox(v_isSilent_1211_) as u8);
    v_res_1219_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2(v_ref_1208_, v_msgData_1209_, v_severity_boxed_1217_, v_isSilent_boxed_1218_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_);
    crate::leanh::lean_dec(v___y_1215_);
    crate::leanh::lean_dec_ref(v___y_1214_);
    crate::leanh::lean_dec(v___y_1213_);
    crate::leanh::lean_dec_ref(v___y_1212_);
    crate::leanh::lean_dec(v_ref_1208_);
    return v_res_1219_;
}
pub unsafe fn l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1(
    mut v_msgData_1220_: *mut crate::leanh::LeanObject,
    mut v_severity_1221_: u8,
    mut v_isSilent_1222_: u8,
    mut v___y_1223_: *mut crate::leanh::LeanObject,
    mut v___y_1224_: *mut crate::leanh::LeanObject,
    mut v___y_1225_: *mut crate::leanh::LeanObject,
    mut v___y_1226_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_1228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_1228_ = crate::leanh::lean_ctor_get(v___y_1225_, 5);
    v___x_1229_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2(v_ref_1228_, v_msgData_1220_, v_severity_1221_, v_isSilent_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_);
    return v___x_1229_;
}
pub unsafe fn l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1___boxed(
    mut v_msgData_1230_: *mut crate::leanh::LeanObject,
    mut v_severity_1231_: *mut crate::leanh::LeanObject,
    mut v_isSilent_1232_: *mut crate::leanh::LeanObject,
    mut v___y_1233_: *mut crate::leanh::LeanObject,
    mut v___y_1234_: *mut crate::leanh::LeanObject,
    mut v___y_1235_: *mut crate::leanh::LeanObject,
    mut v___y_1236_: *mut crate::leanh::LeanObject,
    mut v___y_1237_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_1238_: u8 = 0;
    let mut v_isSilent_boxed_1239_: u8 = 0;
    let mut v_res_1240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_1238_ = (crate::leanh::lean_unbox(v_severity_1231_) as u8);
    v_isSilent_boxed_1239_ = (crate::leanh::lean_unbox(v_isSilent_1232_) as u8);
    v_res_1240_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1(v_msgData_1230_, v_severity_boxed_1238_, v_isSilent_boxed_1239_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_);
    crate::leanh::lean_dec(v___y_1236_);
    crate::leanh::lean_dec_ref(v___y_1235_);
    crate::leanh::lean_dec(v___y_1234_);
    crate::leanh::lean_dec_ref(v___y_1233_);
    return v_res_1240_;
}
pub unsafe fn l_Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1(
    mut v_msgData_1241_: *mut crate::leanh::LeanObject,
    mut v___y_1242_: *mut crate::leanh::LeanObject,
    mut v___y_1243_: *mut crate::leanh::LeanObject,
    mut v___y_1244_: *mut crate::leanh::LeanObject,
    mut v___y_1245_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1247_: u8 = 0;
    let mut v___x_1248_: u8 = 0;
    let mut v___x_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1247_ = 1;
    v___x_1248_ = 0;
    v___x_1249_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1(v_msgData_1241_, v___x_1247_, v___x_1248_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_);
    return v___x_1249_;
}
pub unsafe fn l_Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1___boxed(
    mut v_msgData_1250_: *mut crate::leanh::LeanObject,
    mut v___y_1251_: *mut crate::leanh::LeanObject,
    mut v___y_1252_: *mut crate::leanh::LeanObject,
    mut v___y_1253_: *mut crate::leanh::LeanObject,
    mut v___y_1254_: *mut crate::leanh::LeanObject,
    mut v___y_1255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1256_ = l_Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1(
        v_msgData_1250_,
        v___y_1251_,
        v___y_1252_,
        v___y_1253_,
        v___y_1254_,
    );
    crate::leanh::lean_dec(v___y_1254_);
    crate::leanh::lean_dec_ref(v___y_1253_);
    crate::leanh::lean_dec(v___y_1252_);
    crate::leanh::lean_dec_ref(v___y_1251_);
    return v_res_1256_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1258_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__0;
    v___x_1259_ = l_Lean_stringToMessageData(v___x_1258_);
    return v___x_1259_;
}
pub unsafe fn l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0(
    mut v_a_1266_: *mut crate::leanh::LeanObject,
    mut v___x_1267_: u8,
    mut v___x_1268_: *mut crate::leanh::LeanObject,
    mut v___x_1269_: *mut crate::leanh::LeanObject,
    mut v___x_1270_: *mut crate::leanh::LeanObject,
    mut v___x_1271_: *mut crate::leanh::LeanObject,
    mut v_tk_1272_: *mut crate::leanh::LeanObject,
    mut v_a_1273_: *mut crate::leanh::LeanObject,
    mut v___y_1274_: *mut crate::leanh::LeanObject,
    mut v___y_1275_: *mut crate::leanh::LeanObject,
    mut v___y_1276_: *mut crate::leanh::LeanObject,
    mut v___y_1277_: *mut crate::leanh::LeanObject,
    mut v___y_1278_: *mut crate::leanh::LeanObject,
    mut v___y_1279_: *mut crate::leanh::LeanObject,
    mut v___y_1280_: *mut crate::leanh::LeanObject,
    mut v___y_1281_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1289_: u8 = 0;
    let mut v___x_1290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1294_: u8 = 0;
    let mut v_unused_1295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1305_: u8 = 0;
    let mut v___x_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: u8 = 0;
    let mut v___x_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1323_: u8 = 0;
    let mut v_unused_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1330_: u8 = 0;
    let mut v___x_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1334_: u8 = 0;
    let mut v_a_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1338_: u8 = 0;
    let mut v___x_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1342_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1296_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v___y_1275_,
                    v___y_1278_,
                    v___y_1279_,
                    v___y_1280_,
                    v___y_1281_,
                );
                if crate::leanh::lean_obj_tag(v___x_1296_) == 0 {
                    v_a_1297_ = crate::leanh::lean_ctor_get(v___x_1296_, 0);
                    crate::leanh::lean_inc(v_a_1297_);
                    crate::leanh::lean_dec_ref_known(v___x_1296_, 1);
                    v___x_1298_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(
                        v_a_1297_,
                        v_a_1266_,
                        v___y_1278_,
                        v___y_1279_,
                        v___y_1280_,
                        v___y_1281_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1298_) == 0 {
                        v_a_1299_ = crate::leanh::lean_ctor_get(v___x_1298_, 0);
                        crate::leanh::lean_inc(v_a_1299_);
                        crate::leanh::lean_dec_ref_known(v___x_1298_, 1);
                        if crate::leanh::lean_obj_tag(v_a_1299_) == 0 {
                            crate::leanh::lean_dec_ref(v_a_1273_);
                            v_ref_1300_ = crate::leanh::lean_ctor_get(v___y_1280_, 5);
                            v___x_1301_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__1_once), _init_l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__1);
                            v___x_1302_ = l_Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1(v___x_1301_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_);
                            if crate::leanh::lean_obj_tag(v___x_1302_) == 0 {
                                v_isSharedCheck_1323_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1302_)) as u8;
                                if v_isSharedCheck_1323_ == 0 {
                                    v_unused_1324_ = crate::leanh::lean_ctor_get(v___x_1302_, 0);
                                    crate::leanh::lean_dec(v_unused_1324_);
                                    v___x_1304_ = v___x_1302_;
                                    v_isShared_1305_ = v_isSharedCheck_1323_;
                                    state = 4;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v___x_1302_);
                                    v___x_1304_ = crate::leanh::lean_box(0);
                                    v_isShared_1305_ = v_isSharedCheck_1323_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_tk_1272_);
                                crate::leanh::lean_dec(v___x_1271_);
                                crate::leanh::lean_dec_ref(v___x_1270_);
                                crate::leanh::lean_dec_ref(v___x_1269_);
                                crate::leanh::lean_dec_ref(v___x_1268_);
                                v___y_1284_ = v___x_1302_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_tk_1272_);
                            crate::leanh::lean_dec(v___x_1271_);
                            crate::leanh::lean_dec_ref(v___x_1270_);
                            crate::leanh::lean_dec_ref(v___x_1269_);
                            crate::leanh::lean_dec_ref(v___x_1268_);
                            v_val_1325_ = crate::leanh::lean_ctor_get(v_a_1299_, 0);
                            crate::leanh::lean_inc(v_val_1325_);
                            crate::leanh::lean_dec_ref_known(v_a_1299_, 1);
                            v___x_1326_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_bvCheck(
                                v_val_1325_,
                                v_a_1273_,
                                v___y_1278_,
                                v___y_1279_,
                                v___y_1280_,
                                v___y_1281_,
                            );
                            v___y_1284_ = v___x_1326_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_a_1273_);
                        crate::leanh::lean_dec(v_tk_1272_);
                        crate::leanh::lean_dec(v___x_1271_);
                        crate::leanh::lean_dec_ref(v___x_1270_);
                        crate::leanh::lean_dec_ref(v___x_1269_);
                        crate::leanh::lean_dec_ref(v___x_1268_);
                        v_a_1327_ = crate::leanh::lean_ctor_get(v___x_1298_, 0);
                        v_isSharedCheck_1334_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1298_)) as u8;
                        if v_isSharedCheck_1334_ == 0 {
                            v___x_1329_ = v___x_1298_;
                            v_isShared_1330_ = v_isSharedCheck_1334_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1327_);
                            crate::leanh::lean_dec(v___x_1298_);
                            v___x_1329_ = crate::leanh::lean_box(0);
                            v_isShared_1330_ = v_isSharedCheck_1334_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_a_1273_);
                    crate::leanh::lean_dec(v_tk_1272_);
                    crate::leanh::lean_dec(v___x_1271_);
                    crate::leanh::lean_dec_ref(v___x_1270_);
                    crate::leanh::lean_dec_ref(v___x_1269_);
                    crate::leanh::lean_dec_ref(v___x_1268_);
                    v_a_1335_ = crate::leanh::lean_ctor_get(v___x_1296_, 0);
                    v_isSharedCheck_1342_ = (!crate::leanh::lean_is_exclusive(v___x_1296_)) as u8;
                    if v_isSharedCheck_1342_ == 0 {
                        v___x_1337_ = v___x_1296_;
                        v_isShared_1338_ = v_isSharedCheck_1342_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1335_);
                        crate::leanh::lean_dec(v___x_1296_);
                        v___x_1337_ = crate::leanh::lean_box(0);
                        v_isShared_1338_ = v_isSharedCheck_1342_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v___y_1284_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___y_1284_, 1);
                    v___x_1285_ = crate::leanh::lean_box(0);
                    v___x_1286_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                        v___x_1285_,
                        v___y_1275_,
                        v___y_1278_,
                        v___y_1279_,
                        v___y_1280_,
                        v___y_1281_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1286_) == 0 {
                        v_isSharedCheck_1294_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1286_)) as u8;
                        if v_isSharedCheck_1294_ == 0 {
                            v_unused_1295_ = crate::leanh::lean_ctor_get(v___x_1286_, 0);
                            crate::leanh::lean_dec(v_unused_1295_);
                            v___x_1288_ = v___x_1286_;
                            v_isShared_1289_ = v_isSharedCheck_1294_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_1286_);
                            v___x_1288_ = crate::leanh::lean_box(0);
                            v_isShared_1289_ = v_isSharedCheck_1294_;
                            state = 2;
                            continue;
                        }
                    } else {
                        return v___x_1286_;
                    }
                } else {
                    return v___y_1284_;
                }
            }
            2 => {
                v___x_1290_ = crate::leanh::lean_box(0);
                if v_isShared_1289_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1288_, 0, v___x_1290_);
                    v___x_1292_ = v___x_1288_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1293_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1293_, 0, v___x_1290_);
                    v___x_1292_ = v_reuseFailAlloc_1293_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1292_;
            }
            4 => {
                v___x_1306_ = l_Lean_SourceInfo_fromRef(v_ref_1300_, v___x_1267_);
                v___x_1307_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__2;
                crate::leanh::lean_inc(v___x_1306_);
                v___x_1308_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1308_, 0, v___x_1306_);
                crate::leanh::lean_ctor_set(v___x_1308_, 1, v___x_1307_);
                v___x_1309_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__4;
                v___x_1310_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__5;
                v___x_1311_ =
                    l_Lean_Name_mkStr4(v___x_1268_, v___x_1269_, v___x_1270_, v___x_1310_);
                v___x_1312_ =
                    l_Lean_Syntax_node2(v___x_1306_, v___x_1311_, v___x_1308_, v___x_1271_);
                v___x_1313_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1313_, 0, v___x_1309_);
                crate::leanh::lean_ctor_set(v___x_1313_, 1, v___x_1312_);
                v___x_1314_ = crate::leanh::lean_box(0);
                v___x_1315_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1315_, 0, v___x_1313_);
                crate::leanh::lean_ctor_set(v___x_1315_, 1, v___x_1314_);
                crate::leanh::lean_ctor_set(v___x_1315_, 2, v___x_1314_);
                crate::leanh::lean_ctor_set(v___x_1315_, 3, v___x_1314_);
                crate::leanh::lean_ctor_set(v___x_1315_, 4, v___x_1314_);
                crate::leanh::lean_ctor_set(v___x_1315_, 5, v___x_1314_);
                crate::leanh::lean_inc(v_ref_1300_);
                if v_isShared_1305_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1304_, 1);
                    crate::leanh::lean_ctor_set(v___x_1304_, 0, v_ref_1300_);
                    v___x_1317_ = v___x_1304_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1322_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_ref_1300_);
                    v___x_1317_ = v_reuseFailAlloc_1322_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1318_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___closed__6;
                v___x_1319_ = 4;
                v___x_1320_ = l_Lean_MessageData_nil;
                v___x_1321_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(
                    v_tk_1272_,
                    v___x_1315_,
                    v___x_1317_,
                    v___x_1318_,
                    v___x_1314_,
                    v___x_1319_,
                    v___x_1320_,
                    v___y_1280_,
                    v___y_1281_,
                );
                v___y_1284_ = v___x_1321_;
                state = 1;
                continue;
            }
            6 => {
                if v_isShared_1330_ == 0 {
                    v___x_1332_ = v___x_1329_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1333_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1333_, 0, v_a_1327_);
                    v___x_1332_ = v_reuseFailAlloc_1333_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1332_;
            }
            8 => {
                if v_isShared_1338_ == 0 {
                    v___x_1340_ = v___x_1337_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1341_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1341_, 0, v_a_1335_);
                    v___x_1340_ = v_reuseFailAlloc_1341_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1340_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1343_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v___x_1344_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v___x_1345_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v___x_1346_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v___x_1347_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___x_1348_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_tk_1349_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_a_1350_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___y_1351_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_1352_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_1353_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_1354_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_1355_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_1356_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_1357_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_1358_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_1359_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___x_6876__boxed_1360_: u8 = 0;
    let mut v_res_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6876__boxed_1360_ = (crate::leanh::lean_unbox(v___x_1344_) as u8);
    v_res_1361_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0(
        v_a_1343_,
        v___x_6876__boxed_1360_,
        v___x_1345_,
        v___x_1346_,
        v___x_1347_,
        v___x_1348_,
        v_tk_1349_,
        v_a_1350_,
        v___y_1351_,
        v___y_1352_,
        v___y_1353_,
        v___y_1354_,
        v___y_1355_,
        v___y_1356_,
        v___y_1357_,
        v___y_1358_,
    );
    crate::leanh::lean_dec(v___y_1358_);
    crate::leanh::lean_dec_ref(v___y_1357_);
    crate::leanh::lean_dec(v___y_1356_);
    crate::leanh::lean_dec_ref(v___y_1355_);
    crate::leanh::lean_dec(v___y_1354_);
    crate::leanh::lean_dec_ref(v___y_1353_);
    crate::leanh::lean_dec(v___y_1352_);
    crate::leanh::lean_dec_ref(v___y_1351_);
    crate::leanh::lean_dec_ref(v_a_1343_);
    return v_res_1361_;
}
pub unsafe fn l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck(
    mut v_x_1379_: *mut crate::leanh::LeanObject,
    mut v_a_1380_: *mut crate::leanh::LeanObject,
    mut v_a_1381_: *mut crate::leanh::LeanObject,
    mut v_a_1382_: *mut crate::leanh::LeanObject,
    mut v_a_1383_: *mut crate::leanh::LeanObject,
    mut v_a_1384_: *mut crate::leanh::LeanObject,
    mut v_a_1385_: *mut crate::leanh::LeanObject,
    mut v_a_1386_: *mut crate::leanh::LeanObject,
    mut v_a_1387_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: u8 = 0;
    let mut v___x_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: u8 = 0;
    let mut v___x_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_path_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: u8 = 0;
    let mut v___x_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: u8 = 0;
    let mut v___x_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: u8 = 0;
    let mut v___x_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1423_: u8 = 0;
    let mut v___x_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1427_: u8 = 0;
    let mut v_a_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1431_: u8 = 0;
    let mut v___x_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1435_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1389_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__0;
                v___x_1390_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__1;
                v___x_1391_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__1_spec__1_spec__2___lam__0___closed__1;
                v___x_1392_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__3;
                crate::leanh::lean_inc(v_x_1379_);
                v___x_1393_ = l_Lean_Syntax_isOfKind(v_x_1379_, v___x_1392_);
                if v___x_1393_ == 0 {
                    crate::leanh::lean_dec(v_x_1379_);
                    v___x_1394_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__0___redArg();
                    return v___x_1394_;
                } else {
                    v___x_1395_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1396_ = l_Lean_Syntax_getArg(v_x_1379_, v___x_1395_);
                    v___x_1397_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__5;
                    crate::leanh::lean_inc(v___x_1396_);
                    v___x_1398_ = l_Lean_Syntax_isOfKind(v___x_1396_, v___x_1397_);
                    if v___x_1398_ == 0 {
                        crate::leanh::lean_dec(v___x_1396_);
                        crate::leanh::lean_dec(v_x_1379_);
                        v___x_1399_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__0___redArg();
                        return v___x_1399_;
                    } else {
                        v___x_1400_ = crate::leanh::lean_unsigned_to_nat(2);
                        v_path_1401_ = l_Lean_Syntax_getArg(v_x_1379_, v___x_1400_);
                        v___x_1402_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__7;
                        crate::leanh::lean_inc(v_path_1401_);
                        v___x_1403_ = l_Lean_Syntax_isOfKind(v_path_1401_, v___x_1402_);
                        if v___x_1403_ == 0 {
                            crate::leanh::lean_dec(v_path_1401_);
                            crate::leanh::lean_dec(v___x_1396_);
                            crate::leanh::lean_dec(v_x_1379_);
                            v___x_1404_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck_spec__0___redArg();
                            return v___x_1404_;
                        } else {
                            v___x_1405_ = crate::leanh::lean_unsigned_to_nat(10);
                            v___x_1406_ = 0;
                            v___x_1407_ = crate::leanh::lean_unsigned_to_nat(100000);
                            v___x_1408_ = 0;
                            v___x_1409_ = crate::leanh::lean_alloc_ctor(0, 2, (11) as u32);
                            crate::leanh::lean_ctor_set(v___x_1409_, 0, v___x_1405_);
                            crate::leanh::lean_ctor_set(v___x_1409_, 1, v___x_1407_);
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_1409_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                                v___x_1403_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_1409_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 1)
                                    as u32,
                                v___x_1403_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_1409_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 2)
                                    as u32,
                                v___x_1406_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_1409_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 3)
                                    as u32,
                                v___x_1403_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_1409_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 4)
                                    as u32,
                                v___x_1403_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_1409_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 5)
                                    as u32,
                                v___x_1403_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_1409_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 6)
                                    as u32,
                                v___x_1403_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_1409_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 7)
                                    as u32,
                                v___x_1403_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_1409_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 8)
                                    as u32,
                                v___x_1406_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_1409_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 9)
                                    as u32,
                                v___x_1406_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_1409_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 10)
                                    as u32,
                                v___x_1408_,
                            );
                            crate::leanh::lean_inc(v___x_1396_);
                            v___x_1410_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg(
                                v___x_1396_,
                                v___x_1409_,
                                v___x_1403_,
                                v_a_1380_,
                                v_a_1386_,
                                v_a_1387_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_1410_) == 0 {
                                v_a_1411_ = crate::leanh::lean_ctor_get(v___x_1410_, 0);
                                crate::leanh::lean_inc_n(v_a_1411_, 2);
                                crate::leanh::lean_dec_ref_known(v___x_1410_, 1);
                                v___x_1412_ = l_Lean_TSyntax_getString(v_path_1401_);
                                crate::leanh::lean_dec(v_path_1401_);
                                v___x_1413_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_mkContext(
                                    v___x_1412_,
                                    v_a_1411_,
                                    v_a_1382_,
                                    v_a_1383_,
                                    v_a_1384_,
                                    v_a_1385_,
                                    v_a_1386_,
                                    v_a_1387_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_1413_) == 0 {
                                    v_a_1414_ = crate::leanh::lean_ctor_get(v___x_1413_, 0);
                                    crate::leanh::lean_inc(v_a_1414_);
                                    crate::leanh::lean_dec_ref_known(v___x_1413_, 1);
                                    v___x_1415_ = crate::leanh::lean_unsigned_to_nat(0);
                                    v_tk_1416_ = l_Lean_Syntax_getArg(v_x_1379_, v___x_1415_);
                                    crate::leanh::lean_dec(v_x_1379_);
                                    v___x_1417_ = crate::leanh::lean_box((v___x_1406_) as usize);
                                    v___f_1418_ = crate::leanh::lean_alloc_closure(l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___lam__0___boxed as *mut core::ffi::c_void, 17, 8);
                                    crate::leanh::lean_closure_set(v___f_1418_, 0, v_a_1411_);
                                    crate::leanh::lean_closure_set(v___f_1418_, 1, v___x_1417_);
                                    crate::leanh::lean_closure_set(v___f_1418_, 2, v___x_1389_);
                                    crate::leanh::lean_closure_set(v___f_1418_, 3, v___x_1390_);
                                    crate::leanh::lean_closure_set(v___f_1418_, 4, v___x_1391_);
                                    crate::leanh::lean_closure_set(v___f_1418_, 5, v___x_1396_);
                                    crate::leanh::lean_closure_set(v___f_1418_, 6, v_tk_1416_);
                                    crate::leanh::lean_closure_set(v___f_1418_, 7, v_a_1414_);
                                    v___x_1419_ = l_Lean_Elab_Tactic_withMainContext___redArg(
                                        v___f_1418_,
                                        v_a_1380_,
                                        v_a_1381_,
                                        v_a_1382_,
                                        v_a_1383_,
                                        v_a_1384_,
                                        v_a_1385_,
                                        v_a_1386_,
                                        v_a_1387_,
                                    );
                                    return v___x_1419_;
                                } else {
                                    crate::leanh::lean_dec(v_a_1411_);
                                    crate::leanh::lean_dec(v___x_1396_);
                                    crate::leanh::lean_dec(v_x_1379_);
                                    v_a_1420_ = crate::leanh::lean_ctor_get(v___x_1413_, 0);
                                    v_isSharedCheck_1427_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1413_)) as u8;
                                    if v_isSharedCheck_1427_ == 0 {
                                        v___x_1422_ = v___x_1413_;
                                        v_isShared_1423_ = v_isSharedCheck_1427_;
                                        state = 1;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_1420_);
                                        crate::leanh::lean_dec(v___x_1413_);
                                        v___x_1422_ = crate::leanh::lean_box(0);
                                        v_isShared_1423_ = v_isSharedCheck_1427_;
                                        state = 1;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_path_1401_);
                                crate::leanh::lean_dec(v___x_1396_);
                                crate::leanh::lean_dec(v_x_1379_);
                                v_a_1428_ = crate::leanh::lean_ctor_get(v___x_1410_, 0);
                                v_isSharedCheck_1435_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1410_)) as u8;
                                if v_isSharedCheck_1435_ == 0 {
                                    v___x_1430_ = v___x_1410_;
                                    v_isShared_1431_ = v_isSharedCheck_1435_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1428_);
                                    crate::leanh::lean_dec(v___x_1410_);
                                    v___x_1430_ = crate::leanh::lean_box(0);
                                    v_isShared_1431_ = v_isSharedCheck_1435_;
                                    state = 3;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1423_ == 0 {
                    v___x_1425_ = v___x_1422_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1426_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1426_, 0, v_a_1420_);
                    v___x_1425_ = v_reuseFailAlloc_1426_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1425_;
            }
            3 => {
                if v_isShared_1431_ == 0 {
                    v___x_1433_ = v___x_1430_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1434_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1434_, 0, v_a_1428_);
                    v___x_1433_ = v_reuseFailAlloc_1434_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1433_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___boxed(
    mut v_x_1436_: *mut crate::leanh::LeanObject,
    mut v_a_1437_: *mut crate::leanh::LeanObject,
    mut v_a_1438_: *mut crate::leanh::LeanObject,
    mut v_a_1439_: *mut crate::leanh::LeanObject,
    mut v_a_1440_: *mut crate::leanh::LeanObject,
    mut v_a_1441_: *mut crate::leanh::LeanObject,
    mut v_a_1442_: *mut crate::leanh::LeanObject,
    mut v_a_1443_: *mut crate::leanh::LeanObject,
    mut v_a_1444_: *mut crate::leanh::LeanObject,
    mut v_a_1445_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1446_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck(
        v_x_1436_, v_a_1437_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_, v_a_1443_,
        v_a_1444_,
    );
    crate::leanh::lean_dec(v_a_1444_);
    crate::leanh::lean_dec_ref(v_a_1443_);
    crate::leanh::lean_dec(v_a_1442_);
    crate::leanh::lean_dec_ref(v_a_1441_);
    crate::leanh::lean_dec(v_a_1440_);
    crate::leanh::lean_dec_ref(v_a_1439_);
    crate::leanh::lean_dec(v_a_1438_);
    crate::leanh::lean_dec_ref(v_a_1437_);
    return v_res_1446_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1458_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_1459_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___closed__3;
    v___x_1460_ = l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1___closed__3;
    v___x_1461_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_1462_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1458_,
        v___x_1459_,
        v___x_1460_,
        v___x_1461_,
    );
    return v___x_1462_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1___boxed(
    mut v_a_1463_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1464_ = l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1();
    return v_res_1464_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_BVDecide_BVCheck(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Tactic_BVDecide_BVDecide(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_TryThis(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_TacticContext(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_BVDecide_BVCheck_0__Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_BVCheck_evalBvCheck__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_BVDecide_BVCheck(
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
pub unsafe fn initialize_Lean_Elab_Tactic_BVDecide_BVCheck(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Tactic_BVDecide_BVDecide(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_TryThis(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_BVDecide_TacticContext(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_BVDecide_Normalize(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_BVDecide_BVCheck(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_BVDecide_BVCheck(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_BVDecide_BVCheck(builtin);
}
