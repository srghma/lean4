// Lean compiler output
// Module: Lean.DefEqAttrib
// Imports: Lean.Meta.Basic Lean.Meta.Check Lean.Meta.WHNF
use crate::ffi::{
    lean_array_get, lean_array_push, lean_mk_empty_array_with_capacity, lean_st_mk_ref,
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take, lean_string_dec_eq, lean_uint64_lor,
    lean_uint64_shift_left, lean_uint64_shift_right, lean_whnf,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_Syntax_getPos_x3f, l_Lean_Syntax_getTailPos_x3f, l_Lean_replaceRef,
};
use crate::r#gen::Lean::Attributes::{l_Lean_TagAttribute_hasTag, l_Lean_registerTagAttribute};
use crate::r#gen::Lean::CoreM::{l_Lean_Exception_isRuntime, l_Lean_diagnostics};
use crate::r#gen::Lean::Data::Name::{l_Lean_Name_isAnonymous, l_Lean_Name_isPrefixOf};
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg,
};
use crate::r#gen::Lean::Data::Options::{l_Lean_Options_empty, lean_register_option};
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Data::Position::l_Lean_FileMap_toPosition;
use crate::r#gen::Lean::Declaration::{l_Lean_ConstantInfo_type, l_Lean_ConstantInfo_value_x3f};
use crate::r#gen::Lean::DeclarationRange::l_Lean_addBuiltinDeclarationRanges;
use crate::r#gen::Lean::DocString::Extension::l_Lean_addBuiltinDocString;
use crate::r#gen::Lean::Environment::{
    l_Lean_EnvExtension_asyncMayModify___redArg, l_Lean_Environment_asyncPrefix_x3f,
    l_Lean_Environment_contains, l_Lean_Environment_find_x3f, l_Lean_Environment_findConstVal_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_EnvironmentHeader_moduleNames,
    l_Lean_Kernel_enableDiag, l_Lean_Kernel_isDiagnosticsEnabled,
    l_Lean_PersistentEnvExtension_addEntry___redArg,
};
use crate::r#gen::Lean::Exception::{
    l_Lean_Exception_isInterrupt, l_Lean_Exception_toMessageData,
    l_Lean_unknownIdentifierMessageTag,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appArg_x21, l_Lean_Expr_appFn_x21, l_Lean_Expr_constName_x21, l_Lean_Expr_getAppFn,
    l_Lean_Expr_isAppOfArity, l_Lean_Expr_isConst,
};
use crate::r#gen::Lean::Log::{
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed, l_Lean_warningAsError,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_hasSyntheticSorry, l_Lean_MessageData_hasTag, l_Lean_MessageData_nil,
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofName,
    l_Lean_MessageLog_add, l_Lean_indentD, l_Lean_indentExpr, l_Lean_inlineExpr,
    l_Lean_instBEqMessageSeverity_beq, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    initialize_Lean_Meta_Basic, l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey,
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp,
    l_Lean_MessageData_ofLazyM, l_Lean_Meta_Context_config, l_Lean_Meta_Context_configKey,
    l_Lean_Meta_TransparencyMode_toUInt64, l_Lean_Meta_isExprDefEq,
    runtime_initialize_Lean_Meta_Basic,
};
use crate::r#gen::Lean::Meta::Check::{
    initialize_Lean_Meta_Check, l_Lean_Meta_addPPExplicitToExposeDiff,
    runtime_initialize_Lean_Meta_Check,
};
use crate::r#gen::Lean::Meta::WHNF::{
    initialize_Lean_Meta_WHNF, l_Lean_Meta_smartUnfolding, runtime_initialize_Lean_Meta_WHNF,
};
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::r#gen::Lean::Util::RecDepth::l_Lean_maxRecDepth;
pub static l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__0_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [98, 97, 99, 107, 119, 97, 114, 100, 0]};
static mut l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__0_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__0_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__1_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [100, 101, 102, 101, 113, 65, 116, 116, 114, 105, 98, 0]};
static mut l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__1_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__1_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__2_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [117, 115, 101, 66, 97, 99, 107, 119, 97, 114, 100, 0]};
static mut l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__2_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__2_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
static l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__3_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__0_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__value) as *mut leanh::LeanObject,15861075605163525197 as *mut leanh::LeanObject] };
static l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__3_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__3_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__1_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__value) as *mut leanh::LeanObject,12572168472204864787 as *mut leanh::LeanObject] };
pub static l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__3_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__3_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__2_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__value) as *mut leanh::LeanObject,4477327115298773222 as *mut leanh::LeanObject] };
static mut l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__3_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__3_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__4_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__value: leanh::LeanStringObject<295> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 295, m_capacity: 295, m_length: 294, m_data: [87, 104, 101, 110, 32, 116, 114, 117, 101, 44, 32, 96, 100, 115, 105, 109, 112, 96, 32, 97, 108, 115, 111, 32, 117, 115, 101, 115, 32, 116, 104, 101, 111, 114, 101, 109, 115, 32, 116, 97, 103, 103, 101, 100, 32, 96, 64, 91, 98, 97, 99, 107, 119, 97, 114, 100, 95, 100, 101, 102, 101, 113, 93, 96, 44, 32, 105, 46, 101, 46, 32, 116, 104, 101, 111, 114, 101, 109, 115, 32, 105, 110, 102, 101, 114, 114, 101, 100, 32, 116, 111, 32, 98, 101, 32, 114, 102, 108, 32, 111, 110, 108, 121, 32, 97, 116, 32, 100, 101, 102, 97, 117, 108, 116, 32, 40, 110, 111, 116, 32, 105, 110, 115, 116, 97, 110, 99, 101, 41, 32, 116, 114, 97, 110, 115, 112, 97, 114, 101, 110, 99, 121, 46, 32, 83, 101, 116, 32, 116, 104, 105, 115, 32, 108, 111, 99, 97, 108, 108, 121, 32, 40, 101, 46, 103, 46, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 98, 97, 99, 107, 119, 97, 114, 100, 46, 100, 101, 102, 101, 113, 65, 116, 116, 114, 105, 98, 46, 117, 115, 101, 66, 97, 99, 107, 119, 97, 114, 100, 32, 116, 114, 117, 101, 32, 105, 110, 32, 46, 46, 46, 96, 41, 32, 116, 111, 32, 114, 101, 115, 116, 111, 114, 101, 32, 116, 104, 101, 32, 112, 114, 101, 45, 115, 116, 114, 105, 99, 116, 101, 114, 45, 105, 110, 102, 101, 114, 101, 110, 99, 101, 32, 98, 101, 104, 97, 118, 105, 111, 114, 32, 102, 111, 114, 32, 97, 32, 115, 112, 101, 99, 105, 102, 105, 99, 32, 112, 114, 111, 111, 102, 46, 0]};
static mut l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__4_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__4_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__5_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__4_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__5_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__5_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__6_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__6_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__6_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
static l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__7_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__6_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__7_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__7_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__0_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__value) as *mut leanh::LeanObject,14199879731904694004 as *mut leanh::LeanObject] };
static l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__7_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__7_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__1_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__value) as *mut leanh::LeanObject,9788898074080165014 as *mut leanh::LeanObject] };
pub static l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__7_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__7_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__2_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__value) as *mut leanh::LeanObject,10925962062280780967 as *mut leanh::LeanObject] };
static mut l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__7_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__7_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static mut l_Lean_backward_defeqAttrib_useBackward: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__0_spec__0___closed__0_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__0_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__0_spec__0___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__0_spec__0___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__0_spec__0___closed__0_value) as *mut leanh::LeanObject,14231257465488249300 as *mut leanh::LeanObject] };
static mut l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__0_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__0_spec__0___closed__1_value) as *mut leanh::LeanObject;
static mut l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__0: u64 = 0;
static mut l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__1: u64 = 0;
static mut l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0___closed__0_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0___closed__1_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0___closed__0_value
        ) as *mut leanh::LeanObject,
        16122875713692181903 as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0___closed__1_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0___closed__2_value:
    leanh::LeanStringObject<74> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 74,
    m_capacity: 74,
    m_length: 73,
    m_data: [
        78, 111, 116, 32, 97, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 97, 108, 32,
        101, 113, 117, 97, 108, 105, 116, 121, 58, 32, 116, 104, 101, 32, 99, 111, 110, 99, 108,
        117, 115, 105, 111, 110, 32, 115, 104, 111, 117, 108, 100, 32, 98, 101, 32, 97, 110, 32,
        101, 113, 117, 97, 108, 105, 116, 121, 44, 32, 98, 117, 116, 32, 105, 115, 0,
    ],
};
static mut l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0___closed__2_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_validateDefEqAttr___lam__0___closed__0_value: leanh::LeanStringObject<48> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 48,
        m_capacity: 48,
        m_length: 47,
        m_data: [
            78, 111, 116, 32, 97, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 97, 108,
            32, 101, 113, 117, 97, 108, 105, 116, 121, 58, 32, 116, 104, 101, 32, 108, 101, 102,
            116, 45, 104, 97, 110, 100, 32, 115, 105, 100, 101, 0,
        ],
    };
static mut l_Lean_validateDefEqAttr___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_validateDefEqAttr___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_validateDefEqAttr___lam__0___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_validateDefEqAttr___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_validateDefEqAttr___lam__0___closed__2_value: leanh::LeanStringObject<52> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 52,
        m_capacity: 52,
        m_length: 51,
        m_data: [
            10, 105, 115, 32, 110, 111, 116, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110,
            97, 108, 108, 121, 32, 101, 113, 117, 97, 108, 32, 116, 111, 32, 116, 104, 101, 32,
            114, 105, 103, 104, 116, 45, 104, 97, 110, 100, 32, 115, 105, 100, 101, 0,
        ],
    };
static mut l_Lean_validateDefEqAttr___lam__0___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_validateDefEqAttr___lam__0___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_validateDefEqAttr___lam__0___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_validateDefEqAttr___lam__0___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_validateDefEqAttr___lam__0___closed__4_value: leanh::LeanStringObject<
    149,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 149,
    m_capacity: 149,
    m_length: 148,
    m_data: [
        84, 104, 105, 115, 32, 116, 104, 101, 111, 114, 101, 109, 32, 105, 115, 32, 101, 120, 112,
        111, 114, 116, 101, 100, 32, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114,
        101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 46, 32, 84, 104, 105, 115, 32, 114, 101,
        113, 117, 105, 114, 101, 115, 32, 116, 104, 97, 116, 32, 97, 108, 108, 32, 100, 101, 102,
        105, 110, 105, 116, 105, 111, 110, 115, 32, 116, 104, 97, 116, 32, 110, 101, 101, 100, 32,
        116, 111, 32, 98, 101, 32, 117, 110, 102, 111, 108, 100, 101, 100, 32, 116, 111, 32, 112,
        114, 111, 118, 101, 32, 116, 104, 105, 115, 32, 116, 104, 101, 111, 114, 101, 109, 32, 109,
        117, 115, 116, 32, 98, 101, 32, 101, 120, 112, 111, 115, 101, 100, 46, 0,
    ],
};
static mut l_Lean_validateDefEqAttr___lam__0___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_validateDefEqAttr___lam__0___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lean_validateDefEqAttr___lam__0___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_validateDefEqAttr___lam__0___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_validateDefEqAttr___lam__0___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_validateDefEqAttr___lam__0___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__6_value: leanh::LeanStringObject<24> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__6_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__8_value: leanh::LeanStringObject<79> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__8_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__10_value: leanh::LeanStringObject<23> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__10_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__11_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__11: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__12_value: leanh::LeanStringObject<68> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__12_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__13_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__13: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__14_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__14_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__15_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__15: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__16_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__16_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__17_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__17: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__18_value: leanh::LeanStringObject<54> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__18_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__19_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__19: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__0_value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__2_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_validateDefEqAttr___closed__0_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0
                + 24) as u16,
            other: 0,
            tag: 0,
        },
        m_objs: [
            282574488338432 as *mut leanh::LeanObject,
            72621647814721793 as *mut leanh::LeanObject,
            65793 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_validateDefEqAttr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_validateDefEqAttr___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_validateDefEqAttr___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_validateDefEqAttr___closed__1: u64 = 0;
static mut l_Lean_validateDefEqAttr___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_validateDefEqAttr___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_validateDefEqAttr___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_validateDefEqAttr___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_validateDefEqAttr___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_validateDefEqAttr___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_validateDefEqAttr___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_validateDefEqAttr___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_validateDefEqAttr___closed__6_value: leanh::LeanArrayObject<0> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_validateDefEqAttr___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_validateDefEqAttr___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Lean_validateDefEqAttr___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_validateDefEqAttr___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_validateDefEqAttr___closed__8_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_validateDefEqAttr___closed__8: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_validateDefEqAttr___closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_validateDefEqAttr___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_validateDefEqAttr___closed__10_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_validateDefEqAttr___closed__10: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_validateDefEqAttr___closed__11_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_validateDefEqAttr___closed__11: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_validateDefEqAttr___closed__12_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_validateDefEqAttr___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_validateDefEqAttr___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_validateDefEqAttr___closed__12_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__0_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2__value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [98, 97, 99, 107, 119, 97, 114, 100, 95, 100, 101, 102, 101, 113, 0]};
static mut l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__0_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__0_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__1_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__0_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2__value) as *mut leanh::LeanObject,12429722056590110245 as *mut leanh::LeanObject] };
static mut l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__1_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__1_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__2_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2__value: leanh::LeanStringObject<163> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 163, m_capacity: 163, m_length: 162, m_data: [109, 97, 114, 107, 32, 116, 104, 101, 111, 114, 101, 109, 32, 97, 115, 32, 97, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 97, 108, 32, 101, 113, 117, 97, 108, 105, 116, 121, 32, 117, 110, 100, 101, 114, 32, 116, 104, 101, 32, 112, 101, 114, 109, 105, 115, 115, 105, 118, 101, 32, 112, 114, 101, 45, 115, 116, 114, 105, 99, 116, 101, 114, 45, 105, 110, 102, 101, 114, 101, 110, 99, 101, 32, 114, 117, 108, 101, 115, 44, 32, 117, 115, 101, 100, 32, 98, 121, 32, 96, 100, 115, 105, 109, 112, 96, 32, 119, 104, 101, 110, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 98, 97, 99, 107, 119, 97, 114, 100, 46, 100, 101, 102, 101, 113, 65, 116, 116, 114, 105, 98, 46, 117, 115, 101, 66, 97, 99, 107, 119, 97, 114, 100, 32, 116, 114, 117, 101, 96, 0]};
static mut l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__2_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__2_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__3_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_validateDefEqAttr___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__3_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__3_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__4_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2__value: leanh::LeanStringObject<18> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [98, 97, 99, 107, 119, 97, 114, 100, 68, 101, 102, 101, 113, 65, 116, 116, 114, 0]};
static mut l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__4_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__4_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__5_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__6_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
pub static l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__5_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__5_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__4_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2__value) as *mut leanh::LeanObject,14531735064061357649 as *mut leanh::LeanObject] };
static mut l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__5_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__5_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__6_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2__value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*0 + 8) as u16, other: 0, tag: 3 }, m_objs: [0 as *mut leanh::LeanObject] };
static mut l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__6_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__6_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static mut l_Lean_backwardDefeqAttr: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_docString__1___closed__0_value: leanh::LeanStringObject<863> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 863, m_capacity: 863, m_length: 862, m_data: [77, 97, 114, 107, 115, 32, 97, 32, 116, 104, 101, 111, 114, 101, 109, 32, 97, 115, 32, 97, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 97, 108, 32, 101, 113, 117, 97, 108, 105, 116, 121, 32, 117, 110, 100, 101, 114, 32, 116, 104, 101, 32, 112, 101, 114, 109, 105, 115, 115, 105, 118, 101, 32, 116, 114, 97, 110, 115, 112, 97, 114, 101, 110, 99, 121, 32, 114, 117, 108, 101, 115, 32, 116, 104, 97, 116, 10, 112, 114, 101, 100, 97, 116, 101, 100, 32, 116, 104, 101, 32, 115, 116, 114, 105, 99, 116, 101, 114, 32, 96, 64, 91, 100, 101, 102, 101, 113, 93, 96, 32, 105, 110, 102, 101, 114, 101, 110, 99, 101, 32, 40, 105, 46, 101, 46, 32, 97, 110, 32, 101, 113, 117, 97, 108, 105, 116, 121, 32, 116, 104, 97, 116, 32, 104, 111, 108, 100, 115, 32, 97, 116, 32, 96, 46, 100, 101, 102, 97, 117, 108, 116, 96, 32, 111, 114, 10, 96, 46, 97, 108, 108, 96, 32, 116, 114, 97, 110, 115, 112, 97, 114, 101, 110, 99, 121, 44, 32, 98, 117, 116, 32, 112, 111, 115, 115, 105, 98, 108, 121, 32, 110, 111, 116, 32, 97, 116, 32, 96, 46, 105, 110, 115, 116, 97, 110, 99, 101, 115, 96, 32, 116, 114, 97, 110, 115, 112, 97, 114, 101, 110, 99, 121, 32, 97, 115, 32, 114, 101, 113, 117, 105, 114, 101, 100, 32, 98, 121, 32, 96, 100, 115, 105, 109, 112, 96, 41, 46, 10, 10, 83, 117, 99, 104, 32, 116, 104, 101, 111, 114, 101, 109, 115, 32, 97, 114, 101, 32, 105, 110, 102, 101, 114, 114, 101, 100, 32, 97, 117, 116, 111, 109, 97, 116, 105, 99, 97, 108, 108, 121, 32, 98, 121, 32, 96, 105, 110, 102, 101, 114, 68, 101, 102, 69, 113, 65, 116, 116, 114, 96, 58, 32, 97, 110, 121, 32, 116, 104, 101, 111, 114, 101, 109, 32, 116, 104, 97, 116, 32, 116, 104, 101, 32, 111, 108, 100, 10, 96, 58, 61, 32, 114, 102, 108, 96, 32, 105, 110, 102, 101, 114, 101, 110, 99, 101, 32, 119, 111, 117, 108, 100, 32, 104, 97, 118, 101, 32, 97, 99, 99, 101, 112, 116, 101, 100, 32, 105, 115, 32, 116, 97, 103, 103, 101, 100, 32, 96, 64, 91, 98, 97, 99, 107, 119, 97, 114, 100, 95, 100, 101, 102, 101, 113, 93, 96, 44, 32, 97, 110, 100, 32, 97, 100, 100, 105, 116, 105, 111, 110, 97, 108, 108, 121, 10, 116, 97, 103, 103, 101, 100, 32, 96, 64, 91, 100, 101, 102, 101, 113, 93, 96, 32, 119, 104, 101, 110, 32, 105, 116, 32, 97, 108, 115, 111, 32, 112, 97, 115, 115, 101, 115, 32, 116, 104, 101, 32, 115, 116, 114, 105, 99, 116, 101, 114, 32, 99, 104, 101, 99, 107, 32, 97, 116, 32, 105, 110, 115, 116, 97, 110, 99, 101, 32, 116, 114, 97, 110, 115, 112, 97, 114, 101, 110, 99, 121, 46, 10, 10, 96, 100, 115, 105, 109, 112, 96, 32, 105, 103, 110, 111, 114, 101, 115, 32, 96, 64, 91, 98, 97, 99, 107, 119, 97, 114, 100, 95, 100, 101, 102, 101, 113, 93, 96, 32, 116, 104, 101, 111, 114, 101, 109, 115, 32, 98, 121, 32, 100, 101, 102, 97, 117, 108, 116, 46, 32, 83, 101, 116, 116, 105, 110, 103, 10, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 98, 97, 99, 107, 119, 97, 114, 100, 46, 100, 101, 102, 101, 113, 65, 116, 116, 114, 105, 98, 46, 117, 115, 101, 66, 97, 99, 107, 119, 97, 114, 100, 32, 116, 114, 117, 101, 96, 32, 40, 116, 121, 112, 105, 99, 97, 108, 108, 121, 32, 115, 99, 111, 112, 101, 100, 32, 116, 111, 32, 97, 32, 115, 105, 110, 103, 108, 101, 32, 112, 114, 111, 111, 102, 10, 119, 105, 116, 104, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 46, 46, 46, 32, 105, 110, 96, 41, 32, 109, 97, 107, 101, 115, 32, 96, 100, 115, 105, 109, 112, 96, 32, 116, 114, 101, 97, 116, 32, 116, 104, 101, 109, 32, 108, 105, 107, 101, 32, 96, 64, 91, 100, 101, 102, 101, 113, 93, 96, 32, 116, 104, 101, 111, 114, 101, 109, 115, 44, 32, 119, 104, 105, 99, 104, 10, 112, 114, 111, 118, 105, 100, 101, 115, 32, 97, 32, 108, 111, 99, 97, 108, 32, 98, 97, 99, 107, 119, 97, 114, 100, 115, 45, 99, 111, 109, 112, 97, 116, 105, 98, 105, 108, 105, 116, 121, 32, 101, 115, 99, 97, 112, 101, 32, 104, 97, 116, 99, 104, 32, 102, 111, 114, 32, 112, 114, 111, 111, 102, 115, 32, 98, 114, 111, 107, 101, 110, 32, 98, 121, 32, 116, 104, 101, 32, 115, 116, 114, 105, 99, 116, 101, 114, 10, 105, 110, 102, 101, 114, 101, 110, 99, 101, 46, 10, 0]};
static mut l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_docString__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_docString__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 70 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___closed__1_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 91 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 34 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___closed__2_value: leanh::LeanCtorObject<4> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___closed__0_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___closed__1_value) as *mut leanh::LeanObject,((( 34 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___closed__3_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 86 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 19 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___closed__4_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 86 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 36 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___closed__5_value: leanh::LeanCtorObject<4> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___closed__3_value) as *mut leanh::LeanObject,((( 19 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___closed__4_value) as *mut leanh::LeanObject,((( 36 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___closed__6_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___closed__2_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___closed__5_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___closed__6_value) as *mut leanh::LeanObject;
pub static l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0_value: leanh::LeanStringObject<24> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [67, 97, 110, 110, 111, 116, 32, 97, 100, 100, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 96, 91, 0]};
static mut l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__2_value: leanh::LeanStringObject<20> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [93, 96, 32, 116, 111, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__4_value: leanh::LeanStringObject<51> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 51, m_capacity: 51, m_length: 50, m_data: [96, 32, 98, 101, 99, 97, 117, 115, 101, 32, 105, 116, 32, 105, 115, 32, 110, 111, 116, 32, 102, 114, 111, 109, 32, 116, 104, 101, 32, 112, 114, 101, 115, 101, 110, 116, 32, 97, 115, 121, 110, 99, 32, 99, 111, 110, 116, 101, 120, 116, 0]};
static mut l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__4_value) as *mut leanh::LeanObject;
static mut l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__6_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [32, 96, 0]};
static mut l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__6_value) as *mut leanh::LeanObject;
static mut l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__1___redArg___closed__0_value: leanh::LeanStringObject<38> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 38, m_capacity: 38, m_length: 37, m_data: [96, 32, 98, 101, 99, 97, 117, 115, 101, 32, 105, 116, 32, 105, 115, 32, 105, 110, 32, 97, 110, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 109, 111, 100, 117, 108, 101, 0]};
static mut l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__1___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__1___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__1___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__0_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_DefEqAttrib_0__Lean_initFn___lam__0_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__0_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__0_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__1_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [100, 101, 102, 101, 113, 0]};
static mut l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__1_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__1_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__2_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__1_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__value) as *mut leanh::LeanObject,4826972851695508558 as *mut leanh::LeanObject] };
static mut l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__2_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__2_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__3_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__value: leanh::LeanStringObject<63> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 63, m_capacity: 63, m_length: 62, m_data: [109, 97, 114, 107, 32, 116, 104, 101, 111, 114, 101, 109, 32, 97, 115, 32, 97, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 97, 108, 32, 101, 113, 117, 97, 108, 105, 116, 121, 44, 32, 116, 111, 32, 98, 101, 32, 117, 115, 101, 100, 32, 98, 121, 32, 96, 100, 115, 105, 109, 112, 96, 0]};
static mut l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__3_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__3_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__4_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [100, 101, 102, 101, 113, 65, 116, 116, 114, 0]};
static mut l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__4_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__4_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__5_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__6_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
pub static l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__5_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__5_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__4_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__value) as *mut leanh::LeanObject,12944298589636027774 as *mut leanh::LeanObject] };
static mut l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__5_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__5_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static mut l_Lean_defeqAttr: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_docString__1___closed__0_value: leanh::LeanStringObject<776> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 776, m_capacity: 776, m_length: 775, m_data: [77, 97, 114, 107, 115, 32, 116, 104, 101, 32, 116, 104, 101, 111, 114, 101, 109, 32, 97, 115, 32, 97, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 97, 108, 32, 101, 113, 117, 97, 108, 105, 116, 121, 32, 116, 104, 97, 116, 32, 99, 97, 110, 32, 98, 101, 32, 117, 115, 101, 100, 32, 98, 121, 32, 96, 100, 115, 105, 109, 112, 96, 46, 10, 10, 84, 104, 101, 32, 116, 104, 101, 111, 114, 101, 109, 32, 109, 117, 115, 116, 32, 98, 101, 32, 97, 110, 32, 101, 113, 117, 97, 108, 105, 116, 121, 32, 116, 104, 97, 116, 32, 104, 111, 108, 100, 115, 32, 97, 116, 32, 96, 46, 105, 110, 115, 116, 97, 110, 99, 101, 115, 96, 32, 116, 114, 97, 110, 115, 112, 97, 114, 101, 110, 99, 121, 46, 32, 65, 32, 116, 104, 101, 111, 114, 101, 109, 10, 119, 105, 116, 104, 32, 97, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 32, 116, 104, 97, 116, 32, 105, 115, 32, 40, 115, 121, 110, 116, 97, 99, 116, 105, 99, 97, 108, 108, 121, 41, 32, 96, 58, 61, 32, 114, 102, 108, 96, 32, 105, 115, 32, 105, 109, 112, 108, 105, 99, 105, 116, 108, 121, 32, 109, 97, 114, 107, 101, 100, 32, 96, 64, 91, 100, 101, 102, 101, 113, 93, 96, 10, 40, 97, 110, 100, 32, 97, 108, 115, 111, 32, 96, 64, 91, 98, 97, 99, 107, 119, 97, 114, 100, 95, 100, 101, 102, 101, 113, 93, 96, 44, 32, 115, 105, 110, 99, 101, 32, 116, 104, 101, 32, 108, 97, 116, 116, 101, 114, 32, 105, 115, 32, 97, 32, 115, 117, 112, 101, 114, 115, 101, 116, 41, 59, 32, 119, 114, 105, 116, 101, 32, 96, 58, 61, 32, 40, 114, 102, 108, 41, 96, 10, 105, 110, 115, 116, 101, 97, 100, 32, 116, 111, 32, 115, 117, 112, 112, 114, 101, 115, 115, 32, 116, 104, 105, 115, 46, 10, 10, 84, 104, 101, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 115, 104, 111, 117, 108, 100, 32, 98, 101, 32, 103, 105, 118, 101, 110, 32, 98, 101, 102, 111, 114, 101, 32, 97, 32, 96, 64, 91, 115, 105, 109, 112, 93, 96, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 116, 111, 32, 104, 97, 118, 101, 32, 101, 102, 102, 101, 99, 116, 46, 10, 10, 87, 104, 101, 110, 32, 117, 115, 105, 110, 103, 32, 116, 104, 101, 32, 109, 111, 100, 117, 108, 101, 32, 115, 121, 115, 116, 101, 109, 44, 32, 97, 110, 32, 101, 120, 112, 111, 114, 116, 101, 100, 32, 116, 104, 101, 111, 114, 101, 109, 32, 99, 97, 110, 32, 111, 110, 108, 121, 32, 98, 101, 32, 96, 64, 91, 100, 101, 102, 101, 113, 93, 96, 32, 105, 102, 32, 97, 108, 108, 10, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 115, 32, 116, 104, 97, 116, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 117, 110, 102, 111, 108, 100, 101, 100, 32, 116, 111, 32, 112, 114, 111, 118, 101, 32, 116, 104, 101, 32, 116, 104, 101, 111, 114, 101, 109, 32, 97, 114, 101, 32, 101, 120, 112, 111, 114, 116, 101, 100, 32, 97, 110, 100, 32, 101, 120, 112, 111, 115, 101, 100, 46, 10, 10, 84, 97, 103, 103, 105, 110, 103, 32, 97, 32, 116, 104, 101, 111, 114, 101, 109, 32, 119, 105, 116, 104, 32, 96, 64, 91, 100, 101, 102, 101, 113, 93, 96, 32, 97, 117, 116, 111, 109, 97, 116, 105, 99, 97, 108, 108, 121, 32, 97, 108, 115, 111, 32, 116, 97, 103, 115, 32, 105, 116, 32, 119, 105, 116, 104, 32, 96, 64, 91, 98, 97, 99, 107, 119, 97, 114, 100, 95, 100, 101, 102, 101, 113, 93, 96, 44, 10, 109, 97, 105, 110, 116, 97, 105, 110, 105, 110, 103, 32, 116, 104, 101, 32, 105, 110, 118, 97, 114, 105, 97, 110, 116, 32, 116, 104, 97, 116, 32, 96, 64, 91, 100, 101, 102, 101, 113, 93, 96, 32, 116, 104, 101, 111, 114, 101, 109, 115, 32, 102, 111, 114, 109, 32, 97, 32, 115, 117, 98, 115, 101, 116, 32, 111, 102, 32, 96, 64, 91, 98, 97, 99, 107, 119, 97, 114, 100, 95, 100, 101, 102, 101, 113, 93, 96, 10, 116, 104, 101, 111, 114, 101, 109, 115, 46, 10, 0]};
static mut l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_docString__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_docString__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 93 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__1_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 119 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 34 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__2_value: leanh::LeanCtorObject<4> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__0_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__1_value) as *mut leanh::LeanObject,((( 34 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__3_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 111 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 19 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__4_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 111 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 28 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__5_value: leanh::LeanCtorObject<4> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__3_value) as *mut leanh::LeanObject,((( 19 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__4_value) as *mut leanh::LeanObject,((( 28 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__6_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__2_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__5_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__0_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__0_value
) as *mut leanh::LeanObject;
static l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__1_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0___closed__0_value
        ) as *mut leanh::LeanObject,
        16122875713692181903 as *mut leanh::LeanObject,
    ],
};
pub static l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__1_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__1_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__0_value
        ) as *mut leanh::LeanObject,
        13480818501600609864 as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__1_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__2_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [114, 102, 108, 0],
};
static mut l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__2_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__3_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__2_value
        ) as *mut leanh::LeanObject,
        17342663138809293389 as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__3_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__4_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [115, 121, 109, 109, 0],
};
static mut l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__4_value
) as *mut leanh::LeanObject;
static l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__5_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0___closed__0_value
        ) as *mut leanh::LeanObject,
        16122875713692181903 as *mut leanh::LeanObject,
    ],
};
pub static l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__5_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__5_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__4_value
        ) as *mut leanh::LeanObject,
        15643637366941324764 as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__5_value
) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__1_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__2_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [117, 110, 115, 111, 108, 118, 101, 100, 71, 111, 97, 108, 115, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__3_value: leanh::LeanStringObject<17> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 121, 110, 116, 104, 80, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__4_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 101, 97, 110, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__5_value: leanh::LeanStringObject<20> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 110, 100, 117, 99, 116, 105, 111, 110, 87, 105, 116, 104, 78, 111, 65, 108, 116, 115, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__5_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__6_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [95, 110, 97, 109, 101, 100, 69, 114, 114, 111, 114, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__6_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___closed__0_value: leanh::LeanStringObject<1> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_inferDefEqAttr___lam__0___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_inferDefEqAttr___lam__0___closed__0: u64 = 0;
pub static l_Lean_inferDefEqAttr___lam__1___closed__0_value: leanh::LeanStringObject<9> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [84, 104, 101, 111, 114, 101, 109, 32, 0],
    };
static mut l_Lean_inferDefEqAttr___lam__1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_inferDefEqAttr___lam__1___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_inferDefEqAttr___lam__1___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_inferDefEqAttr___lam__1___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_inferDefEqAttr___lam__1___closed__2_value: leanh::LeanStringObject<74> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 74,
        m_capacity: 74,
        m_length: 73,
        m_data: [
            32, 104, 97, 115, 32, 97, 32, 96, 114, 102, 108, 96, 45, 112, 114, 111, 111, 102, 32,
            98, 117, 116, 32, 99, 111, 117, 108, 100, 32, 110, 111, 116, 32, 98, 101, 32, 118, 97,
            108, 105, 100, 97, 116, 101, 100, 32, 97, 115, 32, 97, 32, 100, 101, 102, 105, 110,
            105, 116, 105, 111, 110, 97, 108, 32, 101, 113, 117, 97, 108, 105, 116, 121, 58, 0,
        ],
    };
static mut l_Lean_inferDefEqAttr___lam__1___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_inferDefEqAttr___lam__1___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_inferDefEqAttr___lam__1___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_inferDefEqAttr___lam__1___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_inferDefEqAttr___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_inferDefEqAttr___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_inferDefEqAttr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_inferDefEqAttr___closed__0_value) as *mut leanh::LeanObject;
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__spec__0(
    mut v_name_2662_: *mut leanh::LeanObject,
    mut v_decl_2663_: *mut leanh::LeanObject,
    mut v_ref_2664_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_defValue_2666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_descr_2667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_2668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: u8 = 0;
    let mut v___x_2671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2675_: u8 = 0;
    let mut v___x_2676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2680_: u8 = 0;
    let mut v_unused_2681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2685_: u8 = 0;
    let mut v___x_2687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2689_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_2666_ = leanh::lean_ctor_get(v_decl_2663_, 0);
                v_descr_2667_ = leanh::lean_ctor_get(v_decl_2663_, 1);
                v_deprecation_x3f_2668_ = leanh::lean_ctor_get(v_decl_2663_, 2);
                v___x_2669_ = leanh::lean_alloc_ctor(1, 0, (1) as u32);
                v___x_2670_ = (leanh::lean_unbox(v_defValue_2666_) as u8);
                leanh::lean_ctor_set_uint8(v___x_2669_, 0 as u32, v___x_2670_);
                leanh::lean_inc(v_deprecation_x3f_2668_);
                leanh::lean_inc_ref(v_descr_2667_);
                leanh::lean_inc_n(v_name_2662_, 2);
                v___x_2671_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_2671_, 0, v_name_2662_);
                leanh::lean_ctor_set(v___x_2671_, 1, v_ref_2664_);
                leanh::lean_ctor_set(v___x_2671_, 2, v___x_2669_);
                leanh::lean_ctor_set(v___x_2671_, 3, v_descr_2667_);
                leanh::lean_ctor_set(v___x_2671_, 4, v_deprecation_x3f_2668_);
                v___x_2672_ = lean_register_option(v_name_2662_, v___x_2671_);
                if leanh::lean_obj_tag(v___x_2672_) == 0 {
                    v_isSharedCheck_2680_ = (!leanh::lean_is_exclusive(v___x_2672_)) as u8;
                    if v_isSharedCheck_2680_ == 0 {
                        v_unused_2681_ = leanh::lean_ctor_get(v___x_2672_, 0);
                        leanh::lean_dec(v_unused_2681_);
                        v___x_2674_ = v___x_2672_;
                        v_isShared_2675_ = v_isSharedCheck_2680_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_2672_);
                        v___x_2674_ = leanh::lean_box(0);
                        v_isShared_2675_ = v_isSharedCheck_2680_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_name_2662_);
                    v_a_2682_ = leanh::lean_ctor_get(v___x_2672_, 0);
                    v_isSharedCheck_2689_ = (!leanh::lean_is_exclusive(v___x_2672_)) as u8;
                    if v_isSharedCheck_2689_ == 0 {
                        v___x_2684_ = v___x_2672_;
                        v_isShared_2685_ = v_isSharedCheck_2689_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2682_);
                        leanh::lean_dec(v___x_2672_);
                        v___x_2684_ = leanh::lean_box(0);
                        v_isShared_2685_ = v_isSharedCheck_2689_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_defValue_2666_);
                v___x_2676_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2676_, 0, v_name_2662_);
                leanh::lean_ctor_set(v___x_2676_, 1, v_defValue_2666_);
                if v_isShared_2675_ == 0 {
                    leanh::lean_ctor_set(v___x_2674_, 0, v___x_2676_);
                    v___x_2678_ = v___x_2674_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2679_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2679_, 0, v___x_2676_);
                    v___x_2678_ = v_reuseFailAlloc_2679_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2678_;
            }
            3 => {
                if v_isShared_2685_ == 0 {
                    v___x_2687_ = v___x_2684_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2688_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2688_, 0, v_a_2682_);
                    v___x_2687_ = v_reuseFailAlloc_2688_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2687_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__spec__0___boxed(
    mut v_name_2690_: *mut leanh::LeanObject,
    mut v_decl_2691_: *mut leanh::LeanObject,
    mut v_ref_2692_: *mut leanh::LeanObject,
    mut v_a_2693_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2694_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2694_ = l_Lean_Option_register___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__spec__0(v_name_2690_, v_decl_2691_, v_ref_2692_);
    leanh::lean_dec_ref(v_decl_2691_);
    return v_res_2694_;
}
pub unsafe fn l___private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4_()
-> *mut leanh::LeanObject {
    let mut v___x_2715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2715_ = l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__3_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4_;
    v___x_2716_ = l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__5_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4_;
    v___x_2717_ = l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__7_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4_;
    v___x_2718_ = l_Lean_Option_register___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4__spec__0(v___x_2715_, v___x_2716_, v___x_2717_);
    return v___x_2718_;
}
pub unsafe fn l___private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4____boxed(
    mut v_a_2719_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2720_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2720_ = l___private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4_();
    return v_res_2720_;
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__1(
    mut v_opts_2721_: *mut leanh::LeanObject,
    mut v_opt_2722_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_name_2723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_2724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_2723_ = leanh::lean_ctor_get(v_opt_2722_, 0);
    v_defValue_2724_ = leanh::lean_ctor_get(v_opt_2722_, 1);
    v_map_2725_ = leanh::lean_ctor_get(v_opts_2721_, 0);
    v___x_2726_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2725_,
            v_name_2723_,
        );
    if leanh::lean_obj_tag(v___x_2726_) == 0 {
        let mut v___x_2727_: u8 = 0;
        v___x_2727_ = (leanh::lean_unbox(v_defValue_2724_) as u8);
        return v___x_2727_;
    } else {
        let mut v_val_2728_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2728_ = leanh::lean_ctor_get(v___x_2726_, 0);
        leanh::lean_inc(v_val_2728_);
        leanh::lean_dec_ref_known(v___x_2726_, 1);
        if leanh::lean_obj_tag(v_val_2728_) == 1 {
            let mut v_v_2729_: u8 = 0;
            v_v_2729_ = leanh::lean_ctor_get_uint8(v_val_2728_, 0 as u32);
            leanh::lean_dec_ref_known(v_val_2728_, 0);
            return v_v_2729_;
        } else {
            let mut v___x_2730_: u8 = 0;
            leanh::lean_dec(v_val_2728_);
            v___x_2730_ = (leanh::lean_unbox(v_defValue_2724_) as u8);
            return v___x_2730_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__1___boxed(
    mut v_opts_2731_: *mut leanh::LeanObject,
    mut v_opt_2732_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2733_: u8 = 0;
    let mut v_r_2734_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2733_ =
        l_Lean_Option_get___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__1(
            v_opts_2731_,
            v_opt_2732_,
        );
    leanh::lean_dec_ref(v_opt_2732_);
    leanh::lean_dec_ref(v_opts_2731_);
    v_r_2734_ = leanh::lean_box((v_res_2733_) as usize);
    return v_r_2734_;
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__2(
    mut v_opts_2735_: *mut leanh::LeanObject,
    mut v_opt_2736_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_name_2737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_2738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2740_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_2737_ = leanh::lean_ctor_get(v_opt_2736_, 0);
    v_defValue_2738_ = leanh::lean_ctor_get(v_opt_2736_, 1);
    v_map_2739_ = leanh::lean_ctor_get(v_opts_2735_, 0);
    v___x_2740_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2739_,
            v_name_2737_,
        );
    if leanh::lean_obj_tag(v___x_2740_) == 0 {
        leanh::lean_inc(v_defValue_2738_);
        return v_defValue_2738_;
    } else {
        let mut v_val_2741_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2741_ = leanh::lean_ctor_get(v___x_2740_, 0);
        leanh::lean_inc(v_val_2741_);
        leanh::lean_dec_ref_known(v___x_2740_, 1);
        if leanh::lean_obj_tag(v_val_2741_) == 3 {
            let mut v_v_2742_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_v_2742_ = leanh::lean_ctor_get(v_val_2741_, 0);
            leanh::lean_inc(v_v_2742_);
            leanh::lean_dec_ref_known(v_val_2741_, 1);
            return v_v_2742_;
        } else {
            leanh::lean_dec(v_val_2741_);
            leanh::lean_inc(v_defValue_2738_);
            return v_defValue_2738_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__2___boxed(
    mut v_opts_2743_: *mut leanh::LeanObject,
    mut v_opt_2744_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2745_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2745_ =
        l_Lean_Option_get___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__2(
            v_opts_2743_,
            v_opt_2744_,
        );
    leanh::lean_dec_ref(v_opt_2744_);
    leanh::lean_dec_ref(v_opts_2743_);
    return v_res_2745_;
}
pub unsafe fn l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__0_spec__0(
    mut v_o_2749_: *mut leanh::LeanObject,
    mut v_k_2750_: *mut leanh::LeanObject,
    mut v_v_2751_: u8,
) -> *mut leanh::LeanObject {
    let mut v_map_2752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_2753_: u8 = 0;
    let mut v___x_2755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2756_: u8 = 0;
    let mut v___x_2757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: u8 = 0;
    let mut v___x_2762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2767_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_map_2752_ = leanh::lean_ctor_get(v_o_2749_, 0);
                v_hasTrace_2753_ = leanh::lean_ctor_get_uint8(
                    v_o_2749_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_2767_ = (!leanh::lean_is_exclusive(v_o_2749_)) as u8;
                if v_isSharedCheck_2767_ == 0 {
                    v___x_2755_ = v_o_2749_;
                    v_isShared_2756_ = v_isSharedCheck_2767_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_map_2752_);
                    leanh::lean_dec(v_o_2749_);
                    v___x_2755_ = leanh::lean_box(0);
                    v_isShared_2756_ = v_isSharedCheck_2767_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2757_ = leanh::lean_alloc_ctor(1, 0, (1) as u32);
                leanh::lean_ctor_set_uint8(v___x_2757_, 0 as u32, v_v_2751_);
                leanh::lean_inc(v_k_2750_);
                v___x_2758_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_2750_, v___x_2757_, v_map_2752_);
                if v_hasTrace_2753_ == 0 {
                    v___x_2759_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__0_spec__0___closed__1;
                    v___x_2760_ = l_Lean_Name_isPrefixOf(v___x_2759_, v_k_2750_);
                    leanh::lean_dec(v_k_2750_);
                    if v_isShared_2756_ == 0 {
                        leanh::lean_ctor_set(v___x_2755_, 0, v___x_2758_);
                        v___x_2762_ = v___x_2755_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2763_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2763_, 0, v___x_2758_);
                        v___x_2762_ = v_reuseFailAlloc_2763_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_k_2750_);
                    if v_isShared_2756_ == 0 {
                        leanh::lean_ctor_set(v___x_2755_, 0, v___x_2758_);
                        v___x_2765_ = v___x_2755_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2766_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2766_, 0, v___x_2758_);
                        leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_2766_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                            v_hasTrace_2753_,
                        );
                        v___x_2765_ = v_reuseFailAlloc_2766_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                leanh::lean_ctor_set_uint8(
                    v___x_2762_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_2760_,
                );
                return v___x_2762_;
            }
            3 => {
                return v___x_2765_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__0_spec__0___boxed(
    mut v_o_2768_: *mut leanh::LeanObject,
    mut v_k_2769_: *mut leanh::LeanObject,
    mut v_v_2770_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_v_boxed_2771_: u8 = 0;
    let mut v_res_2772_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_v_boxed_2771_ = (leanh::lean_unbox(v_v_2770_) as u8);
    v_res_2772_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__0_spec__0(v_o_2768_, v_k_2769_, v_v_boxed_2771_);
    return v_res_2772_;
}
pub unsafe fn l_Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__0(
    mut v_opts_2773_: *mut leanh::LeanObject,
    mut v_opt_2774_: *mut leanh::LeanObject,
    mut v_val_2775_: u8,
) -> *mut leanh::LeanObject {
    let mut v_name_2776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2777_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_2776_ = leanh::lean_ctor_get(v_opt_2774_, 0);
    leanh::lean_inc(v_name_2776_);
    leanh::lean_dec_ref(v_opt_2774_);
    v___x_2777_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__0_spec__0(v_opts_2773_, v_name_2776_, v_val_2775_);
    return v___x_2777_;
}
pub unsafe fn l_Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__0___boxed(
    mut v_opts_2778_: *mut leanh::LeanObject,
    mut v_opt_2779_: *mut leanh::LeanObject,
    mut v_val_2780_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_val_boxed_2781_: u8 = 0;
    let mut v_res_2782_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_val_boxed_2781_ = (leanh::lean_unbox(v_val_2780_) as u8);
    v_res_2782_ =
        l_Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__0(
            v_opts_2778_,
            v_opt_2779_,
            v_val_boxed_2781_,
        );
    return v_res_2782_;
}
pub unsafe fn _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__0() -> u64 {
    let mut v___x_2783_: u8 = 0;
    let mut v___x_2784_: u64 = 0;
    v___x_2783_ = 1;
    v___x_2784_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_2783_);
    return v___x_2784_;
}
pub unsafe fn _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__1() -> u64 {
    let mut v___x_2785_: u8 = 0;
    let mut v___x_2786_: u64 = 0;
    v___x_2785_ = 0;
    v___x_2786_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_2785_);
    return v___x_2786_;
}
pub unsafe fn _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2787_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2787_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_2787_;
}
pub unsafe fn _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2789_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2788_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2),
        core::ptr::addr_of_mut!(
            l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2_once
        ),
        _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2,
    );
    v___x_2789_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2789_, 0, v___x_2788_);
    return v___x_2789_;
}
pub unsafe fn _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_2790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2790_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__3),
        core::ptr::addr_of_mut!(
            l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__3_once
        ),
        _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__3,
    );
    v___x_2791_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2791_, 0, v___x_2790_);
    leanh::lean_ctor_set(v___x_2791_, 1, v___x_2790_);
    return v___x_2791_;
}
pub unsafe fn l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful(
    mut v_e1_2792_: *mut leanh::LeanObject,
    mut v_e2_2793_: *mut leanh::LeanObject,
    mut v_a_2794_: *mut leanh::LeanObject,
    mut v_a_2795_: *mut leanh::LeanObject,
    mut v_a_2796_: *mut leanh::LeanObject,
    mut v_a_2797_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_2800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_2807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_2808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_2811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2812_: u8 = 0;
    let mut v_inheritedTraceOptions_2813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: u8 = 0;
    let mut v___x_2816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: u8 = 0;
    let mut v___x_2818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: u8 = 0;
    let mut v_fileName_2822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_2828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_2829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_2832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2833_: u8 = 0;
    let mut v_inheritedTraceOptions_2834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_foApprox_2837_: u8 = 0;
    let mut v_ctxApprox_2838_: u8 = 0;
    let mut v_quasiPatternApprox_2839_: u8 = 0;
    let mut v_constApprox_2840_: u8 = 0;
    let mut v_isDefEqStuckEx_2841_: u8 = 0;
    let mut v_unificationHints_2842_: u8 = 0;
    let mut v_proofIrrelevance_2843_: u8 = 0;
    let mut v_assignSyntheticOpaque_2844_: u8 = 0;
    let mut v_offsetCnstrs_2845_: u8 = 0;
    let mut v_etaStruct_2846_: u8 = 0;
    let mut v_univApprox_2847_: u8 = 0;
    let mut v_iota_2848_: u8 = 0;
    let mut v_beta_2849_: u8 = 0;
    let mut v_proj_2850_: u8 = 0;
    let mut v_zeta_2851_: u8 = 0;
    let mut v_zetaDelta_2852_: u8 = 0;
    let mut v_zetaUnused_2853_: u8 = 0;
    let mut v_zetaHave_2854_: u8 = 0;
    let mut v___x_2856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2857_: u8 = 0;
    let mut v_trackZetaDelta_2858_: u8 = 0;
    let mut v_zetaDeltaSet_2859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_2861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_2862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_2863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_2864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_2865_: u8 = 0;
    let mut v_inTypeClassResolution_2866_: u8 = 0;
    let mut v_cacheInferType_2867_: u8 = 0;
    let mut v___x_2868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: u64 = 0;
    let mut v___x_2873_: u64 = 0;
    let mut v___x_2874_: u64 = 0;
    let mut v___x_2875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2876_: u64 = 0;
    let mut v___x_2877_: u64 = 0;
    let mut v_key_2878_: u64 = 0;
    let mut v___x_2879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2883_: u8 = 0;
    let mut v___x_2884_: u8 = 0;
    let mut v_config_2885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: u64 = 0;
    let mut v_key_2887_: u64 = 0;
    let mut v___x_2888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2892_: u8 = 0;
    let mut v___y_2894_: u8 = 0;
    let mut v___x_2895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2906_: u8 = 0;
    let mut v___x_2907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2913_: u8 = 0;
    let mut v_unused_2914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2915_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2799_ = lean_st_ref_get(v_a_2797_);
                v_fileName_2800_ = leanh::lean_ctor_get(v_a_2796_, 0);
                v_fileMap_2801_ = leanh::lean_ctor_get(v_a_2796_, 1);
                v_options_2802_ = leanh::lean_ctor_get(v_a_2796_, 2);
                v_currRecDepth_2803_ = leanh::lean_ctor_get(v_a_2796_, 3);
                v_ref_2804_ = leanh::lean_ctor_get(v_a_2796_, 5);
                v_currNamespace_2805_ = leanh::lean_ctor_get(v_a_2796_, 6);
                v_openDecls_2806_ = leanh::lean_ctor_get(v_a_2796_, 7);
                v_initHeartbeats_2807_ = leanh::lean_ctor_get(v_a_2796_, 8);
                v_maxHeartbeats_2808_ = leanh::lean_ctor_get(v_a_2796_, 9);
                v_quotContext_2809_ = leanh::lean_ctor_get(v_a_2796_, 10);
                v_currMacroScope_2810_ = leanh::lean_ctor_get(v_a_2796_, 11);
                v_cancelTk_x3f_2811_ = leanh::lean_ctor_get(v_a_2796_, 12);
                v_suppressElabErrors_2812_ = leanh::lean_ctor_get_uint8(
                    v_a_2796_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_2813_ = leanh::lean_ctor_get(v_a_2796_, 13);
                v_env_2814_ = leanh::lean_ctor_get(v___x_2799_, 0);
                leanh::lean_inc_ref(v_env_2814_);
                leanh::lean_dec(v___x_2799_);
                v___x_2815_ = 1;
                v___x_2816_ = l_Lean_Meta_smartUnfolding;
                v___x_2817_ = 0;
                leanh::lean_inc_ref(v_options_2802_);
                v___x_2818_ = l_Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__0(v_options_2802_, v___x_2816_, v___x_2817_);
                v___x_2819_ = l_Lean_diagnostics;
                v___x_2820_ = l_Lean_Option_get___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__1(v___x_2818_, v___x_2819_);
                v___x_2915_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_2814_);
                leanh::lean_dec_ref(v_env_2814_);
                if v___x_2915_ == 0 {
                    if v___x_2820_ == 0 {
                        v_fileName_2822_ = v_fileName_2800_;
                        v_fileMap_2823_ = v_fileMap_2801_;
                        v_currRecDepth_2824_ = v_currRecDepth_2803_;
                        v_ref_2825_ = v_ref_2804_;
                        v_currNamespace_2826_ = v_currNamespace_2805_;
                        v_openDecls_2827_ = v_openDecls_2806_;
                        v_initHeartbeats_2828_ = v_initHeartbeats_2807_;
                        v_maxHeartbeats_2829_ = v_maxHeartbeats_2808_;
                        v_quotContext_2830_ = v_quotContext_2809_;
                        v_currMacroScope_2831_ = v_currMacroScope_2810_;
                        v_cancelTk_x3f_2832_ = v_cancelTk_x3f_2811_;
                        v_suppressElabErrors_2833_ = v_suppressElabErrors_2812_;
                        v_inheritedTraceOptions_2834_ = v_inheritedTraceOptions_2813_;
                        v___y_2835_ = v_a_2797_;
                        state = 1;
                        continue;
                    } else {
                        v___y_2894_ = v___x_2915_;
                        state = 4;
                        continue;
                    }
                } else {
                    v___y_2894_ = v___x_2820_;
                    state = 4;
                    continue;
                }
            }
            1 => {
                v___x_2836_ = l_Lean_Meta_Context_config(v_a_2794_);
                v_foApprox_2837_ = leanh::lean_ctor_get_uint8(v___x_2836_, 0 as u32);
                v_ctxApprox_2838_ = leanh::lean_ctor_get_uint8(v___x_2836_, 1 as u32);
                v_quasiPatternApprox_2839_ =
                    leanh::lean_ctor_get_uint8(v___x_2836_, 2 as u32);
                v_constApprox_2840_ = leanh::lean_ctor_get_uint8(v___x_2836_, 3 as u32);
                v_isDefEqStuckEx_2841_ = leanh::lean_ctor_get_uint8(v___x_2836_, 4 as u32);
                v_unificationHints_2842_ = leanh::lean_ctor_get_uint8(v___x_2836_, 5 as u32);
                v_proofIrrelevance_2843_ = leanh::lean_ctor_get_uint8(v___x_2836_, 6 as u32);
                v_assignSyntheticOpaque_2844_ =
                    leanh::lean_ctor_get_uint8(v___x_2836_, 7 as u32);
                v_offsetCnstrs_2845_ = leanh::lean_ctor_get_uint8(v___x_2836_, 8 as u32);
                v_etaStruct_2846_ = leanh::lean_ctor_get_uint8(v___x_2836_, 10 as u32);
                v_univApprox_2847_ = leanh::lean_ctor_get_uint8(v___x_2836_, 11 as u32);
                v_iota_2848_ = leanh::lean_ctor_get_uint8(v___x_2836_, 12 as u32);
                v_beta_2849_ = leanh::lean_ctor_get_uint8(v___x_2836_, 13 as u32);
                v_proj_2850_ = leanh::lean_ctor_get_uint8(v___x_2836_, 14 as u32);
                v_zeta_2851_ = leanh::lean_ctor_get_uint8(v___x_2836_, 15 as u32);
                v_zetaDelta_2852_ = leanh::lean_ctor_get_uint8(v___x_2836_, 16 as u32);
                v_zetaUnused_2853_ = leanh::lean_ctor_get_uint8(v___x_2836_, 17 as u32);
                v_zetaHave_2854_ = leanh::lean_ctor_get_uint8(v___x_2836_, 18 as u32);
                v_isSharedCheck_2892_ = (!leanh::lean_is_exclusive(v___x_2836_)) as u8;
                if v_isSharedCheck_2892_ == 0 {
                    v___x_2856_ = v___x_2836_;
                    v_isShared_2857_ = v_isSharedCheck_2892_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v___x_2836_);
                    v___x_2856_ = leanh::lean_box(0);
                    v_isShared_2857_ = v_isSharedCheck_2892_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_trackZetaDelta_2858_ = leanh::lean_ctor_get_uint8(
                    v_a_2794_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_2859_ = leanh::lean_ctor_get(v_a_2794_, 1);
                v_lctx_2860_ = leanh::lean_ctor_get(v_a_2794_, 2);
                v_localInstances_2861_ = leanh::lean_ctor_get(v_a_2794_, 3);
                v_defEqCtx_x3f_2862_ = leanh::lean_ctor_get(v_a_2794_, 4);
                v_synthPendingDepth_2863_ = leanh::lean_ctor_get(v_a_2794_, 5);
                v_canUnfold_x3f_2864_ = leanh::lean_ctor_get(v_a_2794_, 6);
                v_univApprox_2865_ = leanh::lean_ctor_get_uint8(
                    v_a_2794_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_2866_ = leanh::lean_ctor_get_uint8(
                    v_a_2794_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_2867_ = leanh::lean_ctor_get_uint8(
                    v_a_2794_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                );
                v___x_2868_ = l_Lean_maxRecDepth;
                v___x_2869_ = l_Lean_Option_get___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__2(v___x_2818_, v___x_2868_);
                if v_isShared_2857_ == 0 {
                    v_config_2871_ = v___x_2856_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2891_ = leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2891_,
                        0 as u32,
                        v_foApprox_2837_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2891_,
                        1 as u32,
                        v_ctxApprox_2838_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2891_,
                        2 as u32,
                        v_quasiPatternApprox_2839_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2891_,
                        3 as u32,
                        v_constApprox_2840_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2891_,
                        4 as u32,
                        v_isDefEqStuckEx_2841_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2891_,
                        5 as u32,
                        v_unificationHints_2842_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2891_,
                        6 as u32,
                        v_proofIrrelevance_2843_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2891_,
                        7 as u32,
                        v_assignSyntheticOpaque_2844_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2891_,
                        8 as u32,
                        v_offsetCnstrs_2845_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2891_,
                        10 as u32,
                        v_etaStruct_2846_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2891_,
                        11 as u32,
                        v_univApprox_2847_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2891_,
                        12 as u32,
                        v_iota_2848_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2891_,
                        13 as u32,
                        v_beta_2849_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2891_,
                        14 as u32,
                        v_proj_2850_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2891_,
                        15 as u32,
                        v_zeta_2851_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2891_,
                        16 as u32,
                        v_zetaDelta_2852_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2891_,
                        17 as u32,
                        v_zetaUnused_2853_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2891_,
                        18 as u32,
                        v_zetaHave_2854_,
                    );
                    v_config_2871_ = v_reuseFailAlloc_2891_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                leanh::lean_ctor_set_uint8(v_config_2871_, 9 as u32, v___x_2815_);
                v___x_2872_ = l_Lean_Meta_Context_configKey(v_a_2794_);
                v___x_2873_ = 3u64;
                v___x_2874_ = lean_uint64_shift_right(v___x_2872_, v___x_2873_);
                leanh::lean_inc_ref(v_inheritedTraceOptions_2834_);
                leanh::lean_inc(v_cancelTk_x3f_2832_);
                leanh::lean_inc(v_currMacroScope_2831_);
                leanh::lean_inc(v_quotContext_2830_);
                leanh::lean_inc(v_maxHeartbeats_2829_);
                leanh::lean_inc(v_initHeartbeats_2828_);
                leanh::lean_inc(v_openDecls_2827_);
                leanh::lean_inc(v_currNamespace_2826_);
                leanh::lean_inc(v_ref_2825_);
                leanh::lean_inc(v_currRecDepth_2824_);
                leanh::lean_inc_ref(v_fileMap_2823_);
                leanh::lean_inc_ref(v_fileName_2822_);
                v___x_2875_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
                leanh::lean_ctor_set(v___x_2875_, 0, v_fileName_2822_);
                leanh::lean_ctor_set(v___x_2875_, 1, v_fileMap_2823_);
                leanh::lean_ctor_set(v___x_2875_, 2, v___x_2818_);
                leanh::lean_ctor_set(v___x_2875_, 3, v_currRecDepth_2824_);
                leanh::lean_ctor_set(v___x_2875_, 4, v___x_2869_);
                leanh::lean_ctor_set(v___x_2875_, 5, v_ref_2825_);
                leanh::lean_ctor_set(v___x_2875_, 6, v_currNamespace_2826_);
                leanh::lean_ctor_set(v___x_2875_, 7, v_openDecls_2827_);
                leanh::lean_ctor_set(v___x_2875_, 8, v_initHeartbeats_2828_);
                leanh::lean_ctor_set(v___x_2875_, 9, v_maxHeartbeats_2829_);
                leanh::lean_ctor_set(v___x_2875_, 10, v_quotContext_2830_);
                leanh::lean_ctor_set(v___x_2875_, 11, v_currMacroScope_2831_);
                leanh::lean_ctor_set(v___x_2875_, 12, v_cancelTk_x3f_2832_);
                leanh::lean_ctor_set(v___x_2875_, 13, v_inheritedTraceOptions_2834_);
                leanh::lean_ctor_set_uint8(
                    v___x_2875_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                    v___x_2820_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2875_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_2833_,
                );
                v___x_2876_ = lean_uint64_shift_left(v___x_2874_, v___x_2873_);
                v___x_2877_ = leanh::lean_uint64_once(
                    core::ptr::addr_of_mut!(
                        l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__0_once
                    ),
                    _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__0,
                );
                v_key_2878_ = lean_uint64_lor(v___x_2876_, v___x_2877_);
                v___x_2879_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                leanh::lean_ctor_set(v___x_2879_, 0, v_config_2871_);
                leanh::lean_ctor_set_uint64(
                    v___x_2879_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v_key_2878_,
                );
                leanh::lean_inc(v_canUnfold_x3f_2864_);
                leanh::lean_inc(v_synthPendingDepth_2863_);
                leanh::lean_inc(v_defEqCtx_x3f_2862_);
                leanh::lean_inc_ref(v_localInstances_2861_);
                leanh::lean_inc_ref(v_lctx_2860_);
                leanh::lean_inc(v_zetaDeltaSet_2859_);
                v___x_2880_ = leanh::lean_alloc_ctor(0, 7, (4) as u32);
                leanh::lean_ctor_set(v___x_2880_, 0, v___x_2879_);
                leanh::lean_ctor_set(v___x_2880_, 1, v_zetaDeltaSet_2859_);
                leanh::lean_ctor_set(v___x_2880_, 2, v_lctx_2860_);
                leanh::lean_ctor_set(v___x_2880_, 3, v_localInstances_2861_);
                leanh::lean_ctor_set(v___x_2880_, 4, v_defEqCtx_x3f_2862_);
                leanh::lean_ctor_set(v___x_2880_, 5, v_synthPendingDepth_2863_);
                leanh::lean_ctor_set(v___x_2880_, 6, v_canUnfold_x3f_2864_);
                leanh::lean_ctor_set_uint8(
                    v___x_2880_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_2858_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2880_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_2865_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2880_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_2866_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2880_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_2867_,
                );
                leanh::lean_inc_ref(v_e2_2793_);
                leanh::lean_inc_ref(v_e1_2792_);
                v___x_2881_ = l_Lean_Meta_isExprDefEq(
                    v_e1_2792_,
                    v_e2_2793_,
                    v___x_2880_,
                    v_a_2795_,
                    v___x_2875_,
                    v___y_2835_,
                );
                leanh::lean_dec_ref_known(v___x_2880_, 7);
                if leanh::lean_obj_tag(v___x_2881_) == 0 {
                    v_a_2882_ = leanh::lean_ctor_get(v___x_2881_, 0);
                    leanh::lean_inc(v_a_2882_);
                    v___x_2883_ = (leanh::lean_unbox(v_a_2882_) as u8);
                    leanh::lean_dec(v_a_2882_);
                    if v___x_2883_ == 0 {
                        leanh::lean_dec_ref_known(v___x_2881_, 1);
                        v___x_2884_ = 0;
                        v_config_2885_ = leanh::lean_alloc_ctor(0, 0, (19) as u32);
                        leanh::lean_ctor_set_uint8(
                            v_config_2885_,
                            0 as u32,
                            v_foApprox_2837_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v_config_2885_,
                            1 as u32,
                            v_ctxApprox_2838_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v_config_2885_,
                            2 as u32,
                            v_quasiPatternApprox_2839_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v_config_2885_,
                            3 as u32,
                            v_constApprox_2840_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v_config_2885_,
                            4 as u32,
                            v_isDefEqStuckEx_2841_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v_config_2885_,
                            5 as u32,
                            v_unificationHints_2842_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v_config_2885_,
                            6 as u32,
                            v_proofIrrelevance_2843_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v_config_2885_,
                            7 as u32,
                            v_assignSyntheticOpaque_2844_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v_config_2885_,
                            8 as u32,
                            v_offsetCnstrs_2845_,
                        );
                        leanh::lean_ctor_set_uint8(v_config_2885_, 9 as u32, v___x_2884_);
                        leanh::lean_ctor_set_uint8(
                            v_config_2885_,
                            10 as u32,
                            v_etaStruct_2846_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v_config_2885_,
                            11 as u32,
                            v_univApprox_2847_,
                        );
                        leanh::lean_ctor_set_uint8(v_config_2885_, 12 as u32, v_iota_2848_);
                        leanh::lean_ctor_set_uint8(v_config_2885_, 13 as u32, v_beta_2849_);
                        leanh::lean_ctor_set_uint8(v_config_2885_, 14 as u32, v_proj_2850_);
                        leanh::lean_ctor_set_uint8(v_config_2885_, 15 as u32, v_zeta_2851_);
                        leanh::lean_ctor_set_uint8(
                            v_config_2885_,
                            16 as u32,
                            v_zetaDelta_2852_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v_config_2885_,
                            17 as u32,
                            v_zetaUnused_2853_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v_config_2885_,
                            18 as u32,
                            v_zetaHave_2854_,
                        );
                        v___x_2886_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__1), core::ptr::addr_of_mut!(l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__1_once), _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__1);
                        v_key_2887_ = lean_uint64_lor(v___x_2876_, v___x_2886_);
                        v___x_2888_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                        leanh::lean_ctor_set(v___x_2888_, 0, v_config_2885_);
                        leanh::lean_ctor_set_uint64(
                            v___x_2888_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                            v_key_2887_,
                        );
                        leanh::lean_inc(v_canUnfold_x3f_2864_);
                        leanh::lean_inc(v_synthPendingDepth_2863_);
                        leanh::lean_inc(v_defEqCtx_x3f_2862_);
                        leanh::lean_inc_ref(v_localInstances_2861_);
                        leanh::lean_inc_ref(v_lctx_2860_);
                        leanh::lean_inc(v_zetaDeltaSet_2859_);
                        v___x_2889_ = leanh::lean_alloc_ctor(0, 7, (4) as u32);
                        leanh::lean_ctor_set(v___x_2889_, 0, v___x_2888_);
                        leanh::lean_ctor_set(v___x_2889_, 1, v_zetaDeltaSet_2859_);
                        leanh::lean_ctor_set(v___x_2889_, 2, v_lctx_2860_);
                        leanh::lean_ctor_set(v___x_2889_, 3, v_localInstances_2861_);
                        leanh::lean_ctor_set(v___x_2889_, 4, v_defEqCtx_x3f_2862_);
                        leanh::lean_ctor_set(v___x_2889_, 5, v_synthPendingDepth_2863_);
                        leanh::lean_ctor_set(v___x_2889_, 6, v_canUnfold_x3f_2864_);
                        leanh::lean_ctor_set_uint8(
                            v___x_2889_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                            v_trackZetaDelta_2858_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v___x_2889_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                            v_univApprox_2865_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v___x_2889_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                            v_inTypeClassResolution_2866_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v___x_2889_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                            v_cacheInferType_2867_,
                        );
                        v___x_2890_ = l_Lean_Meta_isExprDefEq(
                            v_e1_2792_,
                            v_e2_2793_,
                            v___x_2889_,
                            v_a_2795_,
                            v___x_2875_,
                            v___y_2835_,
                        );
                        leanh::lean_dec_ref_known(v___x_2875_, 14);
                        leanh::lean_dec_ref_known(v___x_2889_, 7);
                        return v___x_2890_;
                    } else {
                        leanh::lean_dec_ref_known(v___x_2875_, 14);
                        leanh::lean_dec_ref(v_e2_2793_);
                        leanh::lean_dec_ref(v_e1_2792_);
                        return v___x_2881_;
                    }
                } else {
                    leanh::lean_dec_ref_known(v___x_2875_, 14);
                    leanh::lean_dec_ref(v_e2_2793_);
                    leanh::lean_dec_ref(v_e1_2792_);
                    return v___x_2881_;
                }
            }
            4 => {
                if v___y_2894_ == 0 {
                    v___x_2895_ = lean_st_ref_take(v_a_2797_);
                    v_env_2896_ = leanh::lean_ctor_get(v___x_2895_, 0);
                    v_nextMacroScope_2897_ = leanh::lean_ctor_get(v___x_2895_, 1);
                    v_ngen_2898_ = leanh::lean_ctor_get(v___x_2895_, 2);
                    v_auxDeclNGen_2899_ = leanh::lean_ctor_get(v___x_2895_, 3);
                    v_traceState_2900_ = leanh::lean_ctor_get(v___x_2895_, 4);
                    v_messages_2901_ = leanh::lean_ctor_get(v___x_2895_, 6);
                    v_infoState_2902_ = leanh::lean_ctor_get(v___x_2895_, 7);
                    v_snapshotTasks_2903_ = leanh::lean_ctor_get(v___x_2895_, 8);
                    v_isSharedCheck_2913_ = (!leanh::lean_is_exclusive(v___x_2895_)) as u8;
                    if v_isSharedCheck_2913_ == 0 {
                        v_unused_2914_ = leanh::lean_ctor_get(v___x_2895_, 5);
                        leanh::lean_dec(v_unused_2914_);
                        v___x_2905_ = v___x_2895_;
                        v_isShared_2906_ = v_isSharedCheck_2913_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_snapshotTasks_2903_);
                        leanh::lean_inc(v_infoState_2902_);
                        leanh::lean_inc(v_messages_2901_);
                        leanh::lean_inc(v_traceState_2900_);
                        leanh::lean_inc(v_auxDeclNGen_2899_);
                        leanh::lean_inc(v_ngen_2898_);
                        leanh::lean_inc(v_nextMacroScope_2897_);
                        leanh::lean_inc(v_env_2896_);
                        leanh::lean_dec(v___x_2895_);
                        v___x_2905_ = leanh::lean_box(0);
                        v_isShared_2906_ = v_isSharedCheck_2913_;
                        state = 5;
                        continue;
                    }
                } else {
                    v_fileName_2822_ = v_fileName_2800_;
                    v_fileMap_2823_ = v_fileMap_2801_;
                    v_currRecDepth_2824_ = v_currRecDepth_2803_;
                    v_ref_2825_ = v_ref_2804_;
                    v_currNamespace_2826_ = v_currNamespace_2805_;
                    v_openDecls_2827_ = v_openDecls_2806_;
                    v_initHeartbeats_2828_ = v_initHeartbeats_2807_;
                    v_maxHeartbeats_2829_ = v_maxHeartbeats_2808_;
                    v_quotContext_2830_ = v_quotContext_2809_;
                    v_currMacroScope_2831_ = v_currMacroScope_2810_;
                    v_cancelTk_x3f_2832_ = v_cancelTk_x3f_2811_;
                    v_suppressElabErrors_2833_ = v_suppressElabErrors_2812_;
                    v_inheritedTraceOptions_2834_ = v_inheritedTraceOptions_2813_;
                    v___y_2835_ = v_a_2797_;
                    state = 1;
                    continue;
                }
            }
            5 => {
                v___x_2907_ = l_Lean_Kernel_enableDiag(v_env_2896_, v___x_2820_);
                v___x_2908_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__4
                    ),
                    core::ptr::addr_of_mut!(
                        l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__4_once
                    ),
                    _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__4,
                );
                if v_isShared_2906_ == 0 {
                    leanh::lean_ctor_set(v___x_2905_, 5, v___x_2908_);
                    leanh::lean_ctor_set(v___x_2905_, 0, v___x_2907_);
                    v___x_2910_ = v___x_2905_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2912_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2912_, 0, v___x_2907_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2912_, 1, v_nextMacroScope_2897_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2912_, 2, v_ngen_2898_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2912_, 3, v_auxDeclNGen_2899_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2912_, 4, v_traceState_2900_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2912_, 5, v___x_2908_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2912_, 6, v_messages_2901_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2912_, 7, v_infoState_2902_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2912_, 8, v_snapshotTasks_2903_);
                    v___x_2910_ = v_reuseFailAlloc_2912_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_2911_ = lean_st_ref_set(v_a_2797_, v___x_2910_);
                v_fileName_2822_ = v_fileName_2800_;
                v_fileMap_2823_ = v_fileMap_2801_;
                v_currRecDepth_2824_ = v_currRecDepth_2803_;
                v_ref_2825_ = v_ref_2804_;
                v_currNamespace_2826_ = v_currNamespace_2805_;
                v_openDecls_2827_ = v_openDecls_2806_;
                v_initHeartbeats_2828_ = v_initHeartbeats_2807_;
                v_maxHeartbeats_2829_ = v_maxHeartbeats_2808_;
                v_quotContext_2830_ = v_quotContext_2809_;
                v_currMacroScope_2831_ = v_currMacroScope_2810_;
                v_cancelTk_x3f_2832_ = v_cancelTk_x3f_2811_;
                v_suppressElabErrors_2833_ = v_suppressElabErrors_2812_;
                v_inheritedTraceOptions_2834_ = v_inheritedTraceOptions_2813_;
                v___y_2835_ = v_a_2797_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___boxed(
    mut v_e1_2916_: *mut leanh::LeanObject,
    mut v_e2_2917_: *mut leanh::LeanObject,
    mut v_a_2918_: *mut leanh::LeanObject,
    mut v_a_2919_: *mut leanh::LeanObject,
    mut v_a_2920_: *mut leanh::LeanObject,
    mut v_a_2921_: *mut leanh::LeanObject,
    mut v_a_2922_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2923_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2923_ = l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful(
        v_e1_2916_, v_e2_2917_, v_a_2918_, v_a_2919_, v_a_2920_, v_a_2921_,
    );
    leanh::lean_dec(v_a_2921_);
    leanh::lean_dec_ref(v_a_2920_);
    leanh::lean_dec(v_a_2919_);
    leanh::lean_dec_ref(v_a_2918_);
    return v_res_2923_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__1___redArg___lam__0(
    mut v_k_2924_: *mut leanh::LeanObject,
    mut v_b_2925_: *mut leanh::LeanObject,
    mut v_c_2926_: *mut leanh::LeanObject,
    mut v___y_2927_: *mut leanh::LeanObject,
    mut v___y_2928_: *mut leanh::LeanObject,
    mut v___y_2929_: *mut leanh::LeanObject,
    mut v___y_2930_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2932_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_2930_);
    leanh::lean_inc_ref(v___y_2929_);
    leanh::lean_inc(v___y_2928_);
    leanh::lean_inc_ref(v___y_2927_);
    v___x_2932_ = leanh::lean_apply_7(
        v_k_2924_,
        v_b_2925_,
        v_c_2926_,
        v___y_2927_,
        v___y_2928_,
        v___y_2929_,
        v___y_2930_,
        leanh::lean_box(0),
    );
    return v___x_2932_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__1___redArg___lam__0___boxed(
    mut v_k_2933_: *mut leanh::LeanObject,
    mut v_b_2934_: *mut leanh::LeanObject,
    mut v_c_2935_: *mut leanh::LeanObject,
    mut v___y_2936_: *mut leanh::LeanObject,
    mut v___y_2937_: *mut leanh::LeanObject,
    mut v___y_2938_: *mut leanh::LeanObject,
    mut v___y_2939_: *mut leanh::LeanObject,
    mut v___y_2940_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2941_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2941_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__1___redArg___lam__0(v_k_2933_, v_b_2934_, v_c_2935_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_);
    leanh::lean_dec(v___y_2939_);
    leanh::lean_dec_ref(v___y_2938_);
    leanh::lean_dec(v___y_2937_);
    leanh::lean_dec_ref(v___y_2936_);
    return v_res_2941_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__1___redArg(
    mut v_type_2942_: *mut leanh::LeanObject,
    mut v_k_2943_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_2944_: u8,
    mut v_whnfType_2945_: u8,
    mut v___y_2946_: *mut leanh::LeanObject,
    mut v___y_2947_: *mut leanh::LeanObject,
    mut v___y_2948_: *mut leanh::LeanObject,
    mut v___y_2949_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2956_: u8 = 0;
    let mut v___x_2958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2960_: u8 = 0;
    let mut v_a_2961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2964_: u8 = 0;
    let mut v___x_2966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2968_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_2951_ = leanh::lean_alloc_closure(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                leanh::lean_closure_set(v___f_2951_, 0, v_k_2943_);
                v___x_2952_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(
                    leanh::lean_box(0),
                    v_type_2942_,
                    v___f_2951_,
                    v_cleanupAnnotations_2944_,
                    v_whnfType_2945_,
                    v___y_2946_,
                    v___y_2947_,
                    v___y_2948_,
                    v___y_2949_,
                );
                if leanh::lean_obj_tag(v___x_2952_) == 0 {
                    v_a_2953_ = leanh::lean_ctor_get(v___x_2952_, 0);
                    v_isSharedCheck_2960_ = (!leanh::lean_is_exclusive(v___x_2952_)) as u8;
                    if v_isSharedCheck_2960_ == 0 {
                        v___x_2955_ = v___x_2952_;
                        v_isShared_2956_ = v_isSharedCheck_2960_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2953_);
                        leanh::lean_dec(v___x_2952_);
                        v___x_2955_ = leanh::lean_box(0);
                        v_isShared_2956_ = v_isSharedCheck_2960_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2961_ = leanh::lean_ctor_get(v___x_2952_, 0);
                    v_isSharedCheck_2968_ = (!leanh::lean_is_exclusive(v___x_2952_)) as u8;
                    if v_isSharedCheck_2968_ == 0 {
                        v___x_2963_ = v___x_2952_;
                        v_isShared_2964_ = v_isSharedCheck_2968_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2961_);
                        leanh::lean_dec(v___x_2952_);
                        v___x_2963_ = leanh::lean_box(0);
                        v_isShared_2964_ = v_isSharedCheck_2968_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2956_ == 0 {
                    v___x_2958_ = v___x_2955_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2959_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2959_, 0, v_a_2953_);
                    v___x_2958_ = v_reuseFailAlloc_2959_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2958_;
            }
            3 => {
                if v_isShared_2964_ == 0 {
                    v___x_2966_ = v___x_2963_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2967_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2967_, 0, v_a_2961_);
                    v___x_2966_ = v_reuseFailAlloc_2967_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2966_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__1___redArg___boxed(
    mut v_type_2969_: *mut leanh::LeanObject,
    mut v_k_2970_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_2971_: *mut leanh::LeanObject,
    mut v_whnfType_2972_: *mut leanh::LeanObject,
    mut v___y_2973_: *mut leanh::LeanObject,
    mut v___y_2974_: *mut leanh::LeanObject,
    mut v___y_2975_: *mut leanh::LeanObject,
    mut v___y_2976_: *mut leanh::LeanObject,
    mut v___y_2977_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_2978_: u8 = 0;
    let mut v_whnfType_boxed_2979_: u8 = 0;
    let mut v_res_2980_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_2978_ = (leanh::lean_unbox(v_cleanupAnnotations_2971_) as u8);
    v_whnfType_boxed_2979_ = (leanh::lean_unbox(v_whnfType_2972_) as u8);
    v_res_2980_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__1___redArg(v_type_2969_, v_k_2970_, v_cleanupAnnotations_boxed_2978_, v_whnfType_boxed_2979_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_);
    leanh::lean_dec(v___y_2976_);
    leanh::lean_dec_ref(v___y_2975_);
    leanh::lean_dec(v___y_2974_);
    leanh::lean_dec_ref(v___y_2973_);
    return v_res_2980_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__1(
    mut v_00_u03b1_2981_: *mut leanh::LeanObject,
    mut v_type_2982_: *mut leanh::LeanObject,
    mut v_k_2983_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_2984_: u8,
    mut v_whnfType_2985_: u8,
    mut v___y_2986_: *mut leanh::LeanObject,
    mut v___y_2987_: *mut leanh::LeanObject,
    mut v___y_2988_: *mut leanh::LeanObject,
    mut v___y_2989_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2991_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2991_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__1___redArg(v_type_2982_, v_k_2983_, v_cleanupAnnotations_2984_, v_whnfType_2985_, v___y_2986_, v___y_2987_, v___y_2988_, v___y_2989_);
    return v___x_2991_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__1___boxed(
    mut v_00_u03b1_2992_: *mut leanh::LeanObject,
    mut v_type_2993_: *mut leanh::LeanObject,
    mut v_k_2994_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_2995_: *mut leanh::LeanObject,
    mut v_whnfType_2996_: *mut leanh::LeanObject,
    mut v___y_2997_: *mut leanh::LeanObject,
    mut v___y_2998_: *mut leanh::LeanObject,
    mut v___y_2999_: *mut leanh::LeanObject,
    mut v___y_3000_: *mut leanh::LeanObject,
    mut v___y_3001_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_3002_: u8 = 0;
    let mut v_whnfType_boxed_3003_: u8 = 0;
    let mut v_res_3004_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_3002_ = (leanh::lean_unbox(v_cleanupAnnotations_2995_) as u8);
    v_whnfType_boxed_3003_ = (leanh::lean_unbox(v_whnfType_2996_) as u8);
    v_res_3004_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__1(v_00_u03b1_2992_, v_type_2993_, v_k_2994_, v_cleanupAnnotations_boxed_3002_, v_whnfType_boxed_3003_, v___y_2997_, v___y_2998_, v___y_2999_, v___y_3000_);
    leanh::lean_dec(v___y_3000_);
    leanh::lean_dec_ref(v___y_2999_);
    leanh::lean_dec(v___y_2998_);
    leanh::lean_dec_ref(v___y_2997_);
    return v_res_3004_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0_spec__0(
    mut v_msgData_3005_: *mut leanh::LeanObject,
    mut v___y_3006_: *mut leanh::LeanObject,
    mut v___y_3007_: *mut leanh::LeanObject,
    mut v___y_3008_: *mut leanh::LeanObject,
    mut v___y_3009_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3011_ = lean_st_ref_get(v___y_3009_);
    v_env_3012_ = leanh::lean_ctor_get(v___x_3011_, 0);
    leanh::lean_inc_ref(v_env_3012_);
    leanh::lean_dec(v___x_3011_);
    v___x_3013_ = lean_st_ref_get(v___y_3007_);
    v_mctx_3014_ = leanh::lean_ctor_get(v___x_3013_, 0);
    leanh::lean_inc_ref(v_mctx_3014_);
    leanh::lean_dec(v___x_3013_);
    v_lctx_3015_ = leanh::lean_ctor_get(v___y_3006_, 2);
    v_options_3016_ = leanh::lean_ctor_get(v___y_3008_, 2);
    leanh::lean_inc_ref(v_options_3016_);
    leanh::lean_inc_ref(v_lctx_3015_);
    v___x_3017_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_3017_, 0, v_env_3012_);
    leanh::lean_ctor_set(v___x_3017_, 1, v_mctx_3014_);
    leanh::lean_ctor_set(v___x_3017_, 2, v_lctx_3015_);
    leanh::lean_ctor_set(v___x_3017_, 3, v_options_3016_);
    v___x_3018_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3018_, 0, v___x_3017_);
    leanh::lean_ctor_set(v___x_3018_, 1, v_msgData_3005_);
    v___x_3019_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3019_, 0, v___x_3018_);
    return v___x_3019_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0_spec__0___boxed(
    mut v_msgData_3020_: *mut leanh::LeanObject,
    mut v___y_3021_: *mut leanh::LeanObject,
    mut v___y_3022_: *mut leanh::LeanObject,
    mut v___y_3023_: *mut leanh::LeanObject,
    mut v___y_3024_: *mut leanh::LeanObject,
    mut v___y_3025_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3026_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3026_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0_spec__0(v_msgData_3020_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_);
    leanh::lean_dec(v___y_3024_);
    leanh::lean_dec_ref(v___y_3023_);
    leanh::lean_dec(v___y_3022_);
    leanh::lean_dec_ref(v___y_3021_);
    return v_res_3026_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0___redArg(
    mut v_msg_3027_: *mut leanh::LeanObject,
    mut v___y_3028_: *mut leanh::LeanObject,
    mut v___y_3029_: *mut leanh::LeanObject,
    mut v___y_3030_: *mut leanh::LeanObject,
    mut v___y_3031_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_3033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3038_: u8 = 0;
    let mut v___x_3039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3043_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3033_ = leanh::lean_ctor_get(v___y_3030_, 5);
                v___x_3034_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0_spec__0(v_msg_3027_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_);
                v_a_3035_ = leanh::lean_ctor_get(v___x_3034_, 0);
                v_isSharedCheck_3043_ = (!leanh::lean_is_exclusive(v___x_3034_)) as u8;
                if v_isSharedCheck_3043_ == 0 {
                    v___x_3037_ = v___x_3034_;
                    v_isShared_3038_ = v_isSharedCheck_3043_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_3035_);
                    leanh::lean_dec(v___x_3034_);
                    v___x_3037_ = leanh::lean_box(0);
                    v_isShared_3038_ = v_isSharedCheck_3043_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_3033_);
                v___x_3039_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3039_, 0, v_ref_3033_);
                leanh::lean_ctor_set(v___x_3039_, 1, v_a_3035_);
                if v_isShared_3038_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3037_, 1);
                    leanh::lean_ctor_set(v___x_3037_, 0, v___x_3039_);
                    v___x_3041_ = v___x_3037_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3042_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3042_, 0, v___x_3039_);
                    v___x_3041_ = v_reuseFailAlloc_3042_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3041_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0___redArg___boxed(
    mut v_msg_3044_: *mut leanh::LeanObject,
    mut v___y_3045_: *mut leanh::LeanObject,
    mut v___y_3046_: *mut leanh::LeanObject,
    mut v___y_3047_: *mut leanh::LeanObject,
    mut v___y_3048_: *mut leanh::LeanObject,
    mut v___y_3049_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3050_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3050_ =
        l_Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0___redArg(
            v_msg_3044_,
            v___y_3045_,
            v___y_3046_,
            v___y_3047_,
            v___y_3048_,
        );
    leanh::lean_dec(v___y_3048_);
    leanh::lean_dec_ref(v___y_3047_);
    leanh::lean_dec(v___y_3046_);
    leanh::lean_dec_ref(v___y_3045_);
    return v_res_3050_;
}
pub unsafe fn _init_l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3055_ = l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0___closed__2;
    v___x_3056_ = l_Lean_stringToMessageData(v___x_3055_);
    return v___x_3056_;
}
pub unsafe fn l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0(
    mut v_k_3057_: *mut leanh::LeanObject,
    mut v_x_3058_: *mut leanh::LeanObject,
    mut v_type_3059_: *mut leanh::LeanObject,
    mut v___y_3060_: *mut leanh::LeanObject,
    mut v___y_3061_: *mut leanh::LeanObject,
    mut v___y_3062_: *mut leanh::LeanObject,
    mut v___y_3063_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: u8 = 0;
    let mut v___x_3070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3082_: u8 = 0;
    let mut v___x_3084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3086_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___y_3063_);
                leanh::lean_inc_ref(v___y_3062_);
                leanh::lean_inc(v___y_3061_);
                leanh::lean_inc_ref(v___y_3060_);
                v___x_3065_ = lean_whnf(
                    v_type_3059_,
                    v___y_3060_,
                    v___y_3061_,
                    v___y_3062_,
                    v___y_3063_,
                );
                if leanh::lean_obj_tag(v___x_3065_) == 0 {
                    v_a_3066_ = leanh::lean_ctor_get(v___x_3065_, 0);
                    leanh::lean_inc(v_a_3066_);
                    leanh::lean_dec_ref_known(v___x_3065_, 1);
                    v___x_3067_ = l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0___closed__1;
                    v___x_3068_ = leanh::lean_unsigned_to_nat(3);
                    v___x_3069_ = l_Lean_Expr_isAppOfArity(v_a_3066_, v___x_3067_, v___x_3068_);
                    if v___x_3069_ == 0 {
                        leanh::lean_dec_ref(v_k_3057_);
                        v___x_3070_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0___closed__3_once), _init_l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0___closed__3);
                        v___x_3071_ = leanh::lean_unsigned_to_nat(30);
                        v___x_3072_ = l_Lean_inlineExpr(v_a_3066_, v___x_3071_);
                        v___x_3073_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3073_, 0, v___x_3070_);
                        leanh::lean_ctor_set(v___x_3073_, 1, v___x_3072_);
                        v___x_3074_ = l_Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0___redArg(v___x_3073_, v___y_3060_, v___y_3061_, v___y_3062_, v___y_3063_);
                        return v___x_3074_;
                    } else {
                        v___x_3075_ = l_Lean_Expr_appFn_x21(v_a_3066_);
                        v___x_3076_ = l_Lean_Expr_appArg_x21(v___x_3075_);
                        leanh::lean_dec_ref(v___x_3075_);
                        v___x_3077_ = l_Lean_Expr_appArg_x21(v_a_3066_);
                        leanh::lean_dec(v_a_3066_);
                        leanh::lean_inc(v___y_3063_);
                        leanh::lean_inc_ref(v___y_3062_);
                        leanh::lean_inc(v___y_3061_);
                        leanh::lean_inc_ref(v___y_3060_);
                        v___x_3078_ = leanh::lean_apply_7(
                            v_k_3057_,
                            v___x_3076_,
                            v___x_3077_,
                            v___y_3060_,
                            v___y_3061_,
                            v___y_3062_,
                            v___y_3063_,
                            leanh::lean_box(0),
                        );
                        return v___x_3078_;
                    }
                } else {
                    leanh::lean_dec_ref(v_k_3057_);
                    v_a_3079_ = leanh::lean_ctor_get(v___x_3065_, 0);
                    v_isSharedCheck_3086_ = (!leanh::lean_is_exclusive(v___x_3065_)) as u8;
                    if v_isSharedCheck_3086_ == 0 {
                        v___x_3081_ = v___x_3065_;
                        v_isShared_3082_ = v_isSharedCheck_3086_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3079_);
                        leanh::lean_dec(v___x_3065_);
                        v___x_3081_ = leanh::lean_box(0);
                        v_isShared_3082_ = v_isSharedCheck_3086_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3082_ == 0 {
                    v___x_3084_ = v___x_3081_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3085_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3085_, 0, v_a_3079_);
                    v___x_3084_ = v_reuseFailAlloc_3085_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3084_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0___boxed(
    mut v_k_3087_: *mut leanh::LeanObject,
    mut v_x_3088_: *mut leanh::LeanObject,
    mut v_type_3089_: *mut leanh::LeanObject,
    mut v___y_3090_: *mut leanh::LeanObject,
    mut v___y_3091_: *mut leanh::LeanObject,
    mut v___y_3092_: *mut leanh::LeanObject,
    mut v___y_3093_: *mut leanh::LeanObject,
    mut v___y_3094_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3095_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3095_ = l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0(
        v_k_3087_,
        v_x_3088_,
        v_type_3089_,
        v___y_3090_,
        v___y_3091_,
        v___y_3092_,
        v___y_3093_,
    );
    leanh::lean_dec(v___y_3093_);
    leanh::lean_dec_ref(v___y_3092_);
    leanh::lean_dec(v___y_3091_);
    leanh::lean_dec_ref(v___y_3090_);
    leanh::lean_dec_ref(v_x_3088_);
    return v_res_3095_;
}
pub unsafe fn l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg(
    mut v_type_3096_: *mut leanh::LeanObject,
    mut v_k_3097_: *mut leanh::LeanObject,
    mut v_a_3098_: *mut leanh::LeanObject,
    mut v_a_3099_: *mut leanh::LeanObject,
    mut v_a_3100_: *mut leanh::LeanObject,
    mut v_a_3101_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_foApprox_3104_: u8 = 0;
    let mut v_ctxApprox_3105_: u8 = 0;
    let mut v_quasiPatternApprox_3106_: u8 = 0;
    let mut v_constApprox_3107_: u8 = 0;
    let mut v_isDefEqStuckEx_3108_: u8 = 0;
    let mut v_unificationHints_3109_: u8 = 0;
    let mut v_proofIrrelevance_3110_: u8 = 0;
    let mut v_assignSyntheticOpaque_3111_: u8 = 0;
    let mut v_offsetCnstrs_3112_: u8 = 0;
    let mut v_etaStruct_3113_: u8 = 0;
    let mut v_univApprox_3114_: u8 = 0;
    let mut v_iota_3115_: u8 = 0;
    let mut v_beta_3116_: u8 = 0;
    let mut v_proj_3117_: u8 = 0;
    let mut v_zeta_3118_: u8 = 0;
    let mut v_zetaDelta_3119_: u8 = 0;
    let mut v_zetaUnused_3120_: u8 = 0;
    let mut v_zetaHave_3121_: u8 = 0;
    let mut v___x_3123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3124_: u8 = 0;
    let mut v_trackZetaDelta_3125_: u8 = 0;
    let mut v_zetaDeltaSet_3126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_3128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_3129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_3130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_3131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_3132_: u8 = 0;
    let mut v_inTypeClassResolution_3133_: u8 = 0;
    let mut v_cacheInferType_3134_: u8 = 0;
    let mut v___x_3135_: u8 = 0;
    let mut v_config_3137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3138_: u64 = 0;
    let mut v___x_3139_: u64 = 0;
    let mut v___x_3140_: u64 = 0;
    let mut v___f_3141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3142_: u8 = 0;
    let mut v___x_3143_: u64 = 0;
    let mut v___x_3144_: u64 = 0;
    let mut v_key_3145_: u64 = 0;
    let mut v___x_3146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3150_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3103_ = l_Lean_Meta_Context_config(v_a_3098_);
                v_foApprox_3104_ = leanh::lean_ctor_get_uint8(v___x_3103_, 0 as u32);
                v_ctxApprox_3105_ = leanh::lean_ctor_get_uint8(v___x_3103_, 1 as u32);
                v_quasiPatternApprox_3106_ =
                    leanh::lean_ctor_get_uint8(v___x_3103_, 2 as u32);
                v_constApprox_3107_ = leanh::lean_ctor_get_uint8(v___x_3103_, 3 as u32);
                v_isDefEqStuckEx_3108_ = leanh::lean_ctor_get_uint8(v___x_3103_, 4 as u32);
                v_unificationHints_3109_ = leanh::lean_ctor_get_uint8(v___x_3103_, 5 as u32);
                v_proofIrrelevance_3110_ = leanh::lean_ctor_get_uint8(v___x_3103_, 6 as u32);
                v_assignSyntheticOpaque_3111_ =
                    leanh::lean_ctor_get_uint8(v___x_3103_, 7 as u32);
                v_offsetCnstrs_3112_ = leanh::lean_ctor_get_uint8(v___x_3103_, 8 as u32);
                v_etaStruct_3113_ = leanh::lean_ctor_get_uint8(v___x_3103_, 10 as u32);
                v_univApprox_3114_ = leanh::lean_ctor_get_uint8(v___x_3103_, 11 as u32);
                v_iota_3115_ = leanh::lean_ctor_get_uint8(v___x_3103_, 12 as u32);
                v_beta_3116_ = leanh::lean_ctor_get_uint8(v___x_3103_, 13 as u32);
                v_proj_3117_ = leanh::lean_ctor_get_uint8(v___x_3103_, 14 as u32);
                v_zeta_3118_ = leanh::lean_ctor_get_uint8(v___x_3103_, 15 as u32);
                v_zetaDelta_3119_ = leanh::lean_ctor_get_uint8(v___x_3103_, 16 as u32);
                v_zetaUnused_3120_ = leanh::lean_ctor_get_uint8(v___x_3103_, 17 as u32);
                v_zetaHave_3121_ = leanh::lean_ctor_get_uint8(v___x_3103_, 18 as u32);
                v_isSharedCheck_3150_ = (!leanh::lean_is_exclusive(v___x_3103_)) as u8;
                if v_isSharedCheck_3150_ == 0 {
                    v___x_3123_ = v___x_3103_;
                    v_isShared_3124_ = v_isSharedCheck_3150_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v___x_3103_);
                    v___x_3123_ = leanh::lean_box(0);
                    v_isShared_3124_ = v_isSharedCheck_3150_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_trackZetaDelta_3125_ = leanh::lean_ctor_get_uint8(
                    v_a_3098_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_3126_ = leanh::lean_ctor_get(v_a_3098_, 1);
                v_lctx_3127_ = leanh::lean_ctor_get(v_a_3098_, 2);
                v_localInstances_3128_ = leanh::lean_ctor_get(v_a_3098_, 3);
                v_defEqCtx_x3f_3129_ = leanh::lean_ctor_get(v_a_3098_, 4);
                v_synthPendingDepth_3130_ = leanh::lean_ctor_get(v_a_3098_, 5);
                v_canUnfold_x3f_3131_ = leanh::lean_ctor_get(v_a_3098_, 6);
                v_univApprox_3132_ = leanh::lean_ctor_get_uint8(
                    v_a_3098_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_3133_ = leanh::lean_ctor_get_uint8(
                    v_a_3098_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_3134_ = leanh::lean_ctor_get_uint8(
                    v_a_3098_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                );
                v___x_3135_ = 0;
                if v_isShared_3124_ == 0 {
                    v_config_3137_ = v___x_3123_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3149_ = leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3149_,
                        0 as u32,
                        v_foApprox_3104_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3149_,
                        1 as u32,
                        v_ctxApprox_3105_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3149_,
                        2 as u32,
                        v_quasiPatternApprox_3106_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3149_,
                        3 as u32,
                        v_constApprox_3107_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3149_,
                        4 as u32,
                        v_isDefEqStuckEx_3108_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3149_,
                        5 as u32,
                        v_unificationHints_3109_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3149_,
                        6 as u32,
                        v_proofIrrelevance_3110_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3149_,
                        7 as u32,
                        v_assignSyntheticOpaque_3111_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3149_,
                        8 as u32,
                        v_offsetCnstrs_3112_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3149_,
                        10 as u32,
                        v_etaStruct_3113_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3149_,
                        11 as u32,
                        v_univApprox_3114_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3149_,
                        12 as u32,
                        v_iota_3115_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3149_,
                        13 as u32,
                        v_beta_3116_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3149_,
                        14 as u32,
                        v_proj_3117_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3149_,
                        15 as u32,
                        v_zeta_3118_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3149_,
                        16 as u32,
                        v_zetaDelta_3119_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3149_,
                        17 as u32,
                        v_zetaUnused_3120_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3149_,
                        18 as u32,
                        v_zetaHave_3121_,
                    );
                    v_config_3137_ = v_reuseFailAlloc_3149_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_ctor_set_uint8(v_config_3137_, 9 as u32, v___x_3135_);
                v___x_3138_ = l_Lean_Meta_Context_configKey(v_a_3098_);
                v___x_3139_ = 3u64;
                v___x_3140_ = lean_uint64_shift_right(v___x_3138_, v___x_3139_);
                v___f_3141_ = leanh::lean_alloc_closure(
                    l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    8,
                    1,
                );
                leanh::lean_closure_set(v___f_3141_, 0, v_k_3097_);
                v___x_3142_ = 0;
                v___x_3143_ = lean_uint64_shift_left(v___x_3140_, v___x_3139_);
                v___x_3144_ = leanh::lean_uint64_once(
                    core::ptr::addr_of_mut!(
                        l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__1_once
                    ),
                    _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__1,
                );
                v_key_3145_ = lean_uint64_lor(v___x_3143_, v___x_3144_);
                v___x_3146_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                leanh::lean_ctor_set(v___x_3146_, 0, v_config_3137_);
                leanh::lean_ctor_set_uint64(
                    v___x_3146_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v_key_3145_,
                );
                leanh::lean_inc(v_canUnfold_x3f_3131_);
                leanh::lean_inc(v_synthPendingDepth_3130_);
                leanh::lean_inc(v_defEqCtx_x3f_3129_);
                leanh::lean_inc_ref(v_localInstances_3128_);
                leanh::lean_inc_ref(v_lctx_3127_);
                leanh::lean_inc(v_zetaDeltaSet_3126_);
                v___x_3147_ = leanh::lean_alloc_ctor(0, 7, (4) as u32);
                leanh::lean_ctor_set(v___x_3147_, 0, v___x_3146_);
                leanh::lean_ctor_set(v___x_3147_, 1, v_zetaDeltaSet_3126_);
                leanh::lean_ctor_set(v___x_3147_, 2, v_lctx_3127_);
                leanh::lean_ctor_set(v___x_3147_, 3, v_localInstances_3128_);
                leanh::lean_ctor_set(v___x_3147_, 4, v_defEqCtx_x3f_3129_);
                leanh::lean_ctor_set(v___x_3147_, 5, v_synthPendingDepth_3130_);
                leanh::lean_ctor_set(v___x_3147_, 6, v_canUnfold_x3f_3131_);
                leanh::lean_ctor_set_uint8(
                    v___x_3147_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_3125_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_3147_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_3132_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_3147_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_3133_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_3147_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_3134_,
                );
                v___x_3148_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__1___redArg(v_type_3096_, v___f_3141_, v___x_3142_, v___x_3142_, v___x_3147_, v_a_3099_, v_a_3100_, v_a_3101_);
                leanh::lean_dec_ref_known(v___x_3147_, 7);
                return v___x_3148_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___boxed(
    mut v_type_3151_: *mut leanh::LeanObject,
    mut v_k_3152_: *mut leanh::LeanObject,
    mut v_a_3153_: *mut leanh::LeanObject,
    mut v_a_3154_: *mut leanh::LeanObject,
    mut v_a_3155_: *mut leanh::LeanObject,
    mut v_a_3156_: *mut leanh::LeanObject,
    mut v_a_3157_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3158_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3158_ = l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg(
        v_type_3151_,
        v_k_3152_,
        v_a_3153_,
        v_a_3154_,
        v_a_3155_,
        v_a_3156_,
    );
    leanh::lean_dec(v_a_3156_);
    leanh::lean_dec_ref(v_a_3155_);
    leanh::lean_dec(v_a_3154_);
    leanh::lean_dec_ref(v_a_3153_);
    return v_res_3158_;
}
pub unsafe fn l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs(
    mut v_00_u03b1_3159_: *mut leanh::LeanObject,
    mut v_type_3160_: *mut leanh::LeanObject,
    mut v_k_3161_: *mut leanh::LeanObject,
    mut v_a_3162_: *mut leanh::LeanObject,
    mut v_a_3163_: *mut leanh::LeanObject,
    mut v_a_3164_: *mut leanh::LeanObject,
    mut v_a_3165_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3167_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3167_ = l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg(
        v_type_3160_,
        v_k_3161_,
        v_a_3162_,
        v_a_3163_,
        v_a_3164_,
        v_a_3165_,
    );
    return v___x_3167_;
}
pub unsafe fn l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___boxed(
    mut v_00_u03b1_3168_: *mut leanh::LeanObject,
    mut v_type_3169_: *mut leanh::LeanObject,
    mut v_k_3170_: *mut leanh::LeanObject,
    mut v_a_3171_: *mut leanh::LeanObject,
    mut v_a_3172_: *mut leanh::LeanObject,
    mut v_a_3173_: *mut leanh::LeanObject,
    mut v_a_3174_: *mut leanh::LeanObject,
    mut v_a_3175_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3176_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3176_ = l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs(
        v_00_u03b1_3168_,
        v_type_3169_,
        v_k_3170_,
        v_a_3171_,
        v_a_3172_,
        v_a_3173_,
        v_a_3174_,
    );
    leanh::lean_dec(v_a_3174_);
    leanh::lean_dec_ref(v_a_3173_);
    leanh::lean_dec(v_a_3172_);
    leanh::lean_dec_ref(v_a_3171_);
    return v_res_3176_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0(
    mut v_00_u03b1_3177_: *mut leanh::LeanObject,
    mut v_msg_3178_: *mut leanh::LeanObject,
    mut v___y_3179_: *mut leanh::LeanObject,
    mut v___y_3180_: *mut leanh::LeanObject,
    mut v___y_3181_: *mut leanh::LeanObject,
    mut v___y_3182_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3184_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3184_ =
        l_Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0___redArg(
            v_msg_3178_,
            v___y_3179_,
            v___y_3180_,
            v___y_3181_,
            v___y_3182_,
        );
    return v___x_3184_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0___boxed(
    mut v_00_u03b1_3185_: *mut leanh::LeanObject,
    mut v_msg_3186_: *mut leanh::LeanObject,
    mut v___y_3187_: *mut leanh::LeanObject,
    mut v___y_3188_: *mut leanh::LeanObject,
    mut v___y_3189_: *mut leanh::LeanObject,
    mut v___y_3190_: *mut leanh::LeanObject,
    mut v___y_3191_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3192_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3192_ =
        l_Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0(
            v_00_u03b1_3185_,
            v_msg_3186_,
            v___y_3187_,
            v___y_3188_,
            v___y_3189_,
            v___y_3190_,
        );
    leanh::lean_dec(v___y_3190_);
    leanh::lean_dec_ref(v___y_3189_);
    leanh::lean_dec(v___y_3188_);
    leanh::lean_dec_ref(v___y_3187_);
    return v_res_3192_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___lam__0(
    mut v___y_3193_: *mut leanh::LeanObject,
    mut v_isExporting_3194_: u8,
    mut v___x_3195_: *mut leanh::LeanObject,
    mut v___y_3196_: *mut leanh::LeanObject,
    mut v___x_3197_: *mut leanh::LeanObject,
    mut v_a_x3f_3198_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3211_: u8 = 0;
    let mut v___x_3212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_3219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3223_: u8 = 0;
    let mut v___x_3225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3230_: u8 = 0;
    let mut v_unused_3231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3233_: u8 = 0;
    let mut v_unused_3234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3200_ = lean_st_ref_take(v___y_3193_);
                v_env_3201_ = leanh::lean_ctor_get(v___x_3200_, 0);
                v_nextMacroScope_3202_ = leanh::lean_ctor_get(v___x_3200_, 1);
                v_ngen_3203_ = leanh::lean_ctor_get(v___x_3200_, 2);
                v_auxDeclNGen_3204_ = leanh::lean_ctor_get(v___x_3200_, 3);
                v_traceState_3205_ = leanh::lean_ctor_get(v___x_3200_, 4);
                v_messages_3206_ = leanh::lean_ctor_get(v___x_3200_, 6);
                v_infoState_3207_ = leanh::lean_ctor_get(v___x_3200_, 7);
                v_snapshotTasks_3208_ = leanh::lean_ctor_get(v___x_3200_, 8);
                v_isSharedCheck_3233_ = (!leanh::lean_is_exclusive(v___x_3200_)) as u8;
                if v_isSharedCheck_3233_ == 0 {
                    v_unused_3234_ = leanh::lean_ctor_get(v___x_3200_, 5);
                    leanh::lean_dec(v_unused_3234_);
                    v___x_3210_ = v___x_3200_;
                    v_isShared_3211_ = v_isSharedCheck_3233_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_3208_);
                    leanh::lean_inc(v_infoState_3207_);
                    leanh::lean_inc(v_messages_3206_);
                    leanh::lean_inc(v_traceState_3205_);
                    leanh::lean_inc(v_auxDeclNGen_3204_);
                    leanh::lean_inc(v_ngen_3203_);
                    leanh::lean_inc(v_nextMacroScope_3202_);
                    leanh::lean_inc(v_env_3201_);
                    leanh::lean_dec(v___x_3200_);
                    v___x_3210_ = leanh::lean_box(0);
                    v_isShared_3211_ = v_isSharedCheck_3233_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3212_ = l_Lean_Environment_setExporting(v_env_3201_, v_isExporting_3194_);
                if v_isShared_3211_ == 0 {
                    leanh::lean_ctor_set(v___x_3210_, 5, v___x_3195_);
                    leanh::lean_ctor_set(v___x_3210_, 0, v___x_3212_);
                    v___x_3214_ = v___x_3210_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3232_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3232_, 0, v___x_3212_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3232_, 1, v_nextMacroScope_3202_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3232_, 2, v_ngen_3203_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3232_, 3, v_auxDeclNGen_3204_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3232_, 4, v_traceState_3205_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3232_, 5, v___x_3195_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3232_, 6, v_messages_3206_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3232_, 7, v_infoState_3207_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3232_, 8, v_snapshotTasks_3208_);
                    v___x_3214_ = v_reuseFailAlloc_3232_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3215_ = lean_st_ref_set(v___y_3193_, v___x_3214_);
                v___x_3216_ = lean_st_ref_take(v___y_3196_);
                v_mctx_3217_ = leanh::lean_ctor_get(v___x_3216_, 0);
                v_zetaDeltaFVarIds_3218_ = leanh::lean_ctor_get(v___x_3216_, 2);
                v_postponed_3219_ = leanh::lean_ctor_get(v___x_3216_, 3);
                v_diag_3220_ = leanh::lean_ctor_get(v___x_3216_, 4);
                v_isSharedCheck_3230_ = (!leanh::lean_is_exclusive(v___x_3216_)) as u8;
                if v_isSharedCheck_3230_ == 0 {
                    v_unused_3231_ = leanh::lean_ctor_get(v___x_3216_, 1);
                    leanh::lean_dec(v_unused_3231_);
                    v___x_3222_ = v___x_3216_;
                    v_isShared_3223_ = v_isSharedCheck_3230_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_3220_);
                    leanh::lean_inc(v_postponed_3219_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_3218_);
                    leanh::lean_inc(v_mctx_3217_);
                    leanh::lean_dec(v___x_3216_);
                    v___x_3222_ = leanh::lean_box(0);
                    v_isShared_3223_ = v_isSharedCheck_3230_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3223_ == 0 {
                    leanh::lean_ctor_set(v___x_3222_, 1, v___x_3197_);
                    v___x_3225_ = v___x_3222_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3229_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3229_, 0, v_mctx_3217_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3229_, 1, v___x_3197_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3229_,
                        2,
                        v_zetaDeltaFVarIds_3218_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3229_, 3, v_postponed_3219_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3229_, 4, v_diag_3220_);
                    v___x_3225_ = v_reuseFailAlloc_3229_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3226_ = lean_st_ref_set(v___y_3196_, v___x_3225_);
                v___x_3227_ = leanh::lean_box(0);
                v___x_3228_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3228_, 0, v___x_3227_);
                return v___x_3228_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___lam__0___boxed(
    mut v___y_3235_: *mut leanh::LeanObject,
    mut v_isExporting_3236_: *mut leanh::LeanObject,
    mut v___x_3237_: *mut leanh::LeanObject,
    mut v___y_3238_: *mut leanh::LeanObject,
    mut v___x_3239_: *mut leanh::LeanObject,
    mut v_a_x3f_3240_: *mut leanh::LeanObject,
    mut v___y_3241_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isExporting_boxed_3242_: u8 = 0;
    let mut v_res_3243_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_3242_ = (leanh::lean_unbox(v_isExporting_3236_) as u8);
    v_res_3243_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___lam__0(v___y_3235_, v_isExporting_boxed_3242_, v___x_3237_, v___y_3238_, v___x_3239_, v_a_x3f_3240_);
    leanh::lean_dec(v_a_x3f_3240_);
    leanh::lean_dec(v___y_3238_);
    leanh::lean_dec(v___y_3235_);
    return v_res_3243_;
}
pub unsafe fn _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3244_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__3),
        core::ptr::addr_of_mut!(
            l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__3_once
        ),
        _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__3,
    );
    v___x_3245_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
    leanh::lean_ctor_set(v___x_3245_, 0, v___x_3244_);
    leanh::lean_ctor_set(v___x_3245_, 1, v___x_3244_);
    leanh::lean_ctor_set(v___x_3245_, 2, v___x_3244_);
    leanh::lean_ctor_set(v___x_3245_, 3, v___x_3244_);
    leanh::lean_ctor_set(v___x_3245_, 4, v___x_3244_);
    leanh::lean_ctor_set(v___x_3245_, 5, v___x_3244_);
    return v___x_3245_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg(
    mut v_x_3246_: *mut leanh::LeanObject,
    mut v_isExporting_3247_: u8,
    mut v___y_3248_: *mut leanh::LeanObject,
    mut v___y_3249_: *mut leanh::LeanObject,
    mut v___y_3250_: *mut leanh::LeanObject,
    mut v___y_3251_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isExporting_3255_: u8 = 0;
    let mut v___x_3256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3267_: u8 = 0;
    let mut v___x_3268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_3276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3280_: u8 = 0;
    let mut v___x_3281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3289_: u8 = 0;
    let mut v___x_3291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3295_: u8 = 0;
    let mut v___x_3297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3299_: u8 = 0;
    let mut v_unused_3300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3302_: u8 = 0;
    let mut v_a_3303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3308_: u8 = 0;
    let mut v___x_3310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3312_: u8 = 0;
    let mut v_unused_3313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3315_: u8 = 0;
    let mut v_unused_3316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3318_: u8 = 0;
    let mut v_unused_3319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3253_ = lean_st_ref_get(v___y_3251_);
                v_env_3254_ = leanh::lean_ctor_get(v___x_3253_, 0);
                leanh::lean_inc_ref(v_env_3254_);
                leanh::lean_dec(v___x_3253_);
                v_isExporting_3255_ = leanh::lean_ctor_get_uint8(
                    v_env_3254_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                );
                leanh::lean_dec_ref(v_env_3254_);
                v___x_3256_ = lean_st_ref_take(v___y_3251_);
                v_env_3257_ = leanh::lean_ctor_get(v___x_3256_, 0);
                v_nextMacroScope_3258_ = leanh::lean_ctor_get(v___x_3256_, 1);
                v_ngen_3259_ = leanh::lean_ctor_get(v___x_3256_, 2);
                v_auxDeclNGen_3260_ = leanh::lean_ctor_get(v___x_3256_, 3);
                v_traceState_3261_ = leanh::lean_ctor_get(v___x_3256_, 4);
                v_messages_3262_ = leanh::lean_ctor_get(v___x_3256_, 6);
                v_infoState_3263_ = leanh::lean_ctor_get(v___x_3256_, 7);
                v_snapshotTasks_3264_ = leanh::lean_ctor_get(v___x_3256_, 8);
                v_isSharedCheck_3318_ = (!leanh::lean_is_exclusive(v___x_3256_)) as u8;
                if v_isSharedCheck_3318_ == 0 {
                    v_unused_3319_ = leanh::lean_ctor_get(v___x_3256_, 5);
                    leanh::lean_dec(v_unused_3319_);
                    v___x_3266_ = v___x_3256_;
                    v_isShared_3267_ = v_isSharedCheck_3318_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_3264_);
                    leanh::lean_inc(v_infoState_3263_);
                    leanh::lean_inc(v_messages_3262_);
                    leanh::lean_inc(v_traceState_3261_);
                    leanh::lean_inc(v_auxDeclNGen_3260_);
                    leanh::lean_inc(v_ngen_3259_);
                    leanh::lean_inc(v_nextMacroScope_3258_);
                    leanh::lean_inc(v_env_3257_);
                    leanh::lean_dec(v___x_3256_);
                    v___x_3266_ = leanh::lean_box(0);
                    v_isShared_3267_ = v_isSharedCheck_3318_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3268_ = l_Lean_Environment_setExporting(v_env_3257_, v_isExporting_3247_);
                v___x_3269_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__4
                    ),
                    core::ptr::addr_of_mut!(
                        l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__4_once
                    ),
                    _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__4,
                );
                if v_isShared_3267_ == 0 {
                    leanh::lean_ctor_set(v___x_3266_, 5, v___x_3269_);
                    leanh::lean_ctor_set(v___x_3266_, 0, v___x_3268_);
                    v___x_3271_ = v___x_3266_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3317_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3317_, 0, v___x_3268_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3317_, 1, v_nextMacroScope_3258_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3317_, 2, v_ngen_3259_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3317_, 3, v_auxDeclNGen_3260_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3317_, 4, v_traceState_3261_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3317_, 5, v___x_3269_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3317_, 6, v_messages_3262_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3317_, 7, v_infoState_3263_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3317_, 8, v_snapshotTasks_3264_);
                    v___x_3271_ = v_reuseFailAlloc_3317_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3272_ = lean_st_ref_set(v___y_3251_, v___x_3271_);
                v___x_3273_ = lean_st_ref_take(v___y_3249_);
                v_mctx_3274_ = leanh::lean_ctor_get(v___x_3273_, 0);
                v_zetaDeltaFVarIds_3275_ = leanh::lean_ctor_get(v___x_3273_, 2);
                v_postponed_3276_ = leanh::lean_ctor_get(v___x_3273_, 3);
                v_diag_3277_ = leanh::lean_ctor_get(v___x_3273_, 4);
                v_isSharedCheck_3315_ = (!leanh::lean_is_exclusive(v___x_3273_)) as u8;
                if v_isSharedCheck_3315_ == 0 {
                    v_unused_3316_ = leanh::lean_ctor_get(v___x_3273_, 1);
                    leanh::lean_dec(v_unused_3316_);
                    v___x_3279_ = v___x_3273_;
                    v_isShared_3280_ = v_isSharedCheck_3315_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_3277_);
                    leanh::lean_inc(v_postponed_3276_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_3275_);
                    leanh::lean_inc(v_mctx_3274_);
                    leanh::lean_dec(v___x_3273_);
                    v___x_3279_ = leanh::lean_box(0);
                    v_isShared_3280_ = v_isSharedCheck_3315_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3281_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___closed__0);
                if v_isShared_3280_ == 0 {
                    leanh::lean_ctor_set(v___x_3279_, 1, v___x_3281_);
                    v___x_3283_ = v___x_3279_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3314_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3314_, 0, v_mctx_3274_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3314_, 1, v___x_3281_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3314_,
                        2,
                        v_zetaDeltaFVarIds_3275_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3314_, 3, v_postponed_3276_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3314_, 4, v_diag_3277_);
                    v___x_3283_ = v_reuseFailAlloc_3314_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3284_ = lean_st_ref_set(v___y_3249_, v___x_3283_);
                leanh::lean_inc(v___y_3251_);
                leanh::lean_inc_ref(v___y_3250_);
                leanh::lean_inc(v___y_3249_);
                leanh::lean_inc_ref(v___y_3248_);
                v_r_3285_ = leanh::lean_apply_5(
                    v_x_3246_,
                    v___y_3248_,
                    v___y_3249_,
                    v___y_3250_,
                    v___y_3251_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v_r_3285_) == 0 {
                    v_a_3286_ = leanh::lean_ctor_get(v_r_3285_, 0);
                    v_isSharedCheck_3302_ = (!leanh::lean_is_exclusive(v_r_3285_)) as u8;
                    if v_isSharedCheck_3302_ == 0 {
                        v___x_3288_ = v_r_3285_;
                        v_isShared_3289_ = v_isSharedCheck_3302_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3286_);
                        leanh::lean_dec(v_r_3285_);
                        v___x_3288_ = leanh::lean_box(0);
                        v_isShared_3289_ = v_isSharedCheck_3302_;
                        state = 5;
                        continue;
                    }
                } else {
                    v_a_3303_ = leanh::lean_ctor_get(v_r_3285_, 0);
                    leanh::lean_inc(v_a_3303_);
                    leanh::lean_dec_ref_known(v_r_3285_, 1);
                    v___x_3304_ = leanh::lean_box(0);
                    v___x_3305_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___lam__0(v___y_3251_, v_isExporting_3255_, v___x_3269_, v___y_3249_, v___x_3281_, v___x_3304_);
                    v_isSharedCheck_3312_ = (!leanh::lean_is_exclusive(v___x_3305_)) as u8;
                    if v_isSharedCheck_3312_ == 0 {
                        v_unused_3313_ = leanh::lean_ctor_get(v___x_3305_, 0);
                        leanh::lean_dec(v_unused_3313_);
                        v___x_3307_ = v___x_3305_;
                        v_isShared_3308_ = v_isSharedCheck_3312_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_3305_);
                        v___x_3307_ = leanh::lean_box(0);
                        v_isShared_3308_ = v_isSharedCheck_3312_;
                        state = 9;
                        continue;
                    }
                }
            }
            5 => {
                leanh::lean_inc(v_a_3286_);
                if v_isShared_3289_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3288_, 1);
                    v___x_3291_ = v___x_3288_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3301_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3301_, 0, v_a_3286_);
                    v___x_3291_ = v_reuseFailAlloc_3301_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_3292_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___lam__0(v___y_3251_, v_isExporting_3255_, v___x_3269_, v___y_3249_, v___x_3281_, v___x_3291_);
                leanh::lean_dec_ref(v___x_3291_);
                v_isSharedCheck_3299_ = (!leanh::lean_is_exclusive(v___x_3292_)) as u8;
                if v_isSharedCheck_3299_ == 0 {
                    v_unused_3300_ = leanh::lean_ctor_get(v___x_3292_, 0);
                    leanh::lean_dec(v_unused_3300_);
                    v___x_3294_ = v___x_3292_;
                    v_isShared_3295_ = v_isSharedCheck_3299_;
                    state = 7;
                    continue;
                } else {
                    leanh::lean_dec(v___x_3292_);
                    v___x_3294_ = leanh::lean_box(0);
                    v_isShared_3295_ = v_isSharedCheck_3299_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_3295_ == 0 {
                    leanh::lean_ctor_set(v___x_3294_, 0, v_a_3286_);
                    v___x_3297_ = v___x_3294_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3298_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3298_, 0, v_a_3286_);
                    v___x_3297_ = v_reuseFailAlloc_3298_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3297_;
            }
            9 => {
                if v_isShared_3308_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3307_, 1);
                    leanh::lean_ctor_set(v___x_3307_, 0, v_a_3303_);
                    v___x_3310_ = v___x_3307_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3311_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3311_, 0, v_a_3303_);
                    v___x_3310_ = v_reuseFailAlloc_3311_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3310_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___boxed(
    mut v_x_3320_: *mut leanh::LeanObject,
    mut v_isExporting_3321_: *mut leanh::LeanObject,
    mut v___y_3322_: *mut leanh::LeanObject,
    mut v___y_3323_: *mut leanh::LeanObject,
    mut v___y_3324_: *mut leanh::LeanObject,
    mut v___y_3325_: *mut leanh::LeanObject,
    mut v___y_3326_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isExporting_boxed_3327_: u8 = 0;
    let mut v_res_3328_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_3327_ = (leanh::lean_unbox(v_isExporting_3321_) as u8);
    v_res_3328_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg(v_x_3320_, v_isExporting_boxed_3327_, v___y_3322_, v___y_3323_, v___y_3324_, v___y_3325_);
    leanh::lean_dec(v___y_3325_);
    leanh::lean_dec_ref(v___y_3324_);
    leanh::lean_dec(v___y_3323_);
    leanh::lean_dec_ref(v___y_3322_);
    return v_res_3328_;
}
pub unsafe fn l_Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0___redArg(
    mut v_x_3329_: *mut leanh::LeanObject,
    mut v_when_3330_: u8,
    mut v___y_3331_: *mut leanh::LeanObject,
    mut v___y_3332_: *mut leanh::LeanObject,
    mut v___y_3333_: *mut leanh::LeanObject,
    mut v___y_3334_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_when_3330_ == 0 {
        let mut v___x_3336_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc(v___y_3334_);
        leanh::lean_inc_ref(v___y_3333_);
        leanh::lean_inc(v___y_3332_);
        leanh::lean_inc_ref(v___y_3331_);
        v___x_3336_ = leanh::lean_apply_5(
            v_x_3329_,
            v___y_3331_,
            v___y_3332_,
            v___y_3333_,
            v___y_3334_,
            leanh::lean_box(0),
        );
        return v___x_3336_;
    } else {
        let mut v___x_3337_: u8 = 0;
        let mut v___x_3338_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3337_ = 0;
        v___x_3338_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg(v_x_3329_, v___x_3337_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_);
        return v___x_3338_;
    }
}
pub unsafe fn l_Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0___redArg___boxed(
    mut v_x_3339_: *mut leanh::LeanObject,
    mut v_when_3340_: *mut leanh::LeanObject,
    mut v___y_3341_: *mut leanh::LeanObject,
    mut v___y_3342_: *mut leanh::LeanObject,
    mut v___y_3343_: *mut leanh::LeanObject,
    mut v___y_3344_: *mut leanh::LeanObject,
    mut v___y_3345_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_when_boxed_3346_: u8 = 0;
    let mut v_res_3347_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_when_boxed_3346_ = (leanh::lean_unbox(v_when_3340_) as u8);
    v_res_3347_ = l_Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0___redArg(
        v_x_3339_,
        v_when_boxed_3346_,
        v___y_3341_,
        v___y_3342_,
        v___y_3343_,
        v___y_3344_,
    );
    leanh::lean_dec(v___y_3344_);
    leanh::lean_dec_ref(v___y_3343_);
    leanh::lean_dec(v___y_3342_);
    leanh::lean_dec_ref(v___y_3341_);
    return v_res_3347_;
}
pub unsafe fn _init_l_Lean_validateDefEqAttr___lam__0___closed__1() -> *mut leanh::LeanObject
{
    let mut v___x_3349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3349_ = l_Lean_validateDefEqAttr___lam__0___closed__0;
    v___x_3350_ = l_Lean_stringToMessageData(v___x_3349_);
    return v___x_3350_;
}
pub unsafe fn _init_l_Lean_validateDefEqAttr___lam__0___closed__3() -> *mut leanh::LeanObject
{
    let mut v___x_3352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3353_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3352_ = l_Lean_validateDefEqAttr___lam__0___closed__2;
    v___x_3353_ = l_Lean_stringToMessageData(v___x_3352_);
    return v___x_3353_;
}
pub unsafe fn _init_l_Lean_validateDefEqAttr___lam__0___closed__5() -> *mut leanh::LeanObject
{
    let mut v___x_3355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3356_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3355_ = l_Lean_validateDefEqAttr___lam__0___closed__4;
    v___x_3356_ = l_Lean_stringToMessageData(v___x_3355_);
    return v___x_3356_;
}
pub unsafe fn _init_l_Lean_validateDefEqAttr___lam__0___closed__6() -> *mut leanh::LeanObject
{
    let mut v___x_3357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3357_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_validateDefEqAttr___lam__0___closed__5),
        core::ptr::addr_of_mut!(l_Lean_validateDefEqAttr___lam__0___closed__5_once),
        _init_l_Lean_validateDefEqAttr___lam__0___closed__5,
    );
    v___x_3358_ = l_Lean_MessageData_note(v___x_3357_);
    return v___x_3358_;
}
pub unsafe fn l_Lean_validateDefEqAttr___lam__0(
    mut v_lhs_3359_: *mut leanh::LeanObject,
    mut v_rhs_3360_: *mut leanh::LeanObject,
    mut v___x_3361_: u8,
    mut v___y_3362_: *mut leanh::LeanObject,
    mut v___y_3363_: *mut leanh::LeanObject,
    mut v___y_3364_: *mut leanh::LeanObject,
    mut v___y_3365_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3371_: u8 = 0;
    let mut v_fst_3372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3376_: u8 = 0;
    let mut v___x_3377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isExporting_3379_: u8 = 0;
    let mut v___x_3380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3396_: u8 = 0;
    let mut v___x_3397_: u8 = 0;
    let mut v___x_3399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3406_: u8 = 0;
    let mut v_a_3407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3410_: u8 = 0;
    let mut v___x_3412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3414_: u8 = 0;
    let mut v_reuseFailAlloc_3415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3416_: u8 = 0;
    let mut v_isSharedCheck_3417_: u8 = 0;
    let mut v_a_3418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3421_: u8 = 0;
    let mut v___x_3423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3425_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3367_ = l_Lean_Meta_addPPExplicitToExposeDiff(
                    v_lhs_3359_,
                    v_rhs_3360_,
                    v___y_3362_,
                    v___y_3363_,
                    v___y_3364_,
                    v___y_3365_,
                );
                if leanh::lean_obj_tag(v___x_3367_) == 0 {
                    v_a_3368_ = leanh::lean_ctor_get(v___x_3367_, 0);
                    v_isSharedCheck_3417_ = (!leanh::lean_is_exclusive(v___x_3367_)) as u8;
                    if v_isSharedCheck_3417_ == 0 {
                        v___x_3370_ = v___x_3367_;
                        v_isShared_3371_ = v_isSharedCheck_3417_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3368_);
                        leanh::lean_dec(v___x_3367_);
                        v___x_3370_ = leanh::lean_box(0);
                        v_isShared_3371_ = v_isSharedCheck_3417_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3418_ = leanh::lean_ctor_get(v___x_3367_, 0);
                    v_isSharedCheck_3425_ = (!leanh::lean_is_exclusive(v___x_3367_)) as u8;
                    if v_isSharedCheck_3425_ == 0 {
                        v___x_3420_ = v___x_3367_;
                        v_isShared_3421_ = v_isSharedCheck_3425_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3418_);
                        leanh::lean_dec(v___x_3367_);
                        v___x_3420_ = leanh::lean_box(0);
                        v_isShared_3421_ = v_isSharedCheck_3425_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_3372_ = leanh::lean_ctor_get(v_a_3368_, 0);
                v_snd_3373_ = leanh::lean_ctor_get(v_a_3368_, 1);
                v_isSharedCheck_3416_ = (!leanh::lean_is_exclusive(v_a_3368_)) as u8;
                if v_isSharedCheck_3416_ == 0 {
                    v___x_3375_ = v_a_3368_;
                    v_isShared_3376_ = v_isSharedCheck_3416_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_3373_);
                    leanh::lean_inc(v_fst_3372_);
                    leanh::lean_dec(v_a_3368_);
                    v___x_3375_ = leanh::lean_box(0);
                    v_isShared_3376_ = v_isSharedCheck_3416_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3377_ = lean_st_ref_get(v___y_3365_);
                v_env_3378_ = leanh::lean_ctor_get(v___x_3377_, 0);
                leanh::lean_inc_ref(v_env_3378_);
                leanh::lean_dec(v___x_3377_);
                v_isExporting_3379_ = leanh::lean_ctor_get_uint8(
                    v_env_3378_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                );
                leanh::lean_dec_ref(v_env_3378_);
                v___x_3380_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_validateDefEqAttr___lam__0___closed__1),
                    core::ptr::addr_of_mut!(l_Lean_validateDefEqAttr___lam__0___closed__1_once),
                    _init_l_Lean_validateDefEqAttr___lam__0___closed__1,
                );
                leanh::lean_inc(v_fst_3372_);
                v___x_3381_ = l_Lean_indentExpr(v_fst_3372_);
                if v_isShared_3376_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3375_, 7);
                    leanh::lean_ctor_set(v___x_3375_, 1, v___x_3381_);
                    leanh::lean_ctor_set(v___x_3375_, 0, v___x_3380_);
                    v___x_3383_ = v___x_3375_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3415_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3415_, 0, v___x_3380_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3415_, 1, v___x_3381_);
                    v___x_3383_ = v_reuseFailAlloc_3415_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3384_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_validateDefEqAttr___lam__0___closed__3),
                    core::ptr::addr_of_mut!(l_Lean_validateDefEqAttr___lam__0___closed__3_once),
                    _init_l_Lean_validateDefEqAttr___lam__0___closed__3,
                );
                v___x_3385_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3385_, 0, v___x_3383_);
                leanh::lean_ctor_set(v___x_3385_, 1, v___x_3384_);
                leanh::lean_inc(v_snd_3373_);
                v___x_3386_ = l_Lean_indentExpr(v_snd_3373_);
                v___x_3387_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3387_, 0, v___x_3385_);
                leanh::lean_ctor_set(v___x_3387_, 1, v___x_3386_);
                if v_isExporting_3379_ == 0 {
                    leanh::lean_dec(v_snd_3373_);
                    leanh::lean_dec(v_fst_3372_);
                    if v_isShared_3371_ == 0 {
                        leanh::lean_ctor_set(v___x_3370_, 0, v___x_3387_);
                        v___x_3389_ = v___x_3370_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3390_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3390_, 0, v___x_3387_);
                        v___x_3389_ = v_reuseFailAlloc_3390_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3370_);
                    v___x_3391_ = leanh::lean_alloc_closure(
                        l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___boxed
                            as *mut core::ffi::c_void,
                        7,
                        2,
                    );
                    leanh::lean_closure_set(v___x_3391_, 0, v_fst_3372_);
                    leanh::lean_closure_set(v___x_3391_, 1, v_snd_3373_);
                    v___x_3392_ =
                        l_Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0___redArg(
                            v___x_3391_,
                            v___x_3361_,
                            v___y_3362_,
                            v___y_3363_,
                            v___y_3364_,
                            v___y_3365_,
                        );
                    if leanh::lean_obj_tag(v___x_3392_) == 0 {
                        v_a_3393_ = leanh::lean_ctor_get(v___x_3392_, 0);
                        v_isSharedCheck_3406_ =
                            (!leanh::lean_is_exclusive(v___x_3392_)) as u8;
                        if v_isSharedCheck_3406_ == 0 {
                            v___x_3395_ = v___x_3392_;
                            v_isShared_3396_ = v_isSharedCheck_3406_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3393_);
                            leanh::lean_dec(v___x_3392_);
                            v___x_3395_ = leanh::lean_box(0);
                            v_isShared_3396_ = v_isSharedCheck_3406_;
                            state = 5;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v___x_3387_, 2);
                        v_a_3407_ = leanh::lean_ctor_get(v___x_3392_, 0);
                        v_isSharedCheck_3414_ =
                            (!leanh::lean_is_exclusive(v___x_3392_)) as u8;
                        if v_isSharedCheck_3414_ == 0 {
                            v___x_3409_ = v___x_3392_;
                            v_isShared_3410_ = v_isSharedCheck_3414_;
                            state = 8;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3407_);
                            leanh::lean_dec(v___x_3392_);
                            v___x_3409_ = leanh::lean_box(0);
                            v_isShared_3410_ = v_isSharedCheck_3414_;
                            state = 8;
                            continue;
                        }
                    }
                }
            }
            4 => {
                return v___x_3389_;
            }
            5 => {
                v___x_3397_ = (leanh::lean_unbox(v_a_3393_) as u8);
                leanh::lean_dec(v_a_3393_);
                if v___x_3397_ == 0 {
                    if v_isShared_3396_ == 0 {
                        leanh::lean_ctor_set(v___x_3395_, 0, v___x_3387_);
                        v___x_3399_ = v___x_3395_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3400_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3400_, 0, v___x_3387_);
                        v___x_3399_ = v_reuseFailAlloc_3400_;
                        state = 6;
                        continue;
                    }
                } else {
                    v___x_3401_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_validateDefEqAttr___lam__0___closed__6),
                        core::ptr::addr_of_mut!(l_Lean_validateDefEqAttr___lam__0___closed__6_once),
                        _init_l_Lean_validateDefEqAttr___lam__0___closed__6,
                    );
                    v___x_3402_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3402_, 0, v___x_3387_);
                    leanh::lean_ctor_set(v___x_3402_, 1, v___x_3401_);
                    if v_isShared_3396_ == 0 {
                        leanh::lean_ctor_set(v___x_3395_, 0, v___x_3402_);
                        v___x_3404_ = v___x_3395_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_3405_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3405_, 0, v___x_3402_);
                        v___x_3404_ = v_reuseFailAlloc_3405_;
                        state = 7;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_3399_;
            }
            7 => {
                return v___x_3404_;
            }
            8 => {
                if v_isShared_3410_ == 0 {
                    v___x_3412_ = v___x_3409_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3413_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3413_, 0, v_a_3407_);
                    v___x_3412_ = v_reuseFailAlloc_3413_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3412_;
            }
            10 => {
                if v_isShared_3421_ == 0 {
                    v___x_3423_ = v___x_3420_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3424_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3424_, 0, v_a_3418_);
                    v___x_3423_ = v_reuseFailAlloc_3424_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3423_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_validateDefEqAttr___lam__0___boxed(
    mut v_lhs_3426_: *mut leanh::LeanObject,
    mut v_rhs_3427_: *mut leanh::LeanObject,
    mut v___x_3428_: *mut leanh::LeanObject,
    mut v___y_3429_: *mut leanh::LeanObject,
    mut v___y_3430_: *mut leanh::LeanObject,
    mut v___y_3431_: *mut leanh::LeanObject,
    mut v___y_3432_: *mut leanh::LeanObject,
    mut v___y_3433_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6863__boxed_3434_: u8 = 0;
    let mut v_res_3435_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6863__boxed_3434_ = (leanh::lean_unbox(v___x_3428_) as u8);
    v_res_3435_ = l_Lean_validateDefEqAttr___lam__0(
        v_lhs_3426_,
        v_rhs_3427_,
        v___x_6863__boxed_3434_,
        v___y_3429_,
        v___y_3430_,
        v___y_3431_,
        v___y_3432_,
    );
    leanh::lean_dec(v___y_3432_);
    leanh::lean_dec_ref(v___y_3431_);
    leanh::lean_dec(v___y_3430_);
    leanh::lean_dec_ref(v___y_3429_);
    return v_res_3435_;
}
pub unsafe fn l_Lean_validateDefEqAttr___lam__1(
    mut v_lhs_3436_: *mut leanh::LeanObject,
    mut v_rhs_3437_: *mut leanh::LeanObject,
    mut v___y_3438_: *mut leanh::LeanObject,
    mut v___y_3439_: *mut leanh::LeanObject,
    mut v___y_3440_: *mut leanh::LeanObject,
    mut v___y_3441_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3447_: u8 = 0;
    let mut v___x_3448_: u8 = 0;
    let mut v___x_3449_: u8 = 0;
    let mut v___x_3450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3462_: u8 = 0;
    let mut v_a_3463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3466_: u8 = 0;
    let mut v___x_3468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3470_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_rhs_3437_);
                leanh::lean_inc_ref(v_lhs_3436_);
                v___x_3443_ = l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful(
                    v_lhs_3436_,
                    v_rhs_3437_,
                    v___y_3438_,
                    v___y_3439_,
                    v___y_3440_,
                    v___y_3441_,
                );
                if leanh::lean_obj_tag(v___x_3443_) == 0 {
                    v_a_3444_ = leanh::lean_ctor_get(v___x_3443_, 0);
                    v_isSharedCheck_3462_ = (!leanh::lean_is_exclusive(v___x_3443_)) as u8;
                    if v_isSharedCheck_3462_ == 0 {
                        v___x_3446_ = v___x_3443_;
                        v_isShared_3447_ = v_isSharedCheck_3462_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3444_);
                        leanh::lean_dec(v___x_3443_);
                        v___x_3446_ = leanh::lean_box(0);
                        v_isShared_3447_ = v_isSharedCheck_3462_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_rhs_3437_);
                    leanh::lean_dec_ref(v_lhs_3436_);
                    v_a_3463_ = leanh::lean_ctor_get(v___x_3443_, 0);
                    v_isSharedCheck_3470_ = (!leanh::lean_is_exclusive(v___x_3443_)) as u8;
                    if v_isSharedCheck_3470_ == 0 {
                        v___x_3465_ = v___x_3443_;
                        v_isShared_3466_ = v_isSharedCheck_3470_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3463_);
                        leanh::lean_dec(v___x_3443_);
                        v___x_3465_ = leanh::lean_box(0);
                        v_isShared_3466_ = v_isSharedCheck_3470_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3448_ = (leanh::lean_unbox(v_a_3444_) as u8);
                leanh::lean_dec(v_a_3444_);
                if v___x_3448_ == 0 {
                    leanh::lean_del_object(v___x_3446_);
                    v___x_3449_ = 1;
                    v___x_3450_ = leanh::lean_box((v___x_3449_) as usize);
                    leanh::lean_inc_ref(v_rhs_3437_);
                    leanh::lean_inc_ref(v_lhs_3436_);
                    v___f_3451_ = leanh::lean_alloc_closure(
                        l_Lean_validateDefEqAttr___lam__0___boxed as *mut core::ffi::c_void,
                        8,
                        3,
                    );
                    leanh::lean_closure_set(v___f_3451_, 0, v_lhs_3436_);
                    leanh::lean_closure_set(v___f_3451_, 1, v_rhs_3437_);
                    leanh::lean_closure_set(v___f_3451_, 2, v___x_3450_);
                    v___x_3452_ = leanh::lean_unsigned_to_nat(2);
                    v___x_3453_ = lean_mk_empty_array_with_capacity(v___x_3452_);
                    v___x_3454_ = lean_array_push(v___x_3453_, v_lhs_3436_);
                    v___x_3455_ = lean_array_push(v___x_3454_, v_rhs_3437_);
                    v___x_3456_ = l_Lean_MessageData_ofLazyM(v___f_3451_, v___x_3455_);
                    v___x_3457_ = l_Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0___redArg(v___x_3456_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_);
                    return v___x_3457_;
                } else {
                    leanh::lean_dec_ref(v_rhs_3437_);
                    leanh::lean_dec_ref(v_lhs_3436_);
                    v___x_3458_ = leanh::lean_box(0);
                    if v_isShared_3447_ == 0 {
                        leanh::lean_ctor_set(v___x_3446_, 0, v___x_3458_);
                        v___x_3460_ = v___x_3446_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3461_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3461_, 0, v___x_3458_);
                        v___x_3460_ = v_reuseFailAlloc_3461_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3460_;
            }
            3 => {
                if v_isShared_3466_ == 0 {
                    v___x_3468_ = v___x_3465_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3469_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3469_, 0, v_a_3463_);
                    v___x_3468_ = v_reuseFailAlloc_3469_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3468_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_validateDefEqAttr___lam__1___boxed(
    mut v_lhs_3471_: *mut leanh::LeanObject,
    mut v_rhs_3472_: *mut leanh::LeanObject,
    mut v___y_3473_: *mut leanh::LeanObject,
    mut v___y_3474_: *mut leanh::LeanObject,
    mut v___y_3475_: *mut leanh::LeanObject,
    mut v___y_3476_: *mut leanh::LeanObject,
    mut v___y_3477_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3478_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3478_ = l_Lean_validateDefEqAttr___lam__1(
        v_lhs_3471_,
        v_rhs_3472_,
        v___y_3473_,
        v___y_3474_,
        v___y_3475_,
        v___y_3476_,
    );
    leanh::lean_dec(v___y_3476_);
    leanh::lean_dec_ref(v___y_3475_);
    leanh::lean_dec(v___y_3474_);
    leanh::lean_dec_ref(v___y_3473_);
    return v_res_3478_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3479_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3479_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_3479_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3481_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3480_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__0);
    v___x_3481_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3481_, 0, v___x_3480_);
    return v___x_3481_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_3482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3484_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3482_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1);
    v___x_3483_ = leanh::lean_unsigned_to_nat(0);
    v___x_3484_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_3484_, 0, v___x_3483_);
    leanh::lean_ctor_set(v___x_3484_, 1, v___x_3483_);
    leanh::lean_ctor_set(v___x_3484_, 2, v___x_3483_);
    leanh::lean_ctor_set(v___x_3484_, 3, v___x_3483_);
    leanh::lean_ctor_set(v___x_3484_, 4, v___x_3482_);
    leanh::lean_ctor_set(v___x_3484_, 5, v___x_3482_);
    leanh::lean_ctor_set(v___x_3484_, 6, v___x_3482_);
    leanh::lean_ctor_set(v___x_3484_, 7, v___x_3482_);
    leanh::lean_ctor_set(v___x_3484_, 8, v___x_3482_);
    leanh::lean_ctor_set(v___x_3484_, 9, v___x_3482_);
    return v___x_3484_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3487_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3485_ = leanh::lean_unsigned_to_nat(32);
    v___x_3486_ = lean_mk_empty_array_with_capacity(v___x_3485_);
    v___x_3487_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3487_, 0, v___x_3486_);
    return v___x_3487_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_3488_: usize = 0;
    let mut v___x_3489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3488_ = 5usize;
    v___x_3489_ = leanh::lean_unsigned_to_nat(0);
    v___x_3490_ = leanh::lean_unsigned_to_nat(32);
    v___x_3491_ = lean_mk_empty_array_with_capacity(v___x_3490_);
    v___x_3492_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__3);
    v___x_3493_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_3493_, 0, v___x_3492_);
    leanh::lean_ctor_set(v___x_3493_, 1, v___x_3491_);
    leanh::lean_ctor_set(v___x_3493_, 2, v___x_3489_);
    leanh::lean_ctor_set(v___x_3493_, 3, v___x_3489_);
    leanh::lean_ctor_set_usize(v___x_3493_, 4, v___x_3488_);
    return v___x_3493_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_3494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3494_ = leanh::lean_box(1);
    v___x_3495_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4);
    v___x_3496_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1);
    v___x_3497_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_3497_, 0, v___x_3496_);
    leanh::lean_ctor_set(v___x_3497_, 1, v___x_3495_);
    leanh::lean_ctor_set(v___x_3497_, 2, v___x_3494_);
    return v___x_3497_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_3499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3500_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3499_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__6;
    v___x_3500_ = l_Lean_stringToMessageData(v___x_3499_);
    return v___x_3500_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_3502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3503_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3502_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__8;
    v___x_3503_ = l_Lean_stringToMessageData(v___x_3502_);
    return v___x_3503_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_3505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3505_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__10;
    v___x_3506_ = l_Lean_stringToMessageData(v___x_3505_);
    return v___x_3506_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_3508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3509_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3508_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__12;
    v___x_3509_ = l_Lean_stringToMessageData(v___x_3508_);
    return v___x_3509_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_3511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3512_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3511_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__14;
    v___x_3512_ = l_Lean_stringToMessageData(v___x_3511_);
    return v___x_3512_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__17()
-> *mut leanh::LeanObject {
    let mut v___x_3514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3515_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3514_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__16;
    v___x_3515_ = l_Lean_stringToMessageData(v___x_3514_);
    return v___x_3515_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__19()
-> *mut leanh::LeanObject {
    let mut v___x_3517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3518_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3517_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__18;
    v___x_3518_ = l_Lean_stringToMessageData(v___x_3517_);
    return v___x_3518_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(
    mut v_msg_3519_: *mut leanh::LeanObject,
    mut v_declHint_3520_: *mut leanh::LeanObject,
    mut v___y_3521_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: u8 = 0;
    let mut v_isExporting_3526_: u8 = 0;
    let mut v___x_3527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3529_: u8 = 0;
    let mut v___x_3530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_3536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3548_: u8 = 0;
    let mut v___x_3549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_3552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3553_: u8 = 0;
    let mut v___x_3554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3580_: u8 = 0;
    let mut v___x_3581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3523_ = lean_st_ref_get(v___y_3521_);
                v_env_3524_ = leanh::lean_ctor_get(v___x_3523_, 0);
                leanh::lean_inc_ref(v_env_3524_);
                leanh::lean_dec(v___x_3523_);
                v___x_3525_ = l_Lean_Name_isAnonymous(v_declHint_3520_);
                if v___x_3525_ == 0 {
                    v_isExporting_3526_ = leanh::lean_ctor_get_uint8(
                        v_env_3524_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_3526_ == 0 {
                        leanh::lean_dec_ref(v_env_3524_);
                        leanh::lean_dec(v_declHint_3520_);
                        v___x_3527_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3527_, 0, v_msg_3519_);
                        return v___x_3527_;
                    } else {
                        leanh::lean_inc_ref(v_env_3524_);
                        v___x_3528_ = l_Lean_Environment_setExporting(v_env_3524_, v___x_3525_);
                        leanh::lean_inc(v_declHint_3520_);
                        leanh::lean_inc_ref(v___x_3528_);
                        v___x_3529_ = l_Lean_Environment_contains(
                            v___x_3528_,
                            v_declHint_3520_,
                            v_isExporting_3526_,
                        );
                        if v___x_3529_ == 0 {
                            leanh::lean_dec_ref(v___x_3528_);
                            leanh::lean_dec_ref(v_env_3524_);
                            leanh::lean_dec(v_declHint_3520_);
                            v___x_3530_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_3530_, 0, v_msg_3519_);
                            return v___x_3530_;
                        } else {
                            v___x_3531_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__2);
                            v___x_3532_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__5);
                            v___x_3533_ = l_Lean_Options_empty;
                            v___x_3534_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            leanh::lean_ctor_set(v___x_3534_, 0, v___x_3528_);
                            leanh::lean_ctor_set(v___x_3534_, 1, v___x_3531_);
                            leanh::lean_ctor_set(v___x_3534_, 2, v___x_3532_);
                            leanh::lean_ctor_set(v___x_3534_, 3, v___x_3533_);
                            leanh::lean_inc(v_declHint_3520_);
                            v___x_3535_ =
                                l_Lean_MessageData_ofConstName(v_declHint_3520_, v___x_3525_);
                            v_c_3536_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            leanh::lean_ctor_set(v_c_3536_, 0, v___x_3534_);
                            leanh::lean_ctor_set(v_c_3536_, 1, v___x_3535_);
                            v___x_3537_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_3524_,
                                v_declHint_3520_,
                            );
                            if leanh::lean_obj_tag(v___x_3537_) == 0 {
                                leanh::lean_dec_ref(v_env_3524_);
                                leanh::lean_dec(v_declHint_3520_);
                                v___x_3538_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7);
                                v___x_3539_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3539_, 0, v___x_3538_);
                                leanh::lean_ctor_set(v___x_3539_, 1, v_c_3536_);
                                v___x_3540_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__9);
                                v___x_3541_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3541_, 0, v___x_3539_);
                                leanh::lean_ctor_set(v___x_3541_, 1, v___x_3540_);
                                v___x_3542_ = l_Lean_MessageData_note(v___x_3541_);
                                v___x_3543_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3543_, 0, v_msg_3519_);
                                leanh::lean_ctor_set(v___x_3543_, 1, v___x_3542_);
                                v___x_3544_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_3544_, 0, v___x_3543_);
                                return v___x_3544_;
                            } else {
                                v_val_3545_ = leanh::lean_ctor_get(v___x_3537_, 0);
                                v_isSharedCheck_3580_ =
                                    (!leanh::lean_is_exclusive(v___x_3537_)) as u8;
                                if v_isSharedCheck_3580_ == 0 {
                                    v___x_3547_ = v___x_3537_;
                                    v_isShared_3548_ = v_isSharedCheck_3580_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_val_3545_);
                                    leanh::lean_dec(v___x_3537_);
                                    v___x_3547_ = leanh::lean_box(0);
                                    v_isShared_3548_ = v_isSharedCheck_3580_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_env_3524_);
                    leanh::lean_dec(v_declHint_3520_);
                    v___x_3581_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3581_, 0, v_msg_3519_);
                    return v___x_3581_;
                }
            }
            1 => {
                v___x_3549_ = leanh::lean_box(0);
                v___x_3550_ = l_Lean_Environment_header(v_env_3524_);
                leanh::lean_dec_ref(v_env_3524_);
                v___x_3551_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3550_);
                v_mod_3552_ = lean_array_get(v___x_3549_, v___x_3551_, v_val_3545_);
                leanh::lean_dec(v_val_3545_);
                leanh::lean_dec_ref(v___x_3551_);
                v___x_3553_ = l_Lean_isPrivateName(v_declHint_3520_);
                leanh::lean_dec(v_declHint_3520_);
                if v___x_3553_ == 0 {
                    v___x_3554_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__11);
                    v___x_3555_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3555_, 0, v___x_3554_);
                    leanh::lean_ctor_set(v___x_3555_, 1, v_c_3536_);
                    v___x_3556_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__13);
                    v___x_3557_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3557_, 0, v___x_3555_);
                    leanh::lean_ctor_set(v___x_3557_, 1, v___x_3556_);
                    v___x_3558_ = l_Lean_MessageData_ofName(v_mod_3552_);
                    v___x_3559_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3559_, 0, v___x_3557_);
                    leanh::lean_ctor_set(v___x_3559_, 1, v___x_3558_);
                    v___x_3560_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__15);
                    v___x_3561_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3561_, 0, v___x_3559_);
                    leanh::lean_ctor_set(v___x_3561_, 1, v___x_3560_);
                    v___x_3562_ = l_Lean_MessageData_note(v___x_3561_);
                    v___x_3563_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3563_, 0, v_msg_3519_);
                    leanh::lean_ctor_set(v___x_3563_, 1, v___x_3562_);
                    if v_isShared_3548_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_3547_, 0);
                        leanh::lean_ctor_set(v___x_3547_, 0, v___x_3563_);
                        v___x_3565_ = v___x_3547_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3566_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3566_, 0, v___x_3563_);
                        v___x_3565_ = v_reuseFailAlloc_3566_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3567_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7);
                    v___x_3568_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3568_, 0, v___x_3567_);
                    leanh::lean_ctor_set(v___x_3568_, 1, v_c_3536_);
                    v___x_3569_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__17);
                    v___x_3570_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3570_, 0, v___x_3568_);
                    leanh::lean_ctor_set(v___x_3570_, 1, v___x_3569_);
                    v___x_3571_ = l_Lean_MessageData_ofName(v_mod_3552_);
                    v___x_3572_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3572_, 0, v___x_3570_);
                    leanh::lean_ctor_set(v___x_3572_, 1, v___x_3571_);
                    v___x_3573_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__19);
                    v___x_3574_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3574_, 0, v___x_3572_);
                    leanh::lean_ctor_set(v___x_3574_, 1, v___x_3573_);
                    v___x_3575_ = l_Lean_MessageData_note(v___x_3574_);
                    v___x_3576_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3576_, 0, v_msg_3519_);
                    leanh::lean_ctor_set(v___x_3576_, 1, v___x_3575_);
                    if v_isShared_3548_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_3547_, 0);
                        leanh::lean_ctor_set(v___x_3547_, 0, v___x_3576_);
                        v___x_3578_ = v___x_3547_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3579_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3579_, 0, v___x_3576_);
                        v___x_3578_ = v_reuseFailAlloc_3579_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3565_;
            }
            3 => {
                return v___x_3578_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___boxed(
    mut v_msg_3582_: *mut leanh::LeanObject,
    mut v_declHint_3583_: *mut leanh::LeanObject,
    mut v___y_3584_: *mut leanh::LeanObject,
    mut v___y_3585_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3586_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3586_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(v_msg_3582_, v_declHint_3583_, v___y_3584_);
    leanh::lean_dec(v___y_3584_);
    return v_res_3586_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5(
    mut v_msg_3587_: *mut leanh::LeanObject,
    mut v_declHint_3588_: *mut leanh::LeanObject,
    mut v___y_3589_: *mut leanh::LeanObject,
    mut v___y_3590_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3596_: u8 = 0;
    let mut v___x_3597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3602_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3592_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(v_msg_3587_, v_declHint_3588_, v___y_3590_);
                v_a_3593_ = leanh::lean_ctor_get(v___x_3592_, 0);
                v_isSharedCheck_3602_ = (!leanh::lean_is_exclusive(v___x_3592_)) as u8;
                if v_isSharedCheck_3602_ == 0 {
                    v___x_3595_ = v___x_3592_;
                    v_isShared_3596_ = v_isSharedCheck_3602_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_3593_);
                    leanh::lean_dec(v___x_3592_);
                    v___x_3595_ = leanh::lean_box(0);
                    v_isShared_3596_ = v_isSharedCheck_3602_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3597_ = l_Lean_unknownIdentifierMessageTag;
                v___x_3598_ = leanh::lean_alloc_ctor(8, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3598_, 0, v___x_3597_);
                leanh::lean_ctor_set(v___x_3598_, 1, v_a_3593_);
                if v_isShared_3596_ == 0 {
                    leanh::lean_ctor_set(v___x_3595_, 0, v___x_3598_);
                    v___x_3600_ = v___x_3595_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3601_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3601_, 0, v___x_3598_);
                    v___x_3600_ = v_reuseFailAlloc_3601_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3600_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5___boxed(
    mut v_msg_3603_: *mut leanh::LeanObject,
    mut v_declHint_3604_: *mut leanh::LeanObject,
    mut v___y_3605_: *mut leanh::LeanObject,
    mut v___y_3606_: *mut leanh::LeanObject,
    mut v___y_3607_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3608_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3608_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5(v_msg_3603_, v_declHint_3604_, v___y_3605_, v___y_3606_);
    leanh::lean_dec(v___y_3606_);
    leanh::lean_dec_ref(v___y_3605_);
    return v_res_3608_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9(
    mut v_msgData_3609_: *mut leanh::LeanObject,
    mut v___y_3610_: *mut leanh::LeanObject,
    mut v___y_3611_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3613_ = lean_st_ref_get(v___y_3611_);
    v_env_3614_ = leanh::lean_ctor_get(v___x_3613_, 0);
    leanh::lean_inc_ref(v_env_3614_);
    leanh::lean_dec(v___x_3613_);
    v_options_3615_ = leanh::lean_ctor_get(v___y_3610_, 2);
    v___x_3616_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__2);
    v___x_3617_ = leanh::lean_unsigned_to_nat(32);
    v___x_3618_ = lean_mk_empty_array_with_capacity(v___x_3617_);
    leanh::lean_dec_ref(v___x_3618_);
    v___x_3619_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__5);
    leanh::lean_inc_ref(v_options_3615_);
    v___x_3620_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_3620_, 0, v_env_3614_);
    leanh::lean_ctor_set(v___x_3620_, 1, v___x_3616_);
    leanh::lean_ctor_set(v___x_3620_, 2, v___x_3619_);
    leanh::lean_ctor_set(v___x_3620_, 3, v_options_3615_);
    v___x_3621_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3621_, 0, v___x_3620_);
    leanh::lean_ctor_set(v___x_3621_, 1, v_msgData_3609_);
    v___x_3622_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3622_, 0, v___x_3621_);
    return v___x_3622_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9___boxed(
    mut v_msgData_3623_: *mut leanh::LeanObject,
    mut v___y_3624_: *mut leanh::LeanObject,
    mut v___y_3625_: *mut leanh::LeanObject,
    mut v___y_3626_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3627_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3627_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9(v_msgData_3623_, v___y_3624_, v___y_3625_);
    leanh::lean_dec(v___y_3625_);
    leanh::lean_dec_ref(v___y_3624_);
    return v_res_3627_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8___redArg(
    mut v_msg_3628_: *mut leanh::LeanObject,
    mut v___y_3629_: *mut leanh::LeanObject,
    mut v___y_3630_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_3632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3637_: u8 = 0;
    let mut v___x_3638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3642_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3632_ = leanh::lean_ctor_get(v___y_3629_, 5);
                v___x_3633_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8_spec__9(v_msg_3628_, v___y_3629_, v___y_3630_);
                v_a_3634_ = leanh::lean_ctor_get(v___x_3633_, 0);
                v_isSharedCheck_3642_ = (!leanh::lean_is_exclusive(v___x_3633_)) as u8;
                if v_isSharedCheck_3642_ == 0 {
                    v___x_3636_ = v___x_3633_;
                    v_isShared_3637_ = v_isSharedCheck_3642_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_3634_);
                    leanh::lean_dec(v___x_3633_);
                    v___x_3636_ = leanh::lean_box(0);
                    v_isShared_3637_ = v_isSharedCheck_3642_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_3632_);
                v___x_3638_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3638_, 0, v_ref_3632_);
                leanh::lean_ctor_set(v___x_3638_, 1, v_a_3634_);
                if v_isShared_3637_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3636_, 1);
                    leanh::lean_ctor_set(v___x_3636_, 0, v___x_3638_);
                    v___x_3640_ = v___x_3636_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3641_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3641_, 0, v___x_3638_);
                    v___x_3640_ = v_reuseFailAlloc_3641_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3640_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8___redArg___boxed(
    mut v_msg_3643_: *mut leanh::LeanObject,
    mut v___y_3644_: *mut leanh::LeanObject,
    mut v___y_3645_: *mut leanh::LeanObject,
    mut v___y_3646_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3647_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3647_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8___redArg(v_msg_3643_, v___y_3644_, v___y_3645_);
    leanh::lean_dec(v___y_3645_);
    leanh::lean_dec_ref(v___y_3644_);
    return v_res_3647_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6___redArg(
    mut v_ref_3648_: *mut leanh::LeanObject,
    mut v_msg_3649_: *mut leanh::LeanObject,
    mut v___y_3650_: *mut leanh::LeanObject,
    mut v___y_3651_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_3653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_3657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_3661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_3662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3665_: u8 = 0;
    let mut v_cancelTk_x3f_3666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3667_: u8 = 0;
    let mut v_inheritedTraceOptions_3668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fileName_3653_ = leanh::lean_ctor_get(v___y_3650_, 0);
    v_fileMap_3654_ = leanh::lean_ctor_get(v___y_3650_, 1);
    v_options_3655_ = leanh::lean_ctor_get(v___y_3650_, 2);
    v_currRecDepth_3656_ = leanh::lean_ctor_get(v___y_3650_, 3);
    v_maxRecDepth_3657_ = leanh::lean_ctor_get(v___y_3650_, 4);
    v_ref_3658_ = leanh::lean_ctor_get(v___y_3650_, 5);
    v_currNamespace_3659_ = leanh::lean_ctor_get(v___y_3650_, 6);
    v_openDecls_3660_ = leanh::lean_ctor_get(v___y_3650_, 7);
    v_initHeartbeats_3661_ = leanh::lean_ctor_get(v___y_3650_, 8);
    v_maxHeartbeats_3662_ = leanh::lean_ctor_get(v___y_3650_, 9);
    v_quotContext_3663_ = leanh::lean_ctor_get(v___y_3650_, 10);
    v_currMacroScope_3664_ = leanh::lean_ctor_get(v___y_3650_, 11);
    v_diag_3665_ = leanh::lean_ctor_get_uint8(
        v___y_3650_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_3666_ = leanh::lean_ctor_get(v___y_3650_, 12);
    v_suppressElabErrors_3667_ = leanh::lean_ctor_get_uint8(
        v___y_3650_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_3668_ = leanh::lean_ctor_get(v___y_3650_, 13);
    v_ref_3669_ = l_Lean_replaceRef(v_ref_3648_, v_ref_3658_);
    leanh::lean_inc_ref(v_inheritedTraceOptions_3668_);
    leanh::lean_inc(v_cancelTk_x3f_3666_);
    leanh::lean_inc(v_currMacroScope_3664_);
    leanh::lean_inc(v_quotContext_3663_);
    leanh::lean_inc(v_maxHeartbeats_3662_);
    leanh::lean_inc(v_initHeartbeats_3661_);
    leanh::lean_inc(v_openDecls_3660_);
    leanh::lean_inc(v_currNamespace_3659_);
    leanh::lean_inc(v_maxRecDepth_3657_);
    leanh::lean_inc(v_currRecDepth_3656_);
    leanh::lean_inc_ref(v_options_3655_);
    leanh::lean_inc_ref(v_fileMap_3654_);
    leanh::lean_inc_ref(v_fileName_3653_);
    v___x_3670_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
    leanh::lean_ctor_set(v___x_3670_, 0, v_fileName_3653_);
    leanh::lean_ctor_set(v___x_3670_, 1, v_fileMap_3654_);
    leanh::lean_ctor_set(v___x_3670_, 2, v_options_3655_);
    leanh::lean_ctor_set(v___x_3670_, 3, v_currRecDepth_3656_);
    leanh::lean_ctor_set(v___x_3670_, 4, v_maxRecDepth_3657_);
    leanh::lean_ctor_set(v___x_3670_, 5, v_ref_3669_);
    leanh::lean_ctor_set(v___x_3670_, 6, v_currNamespace_3659_);
    leanh::lean_ctor_set(v___x_3670_, 7, v_openDecls_3660_);
    leanh::lean_ctor_set(v___x_3670_, 8, v_initHeartbeats_3661_);
    leanh::lean_ctor_set(v___x_3670_, 9, v_maxHeartbeats_3662_);
    leanh::lean_ctor_set(v___x_3670_, 10, v_quotContext_3663_);
    leanh::lean_ctor_set(v___x_3670_, 11, v_currMacroScope_3664_);
    leanh::lean_ctor_set(v___x_3670_, 12, v_cancelTk_x3f_3666_);
    leanh::lean_ctor_set(v___x_3670_, 13, v_inheritedTraceOptions_3668_);
    leanh::lean_ctor_set_uint8(
        v___x_3670_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
        v_diag_3665_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_3670_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_3667_,
    );
    v___x_3671_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8___redArg(v_msg_3649_, v___x_3670_, v___y_3651_);
    leanh::lean_dec_ref_known(v___x_3670_, 14);
    return v___x_3671_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6___redArg___boxed(
    mut v_ref_3672_: *mut leanh::LeanObject,
    mut v_msg_3673_: *mut leanh::LeanObject,
    mut v___y_3674_: *mut leanh::LeanObject,
    mut v___y_3675_: *mut leanh::LeanObject,
    mut v___y_3676_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3677_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3677_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6___redArg(v_ref_3672_, v_msg_3673_, v___y_3674_, v___y_3675_);
    leanh::lean_dec(v___y_3675_);
    leanh::lean_dec_ref(v___y_3674_);
    leanh::lean_dec(v_ref_3672_);
    return v_res_3677_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4___redArg(
    mut v_ref_3678_: *mut leanh::LeanObject,
    mut v_msg_3679_: *mut leanh::LeanObject,
    mut v_declHint_3680_: *mut leanh::LeanObject,
    mut v___y_3681_: *mut leanh::LeanObject,
    mut v___y_3682_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3686_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3684_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5(v_msg_3679_, v_declHint_3680_, v___y_3681_, v___y_3682_);
    v_a_3685_ = leanh::lean_ctor_get(v___x_3684_, 0);
    leanh::lean_inc(v_a_3685_);
    leanh::lean_dec_ref(v___x_3684_);
    v___x_3686_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6___redArg(v_ref_3678_, v_a_3685_, v___y_3681_, v___y_3682_);
    return v___x_3686_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4___redArg___boxed(
    mut v_ref_3687_: *mut leanh::LeanObject,
    mut v_msg_3688_: *mut leanh::LeanObject,
    mut v_declHint_3689_: *mut leanh::LeanObject,
    mut v___y_3690_: *mut leanh::LeanObject,
    mut v___y_3691_: *mut leanh::LeanObject,
    mut v___y_3692_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3693_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3693_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4___redArg(v_ref_3687_, v_msg_3688_, v_declHint_3689_, v___y_3690_, v___y_3691_);
    leanh::lean_dec(v___y_3691_);
    leanh::lean_dec_ref(v___y_3690_);
    leanh::lean_dec(v_ref_3687_);
    return v_res_3693_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3696_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3695_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__0;
    v___x_3696_ = l_Lean_stringToMessageData(v___x_3695_);
    return v___x_3696_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3699_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3698_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__2;
    v___x_3699_ = l_Lean_stringToMessageData(v___x_3698_);
    return v___x_3699_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg(
    mut v_ref_3700_: *mut leanh::LeanObject,
    mut v_constName_3701_: *mut leanh::LeanObject,
    mut v___y_3702_: *mut leanh::LeanObject,
    mut v___y_3703_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3706_: u8 = 0;
    let mut v___x_3707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3711_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3705_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__1);
    v___x_3706_ = 0;
    leanh::lean_inc(v_constName_3701_);
    v___x_3707_ = l_Lean_MessageData_ofConstName(v_constName_3701_, v___x_3706_);
    v___x_3708_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3708_, 0, v___x_3705_);
    leanh::lean_ctor_set(v___x_3708_, 1, v___x_3707_);
    v___x_3709_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3);
    v___x_3710_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3710_, 0, v___x_3708_);
    leanh::lean_ctor_set(v___x_3710_, 1, v___x_3709_);
    v___x_3711_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4___redArg(v_ref_3700_, v___x_3710_, v_constName_3701_, v___y_3702_, v___y_3703_);
    return v___x_3711_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___boxed(
    mut v_ref_3712_: *mut leanh::LeanObject,
    mut v_constName_3713_: *mut leanh::LeanObject,
    mut v___y_3714_: *mut leanh::LeanObject,
    mut v___y_3715_: *mut leanh::LeanObject,
    mut v___y_3716_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3717_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3717_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg(v_ref_3712_, v_constName_3713_, v___y_3714_, v___y_3715_);
    leanh::lean_dec(v___y_3715_);
    leanh::lean_dec_ref(v___y_3714_);
    leanh::lean_dec(v_ref_3712_);
    return v_res_3717_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2___redArg(
    mut v_constName_3718_: *mut leanh::LeanObject,
    mut v___y_3719_: *mut leanh::LeanObject,
    mut v___y_3720_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_3722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3723_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_3722_ = leanh::lean_ctor_get(v___y_3719_, 5);
    v___x_3723_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg(v_ref_3722_, v_constName_3718_, v___y_3719_, v___y_3720_);
    return v___x_3723_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2___redArg___boxed(
    mut v_constName_3724_: *mut leanh::LeanObject,
    mut v___y_3725_: *mut leanh::LeanObject,
    mut v___y_3726_: *mut leanh::LeanObject,
    mut v___y_3727_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3728_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3728_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2___redArg(v_constName_3724_, v___y_3725_, v___y_3726_);
    leanh::lean_dec(v___y_3726_);
    leanh::lean_dec_ref(v___y_3725_);
    return v_res_3728_;
}
pub unsafe fn l_Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1(
    mut v_constName_3729_: *mut leanh::LeanObject,
    mut v___y_3730_: *mut leanh::LeanObject,
    mut v___y_3731_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3735_: u8 = 0;
    let mut v___x_3736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3741_: u8 = 0;
    let mut v___x_3743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3745_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3733_ = lean_st_ref_get(v___y_3731_);
                v_env_3734_ = leanh::lean_ctor_get(v___x_3733_, 0);
                leanh::lean_inc_ref(v_env_3734_);
                leanh::lean_dec(v___x_3733_);
                v___x_3735_ = 0;
                leanh::lean_inc(v_constName_3729_);
                v___x_3736_ = l_Lean_Environment_findConstVal_x3f(
                    v_env_3734_,
                    v_constName_3729_,
                    v___x_3735_,
                );
                if leanh::lean_obj_tag(v___x_3736_) == 0 {
                    v___x_3737_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2___redArg(v_constName_3729_, v___y_3730_, v___y_3731_);
                    return v___x_3737_;
                } else {
                    leanh::lean_dec(v_constName_3729_);
                    v_val_3738_ = leanh::lean_ctor_get(v___x_3736_, 0);
                    v_isSharedCheck_3745_ = (!leanh::lean_is_exclusive(v___x_3736_)) as u8;
                    if v_isSharedCheck_3745_ == 0 {
                        v___x_3740_ = v___x_3736_;
                        v_isShared_3741_ = v_isSharedCheck_3745_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_3738_);
                        leanh::lean_dec(v___x_3736_);
                        v___x_3740_ = leanh::lean_box(0);
                        v_isShared_3741_ = v_isSharedCheck_3745_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3741_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3740_, 0);
                    v___x_3743_ = v___x_3740_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3744_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3744_, 0, v_val_3738_);
                    v___x_3743_ = v_reuseFailAlloc_3744_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3743_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1___boxed(
    mut v_constName_3746_: *mut leanh::LeanObject,
    mut v___y_3747_: *mut leanh::LeanObject,
    mut v___y_3748_: *mut leanh::LeanObject,
    mut v___y_3749_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3750_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3750_ = l_Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1(
        v_constName_3746_,
        v___y_3747_,
        v___y_3748_,
    );
    leanh::lean_dec(v___y_3748_);
    leanh::lean_dec_ref(v___y_3747_);
    return v_res_3750_;
}
pub unsafe fn _init_l_Lean_validateDefEqAttr___closed__1() -> u64 {
    let mut v___x_3757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3758_: u64 = 0;
    v___x_3757_ = l_Lean_validateDefEqAttr___closed__0;
    v___x_3758_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3757_);
    return v___x_3758_;
}
pub unsafe fn _init_l_Lean_validateDefEqAttr___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_3759_: u64 = 0;
    let mut v___x_3760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3761_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3759_ = leanh::lean_uint64_once(
        core::ptr::addr_of_mut!(l_Lean_validateDefEqAttr___closed__1),
        core::ptr::addr_of_mut!(l_Lean_validateDefEqAttr___closed__1_once),
        _init_l_Lean_validateDefEqAttr___closed__1,
    );
    v___x_3760_ = l_Lean_validateDefEqAttr___closed__0;
    v___x_3761_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
    leanh::lean_ctor_set(v___x_3761_, 0, v___x_3760_);
    leanh::lean_ctor_set_uint64(
        v___x_3761_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_3759_,
    );
    return v___x_3761_;
}
pub unsafe fn _init_l_Lean_validateDefEqAttr___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_3762_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3762_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_3762_;
}
pub unsafe fn _init_l_Lean_validateDefEqAttr___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_3763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3764_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3763_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_validateDefEqAttr___closed__3),
        core::ptr::addr_of_mut!(l_Lean_validateDefEqAttr___closed__3_once),
        _init_l_Lean_validateDefEqAttr___closed__3,
    );
    v___x_3764_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3764_, 0, v___x_3763_);
    return v___x_3764_;
}
pub unsafe fn _init_l_Lean_validateDefEqAttr___closed__5() -> *mut leanh::LeanObject {
    let mut v___x_3765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3768_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3765_ = leanh::lean_box(1);
    v___x_3766_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4);
    v___x_3767_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_validateDefEqAttr___closed__4),
        core::ptr::addr_of_mut!(l_Lean_validateDefEqAttr___closed__4_once),
        _init_l_Lean_validateDefEqAttr___closed__4,
    );
    v___x_3768_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_3768_, 0, v___x_3767_);
    leanh::lean_ctor_set(v___x_3768_, 1, v___x_3766_);
    leanh::lean_ctor_set(v___x_3768_, 2, v___x_3765_);
    return v___x_3768_;
}
pub unsafe fn _init_l_Lean_validateDefEqAttr___closed__7() -> *mut leanh::LeanObject {
    let mut v___x_3771_: u8 = 0;
    let mut v___x_3772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: u8 = 0;
    let mut v___x_3778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3779_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3771_ = 1;
    v___x_3772_ = leanh::lean_unsigned_to_nat(0);
    v___x_3773_ = leanh::lean_box(0);
    v___x_3774_ = l_Lean_validateDefEqAttr___closed__6;
    v___x_3775_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_validateDefEqAttr___closed__5),
        core::ptr::addr_of_mut!(l_Lean_validateDefEqAttr___closed__5_once),
        _init_l_Lean_validateDefEqAttr___closed__5,
    );
    v___x_3776_ = leanh::lean_box(1);
    v___x_3777_ = 0;
    v___x_3778_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_validateDefEqAttr___closed__2),
        core::ptr::addr_of_mut!(l_Lean_validateDefEqAttr___closed__2_once),
        _init_l_Lean_validateDefEqAttr___closed__2,
    );
    v___x_3779_ = leanh::lean_alloc_ctor(0, 7, (4) as u32);
    leanh::lean_ctor_set(v___x_3779_, 0, v___x_3778_);
    leanh::lean_ctor_set(v___x_3779_, 1, v___x_3776_);
    leanh::lean_ctor_set(v___x_3779_, 2, v___x_3775_);
    leanh::lean_ctor_set(v___x_3779_, 3, v___x_3774_);
    leanh::lean_ctor_set(v___x_3779_, 4, v___x_3773_);
    leanh::lean_ctor_set(v___x_3779_, 5, v___x_3772_);
    leanh::lean_ctor_set(v___x_3779_, 6, v___x_3773_);
    leanh::lean_ctor_set_uint8(
        v___x_3779_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
        v___x_3777_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_3779_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
        v___x_3777_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_3779_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
        v___x_3777_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_3779_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
        v___x_3771_,
    );
    return v___x_3779_;
}
pub unsafe fn _init_l_Lean_validateDefEqAttr___closed__8() -> *mut leanh::LeanObject {
    let mut v___x_3780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3782_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3780_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_validateDefEqAttr___closed__4),
        core::ptr::addr_of_mut!(l_Lean_validateDefEqAttr___closed__4_once),
        _init_l_Lean_validateDefEqAttr___closed__4,
    );
    v___x_3781_ = leanh::lean_unsigned_to_nat(0);
    v___x_3782_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_3782_, 0, v___x_3781_);
    leanh::lean_ctor_set(v___x_3782_, 1, v___x_3781_);
    leanh::lean_ctor_set(v___x_3782_, 2, v___x_3781_);
    leanh::lean_ctor_set(v___x_3782_, 3, v___x_3781_);
    leanh::lean_ctor_set(v___x_3782_, 4, v___x_3780_);
    leanh::lean_ctor_set(v___x_3782_, 5, v___x_3780_);
    leanh::lean_ctor_set(v___x_3782_, 6, v___x_3780_);
    leanh::lean_ctor_set(v___x_3782_, 7, v___x_3780_);
    leanh::lean_ctor_set(v___x_3782_, 8, v___x_3780_);
    leanh::lean_ctor_set(v___x_3782_, 9, v___x_3780_);
    return v___x_3782_;
}
pub unsafe fn _init_l_Lean_validateDefEqAttr___closed__9() -> *mut leanh::LeanObject {
    let mut v___x_3783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3784_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3783_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_validateDefEqAttr___closed__4),
        core::ptr::addr_of_mut!(l_Lean_validateDefEqAttr___closed__4_once),
        _init_l_Lean_validateDefEqAttr___closed__4,
    );
    v___x_3784_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
    leanh::lean_ctor_set(v___x_3784_, 0, v___x_3783_);
    leanh::lean_ctor_set(v___x_3784_, 1, v___x_3783_);
    leanh::lean_ctor_set(v___x_3784_, 2, v___x_3783_);
    leanh::lean_ctor_set(v___x_3784_, 3, v___x_3783_);
    leanh::lean_ctor_set(v___x_3784_, 4, v___x_3783_);
    leanh::lean_ctor_set(v___x_3784_, 5, v___x_3783_);
    return v___x_3784_;
}
pub unsafe fn _init_l_Lean_validateDefEqAttr___closed__10() -> *mut leanh::LeanObject {
    let mut v___x_3785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3786_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3785_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_validateDefEqAttr___closed__4),
        core::ptr::addr_of_mut!(l_Lean_validateDefEqAttr___closed__4_once),
        _init_l_Lean_validateDefEqAttr___closed__4,
    );
    v___x_3786_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_3786_, 0, v___x_3785_);
    leanh::lean_ctor_set(v___x_3786_, 1, v___x_3785_);
    leanh::lean_ctor_set(v___x_3786_, 2, v___x_3785_);
    leanh::lean_ctor_set(v___x_3786_, 3, v___x_3785_);
    leanh::lean_ctor_set(v___x_3786_, 4, v___x_3785_);
    return v___x_3786_;
}
pub unsafe fn _init_l_Lean_validateDefEqAttr___closed__11() -> *mut leanh::LeanObject {
    let mut v___x_3787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3792_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3787_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_validateDefEqAttr___closed__10),
        core::ptr::addr_of_mut!(l_Lean_validateDefEqAttr___closed__10_once),
        _init_l_Lean_validateDefEqAttr___closed__10,
    );
    v___x_3788_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4);
    v___x_3789_ = leanh::lean_box(1);
    v___x_3790_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_validateDefEqAttr___closed__9),
        core::ptr::addr_of_mut!(l_Lean_validateDefEqAttr___closed__9_once),
        _init_l_Lean_validateDefEqAttr___closed__9,
    );
    v___x_3791_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_validateDefEqAttr___closed__8),
        core::ptr::addr_of_mut!(l_Lean_validateDefEqAttr___closed__8_once),
        _init_l_Lean_validateDefEqAttr___closed__8,
    );
    v___x_3792_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_3792_, 0, v___x_3791_);
    leanh::lean_ctor_set(v___x_3792_, 1, v___x_3790_);
    leanh::lean_ctor_set(v___x_3792_, 2, v___x_3789_);
    leanh::lean_ctor_set(v___x_3792_, 3, v___x_3788_);
    leanh::lean_ctor_set(v___x_3792_, 4, v___x_3787_);
    return v___x_3792_;
}
pub unsafe fn l_Lean_validateDefEqAttr(
    mut v_declName_3794_: *mut leanh::LeanObject,
    mut v_a_3795_: *mut leanh::LeanObject,
    mut v_a_3796_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3809_: u8 = 0;
    let mut v___x_3810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3814_: u8 = 0;
    let mut v_a_3815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3818_: u8 = 0;
    let mut v___x_3820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3822_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3798_ = l_Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1(
                    v_declName_3794_,
                    v_a_3795_,
                    v_a_3796_,
                );
                if leanh::lean_obj_tag(v___x_3798_) == 0 {
                    v_a_3799_ = leanh::lean_ctor_get(v___x_3798_, 0);
                    leanh::lean_inc(v_a_3799_);
                    leanh::lean_dec_ref_known(v___x_3798_, 1);
                    v___x_3800_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_validateDefEqAttr___closed__7),
                        core::ptr::addr_of_mut!(l_Lean_validateDefEqAttr___closed__7_once),
                        _init_l_Lean_validateDefEqAttr___closed__7,
                    );
                    v___x_3801_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_validateDefEqAttr___closed__11),
                        core::ptr::addr_of_mut!(l_Lean_validateDefEqAttr___closed__11_once),
                        _init_l_Lean_validateDefEqAttr___closed__11,
                    );
                    v___x_3802_ = lean_st_mk_ref(v___x_3801_);
                    v_type_3803_ = leanh::lean_ctor_get(v_a_3799_, 2);
                    leanh::lean_inc_ref(v_type_3803_);
                    leanh::lean_dec(v_a_3799_);
                    v___f_3804_ = l_Lean_validateDefEqAttr___closed__12;
                    v___x_3805_ = l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg(
                        v_type_3803_,
                        v___f_3804_,
                        v___x_3800_,
                        v___x_3802_,
                        v_a_3795_,
                        v_a_3796_,
                    );
                    if leanh::lean_obj_tag(v___x_3805_) == 0 {
                        v_a_3806_ = leanh::lean_ctor_get(v___x_3805_, 0);
                        v_isSharedCheck_3814_ =
                            (!leanh::lean_is_exclusive(v___x_3805_)) as u8;
                        if v_isSharedCheck_3814_ == 0 {
                            v___x_3808_ = v___x_3805_;
                            v_isShared_3809_ = v_isSharedCheck_3814_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3806_);
                            leanh::lean_dec(v___x_3805_);
                            v___x_3808_ = leanh::lean_box(0);
                            v_isShared_3809_ = v_isSharedCheck_3814_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_3802_);
                        return v___x_3805_;
                    }
                } else {
                    v_a_3815_ = leanh::lean_ctor_get(v___x_3798_, 0);
                    v_isSharedCheck_3822_ = (!leanh::lean_is_exclusive(v___x_3798_)) as u8;
                    if v_isSharedCheck_3822_ == 0 {
                        v___x_3817_ = v___x_3798_;
                        v_isShared_3818_ = v_isSharedCheck_3822_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3815_);
                        leanh::lean_dec(v___x_3798_);
                        v___x_3817_ = leanh::lean_box(0);
                        v_isShared_3818_ = v_isSharedCheck_3822_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3810_ = lean_st_ref_get(v___x_3802_);
                leanh::lean_dec(v___x_3802_);
                leanh::lean_dec(v___x_3810_);
                if v_isShared_3809_ == 0 {
                    v___x_3812_ = v___x_3808_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3813_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3813_, 0, v_a_3806_);
                    v___x_3812_ = v_reuseFailAlloc_3813_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3812_;
            }
            3 => {
                if v_isShared_3818_ == 0 {
                    v___x_3820_ = v___x_3817_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3821_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3821_, 0, v_a_3815_);
                    v___x_3820_ = v_reuseFailAlloc_3821_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3820_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_validateDefEqAttr___boxed(
    mut v_declName_3823_: *mut leanh::LeanObject,
    mut v_a_3824_: *mut leanh::LeanObject,
    mut v_a_3825_: *mut leanh::LeanObject,
    mut v_a_3826_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3827_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3827_ = l_Lean_validateDefEqAttr(v_declName_3823_, v_a_3824_, v_a_3825_);
    leanh::lean_dec(v_a_3825_);
    leanh::lean_dec_ref(v_a_3824_);
    return v_res_3827_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0(
    mut v_00_u03b1_3828_: *mut leanh::LeanObject,
    mut v_x_3829_: *mut leanh::LeanObject,
    mut v_isExporting_3830_: u8,
    mut v___y_3831_: *mut leanh::LeanObject,
    mut v___y_3832_: *mut leanh::LeanObject,
    mut v___y_3833_: *mut leanh::LeanObject,
    mut v___y_3834_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3836_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3836_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg(v_x_3829_, v_isExporting_3830_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_);
    return v___x_3836_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___boxed(
    mut v_00_u03b1_3837_: *mut leanh::LeanObject,
    mut v_x_3838_: *mut leanh::LeanObject,
    mut v_isExporting_3839_: *mut leanh::LeanObject,
    mut v___y_3840_: *mut leanh::LeanObject,
    mut v___y_3841_: *mut leanh::LeanObject,
    mut v___y_3842_: *mut leanh::LeanObject,
    mut v___y_3843_: *mut leanh::LeanObject,
    mut v___y_3844_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isExporting_boxed_3845_: u8 = 0;
    let mut v_res_3846_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_3845_ = (leanh::lean_unbox(v_isExporting_3839_) as u8);
    v_res_3846_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0(v_00_u03b1_3837_, v_x_3838_, v_isExporting_boxed_3845_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_);
    leanh::lean_dec(v___y_3843_);
    leanh::lean_dec_ref(v___y_3842_);
    leanh::lean_dec(v___y_3841_);
    leanh::lean_dec_ref(v___y_3840_);
    return v_res_3846_;
}
pub unsafe fn l_Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0(
    mut v_00_u03b1_3847_: *mut leanh::LeanObject,
    mut v_x_3848_: *mut leanh::LeanObject,
    mut v_when_3849_: u8,
    mut v___y_3850_: *mut leanh::LeanObject,
    mut v___y_3851_: *mut leanh::LeanObject,
    mut v___y_3852_: *mut leanh::LeanObject,
    mut v___y_3853_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3855_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3855_ = l_Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0___redArg(
        v_x_3848_,
        v_when_3849_,
        v___y_3850_,
        v___y_3851_,
        v___y_3852_,
        v___y_3853_,
    );
    return v___x_3855_;
}
pub unsafe fn l_Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0___boxed(
    mut v_00_u03b1_3856_: *mut leanh::LeanObject,
    mut v_x_3857_: *mut leanh::LeanObject,
    mut v_when_3858_: *mut leanh::LeanObject,
    mut v___y_3859_: *mut leanh::LeanObject,
    mut v___y_3860_: *mut leanh::LeanObject,
    mut v___y_3861_: *mut leanh::LeanObject,
    mut v___y_3862_: *mut leanh::LeanObject,
    mut v___y_3863_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_when_boxed_3864_: u8 = 0;
    let mut v_res_3865_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_when_boxed_3864_ = (leanh::lean_unbox(v_when_3858_) as u8);
    v_res_3865_ = l_Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0(
        v_00_u03b1_3856_,
        v_x_3857_,
        v_when_boxed_3864_,
        v___y_3859_,
        v___y_3860_,
        v___y_3861_,
        v___y_3862_,
    );
    leanh::lean_dec(v___y_3862_);
    leanh::lean_dec_ref(v___y_3861_);
    leanh::lean_dec(v___y_3860_);
    leanh::lean_dec_ref(v___y_3859_);
    return v_res_3865_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2(
    mut v_00_u03b1_3866_: *mut leanh::LeanObject,
    mut v_constName_3867_: *mut leanh::LeanObject,
    mut v___y_3868_: *mut leanh::LeanObject,
    mut v___y_3869_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3871_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3871_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2___redArg(v_constName_3867_, v___y_3868_, v___y_3869_);
    return v___x_3871_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2___boxed(
    mut v_00_u03b1_3872_: *mut leanh::LeanObject,
    mut v_constName_3873_: *mut leanh::LeanObject,
    mut v___y_3874_: *mut leanh::LeanObject,
    mut v___y_3875_: *mut leanh::LeanObject,
    mut v___y_3876_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3877_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3877_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2(v_00_u03b1_3872_, v_constName_3873_, v___y_3874_, v___y_3875_);
    leanh::lean_dec(v___y_3875_);
    leanh::lean_dec_ref(v___y_3874_);
    return v_res_3877_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3(
    mut v_00_u03b1_3878_: *mut leanh::LeanObject,
    mut v_ref_3879_: *mut leanh::LeanObject,
    mut v_constName_3880_: *mut leanh::LeanObject,
    mut v___y_3881_: *mut leanh::LeanObject,
    mut v___y_3882_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3884_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3884_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg(v_ref_3879_, v_constName_3880_, v___y_3881_, v___y_3882_);
    return v___x_3884_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___boxed(
    mut v_00_u03b1_3885_: *mut leanh::LeanObject,
    mut v_ref_3886_: *mut leanh::LeanObject,
    mut v_constName_3887_: *mut leanh::LeanObject,
    mut v___y_3888_: *mut leanh::LeanObject,
    mut v___y_3889_: *mut leanh::LeanObject,
    mut v___y_3890_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3891_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3891_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3(v_00_u03b1_3885_, v_ref_3886_, v_constName_3887_, v___y_3888_, v___y_3889_);
    leanh::lean_dec(v___y_3889_);
    leanh::lean_dec_ref(v___y_3888_);
    leanh::lean_dec(v_ref_3886_);
    return v_res_3891_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4(
    mut v_00_u03b1_3892_: *mut leanh::LeanObject,
    mut v_ref_3893_: *mut leanh::LeanObject,
    mut v_msg_3894_: *mut leanh::LeanObject,
    mut v_declHint_3895_: *mut leanh::LeanObject,
    mut v___y_3896_: *mut leanh::LeanObject,
    mut v___y_3897_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3899_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3899_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4___redArg(v_ref_3893_, v_msg_3894_, v_declHint_3895_, v___y_3896_, v___y_3897_);
    return v___x_3899_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4___boxed(
    mut v_00_u03b1_3900_: *mut leanh::LeanObject,
    mut v_ref_3901_: *mut leanh::LeanObject,
    mut v_msg_3902_: *mut leanh::LeanObject,
    mut v_declHint_3903_: *mut leanh::LeanObject,
    mut v___y_3904_: *mut leanh::LeanObject,
    mut v___y_3905_: *mut leanh::LeanObject,
    mut v___y_3906_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3907_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3907_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4(v_00_u03b1_3900_, v_ref_3901_, v_msg_3902_, v_declHint_3903_, v___y_3904_, v___y_3905_);
    leanh::lean_dec(v___y_3905_);
    leanh::lean_dec_ref(v___y_3904_);
    leanh::lean_dec(v_ref_3901_);
    return v_res_3907_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6(
    mut v_msg_3908_: *mut leanh::LeanObject,
    mut v_declHint_3909_: *mut leanh::LeanObject,
    mut v___y_3910_: *mut leanh::LeanObject,
    mut v___y_3911_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3913_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3913_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(v_msg_3908_, v_declHint_3909_, v___y_3911_);
    return v___x_3913_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___boxed(
    mut v_msg_3914_: *mut leanh::LeanObject,
    mut v_declHint_3915_: *mut leanh::LeanObject,
    mut v___y_3916_: *mut leanh::LeanObject,
    mut v___y_3917_: *mut leanh::LeanObject,
    mut v___y_3918_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3919_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3919_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6(v_msg_3914_, v_declHint_3915_, v___y_3916_, v___y_3917_);
    leanh::lean_dec(v___y_3917_);
    leanh::lean_dec_ref(v___y_3916_);
    return v_res_3919_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6(
    mut v_00_u03b1_3920_: *mut leanh::LeanObject,
    mut v_ref_3921_: *mut leanh::LeanObject,
    mut v_msg_3922_: *mut leanh::LeanObject,
    mut v___y_3923_: *mut leanh::LeanObject,
    mut v___y_3924_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3926_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3926_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6___redArg(v_ref_3921_, v_msg_3922_, v___y_3923_, v___y_3924_);
    return v___x_3926_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6___boxed(
    mut v_00_u03b1_3927_: *mut leanh::LeanObject,
    mut v_ref_3928_: *mut leanh::LeanObject,
    mut v_msg_3929_: *mut leanh::LeanObject,
    mut v___y_3930_: *mut leanh::LeanObject,
    mut v___y_3931_: *mut leanh::LeanObject,
    mut v___y_3932_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3933_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3933_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6(v_00_u03b1_3927_, v_ref_3928_, v_msg_3929_, v___y_3930_, v___y_3931_);
    leanh::lean_dec(v___y_3931_);
    leanh::lean_dec_ref(v___y_3930_);
    leanh::lean_dec(v_ref_3928_);
    return v_res_3933_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8(
    mut v_00_u03b1_3934_: *mut leanh::LeanObject,
    mut v_msg_3935_: *mut leanh::LeanObject,
    mut v___y_3936_: *mut leanh::LeanObject,
    mut v___y_3937_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3939_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3939_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8___redArg(v_msg_3935_, v___y_3936_, v___y_3937_);
    return v___x_3939_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8___boxed(
    mut v_00_u03b1_3940_: *mut leanh::LeanObject,
    mut v_msg_3941_: *mut leanh::LeanObject,
    mut v___y_3942_: *mut leanh::LeanObject,
    mut v___y_3943_: *mut leanh::LeanObject,
    mut v___y_3944_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3945_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3945_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8(v_00_u03b1_3940_, v_msg_3941_, v___y_3942_, v___y_3943_);
    leanh::lean_dec(v___y_3943_);
    leanh::lean_dec_ref(v___y_3942_);
    return v_res_3945_;
}
pub unsafe fn l___private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_3958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3962_: u8 = 0;
    let mut v___x_3963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3958_ = l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__1_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_;
    v___x_3959_ = l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__2_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_;
    v___x_3960_ = l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__3_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_;
    v___x_3961_ = l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__5_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_;
    v___x_3962_ = 0;
    v___x_3963_ = l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__6_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_;
    v___x_3964_ = l_Lean_registerTagAttribute(
        v___x_3958_,
        v___x_3959_,
        v___x_3960_,
        v___x_3961_,
        v___x_3962_,
        v___x_3963_,
    );
    return v___x_3964_;
}
pub unsafe fn l___private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2____boxed(
    mut v_a_3965_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3966_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3966_ = l___private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_();
    return v_res_3966_;
}
pub unsafe fn l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_docString__1()
-> *mut leanh::LeanObject {
    let mut v___x_3969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3971_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3969_ = l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__5_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_;
    v___x_3970_ = l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_docString__1___closed__0;
    v___x_3971_ = l_Lean_addBuiltinDocString(v___x_3969_, v___x_3970_);
    return v___x_3971_;
}
pub unsafe fn l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_docString__1___boxed(
    mut v_a_3972_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3973_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3973_ = l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_docString__1();
    return v_res_3973_;
}
pub unsafe fn l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3()
-> *mut leanh::LeanObject {
    let mut v___x_4000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4000_ = l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__5_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_;
    v___x_4001_ = l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___closed__6;
    v___x_4002_ = l_Lean_addBuiltinDeclarationRanges(v___x_4000_, v___x_4001_);
    return v___x_4002_;
}
pub unsafe fn l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3___boxed(
    mut v_a_4003_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4004_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4004_ = l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3();
    return v_res_4004_;
}
pub unsafe fn _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4006_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0;
    v___x_4007_ = l_Lean_stringToMessageData(v___x_4006_);
    return v___x_4007_;
}
pub unsafe fn _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_4009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4009_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__2;
    v___x_4010_ = l_Lean_stringToMessageData(v___x_4009_);
    return v___x_4010_;
}
pub unsafe fn _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_4012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4012_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__4;
    v___x_4013_ = l_Lean_stringToMessageData(v___x_4012_);
    return v___x_4013_;
}
pub unsafe fn _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_4015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4016_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4015_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__6;
    v___x_4016_ = l_Lean_stringToMessageData(v___x_4015_);
    return v___x_4016_;
}
pub unsafe fn l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__0___redArg(
    mut v_attrName_4017_: *mut leanh::LeanObject,
    mut v_declName_4018_: *mut leanh::LeanObject,
    mut v_asyncPrefix_x3f_4019_: *mut leanh::LeanObject,
    mut v___y_4020_: *mut leanh::LeanObject,
    mut v___y_4021_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: u8 = 0;
    let mut v___x_4031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_asyncPrefix_x3f_4019_) == 0 {
                    v___x_4037_ = l_Lean_MessageData_nil;
                    v___y_4024_ = v___x_4037_;
                    state = 1;
                    continue;
                } else {
                    v_val_4038_ = leanh::lean_ctor_get(v_asyncPrefix_x3f_4019_, 0);
                    leanh::lean_inc(v_val_4038_);
                    leanh::lean_dec_ref_known(v_asyncPrefix_x3f_4019_, 1);
                    v___x_4039_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__7_once), _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__7);
                    v___x_4040_ = l_Lean_MessageData_ofName(v_val_4038_);
                    v___x_4041_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4041_, 0, v___x_4039_);
                    leanh::lean_ctor_set(v___x_4041_, 1, v___x_4040_);
                    v___x_4042_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3);
                    v___x_4043_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4043_, 0, v___x_4041_);
                    leanh::lean_ctor_set(v___x_4043_, 1, v___x_4042_);
                    v___y_4024_ = v___x_4043_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4025_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1);
                v___x_4026_ = l_Lean_MessageData_ofName(v_attrName_4017_);
                v___x_4027_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4027_, 0, v___x_4025_);
                leanh::lean_ctor_set(v___x_4027_, 1, v___x_4026_);
                v___x_4028_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3_once), _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3);
                v___x_4029_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4029_, 0, v___x_4027_);
                leanh::lean_ctor_set(v___x_4029_, 1, v___x_4028_);
                v___x_4030_ = 0;
                v___x_4031_ = l_Lean_MessageData_ofConstName(v_declName_4018_, v___x_4030_);
                v___x_4032_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4032_, 0, v___x_4029_);
                leanh::lean_ctor_set(v___x_4032_, 1, v___x_4031_);
                v___x_4033_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__5_once), _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__5);
                v___x_4034_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4034_, 0, v___x_4032_);
                leanh::lean_ctor_set(v___x_4034_, 1, v___x_4033_);
                v___x_4035_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4035_, 0, v___x_4034_);
                leanh::lean_ctor_set(v___x_4035_, 1, v___y_4024_);
                v___x_4036_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8___redArg(v___x_4035_, v___y_4020_, v___y_4021_);
                return v___x_4036_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(
    mut v_attrName_4044_: *mut leanh::LeanObject,
    mut v_declName_4045_: *mut leanh::LeanObject,
    mut v_asyncPrefix_x3f_4046_: *mut leanh::LeanObject,
    mut v___y_4047_: *mut leanh::LeanObject,
    mut v___y_4048_: *mut leanh::LeanObject,
    mut v___y_4049_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4050_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4050_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__0___redArg(v_attrName_4044_, v_declName_4045_, v_asyncPrefix_x3f_4046_, v___y_4047_, v___y_4048_);
    leanh::lean_dec(v___y_4048_);
    leanh::lean_dec_ref(v___y_4047_);
    return v_res_4050_;
}
pub unsafe fn _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__1___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4053_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4052_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__1___redArg___closed__0;
    v___x_4053_ = l_Lean_stringToMessageData(v___x_4052_);
    return v___x_4053_;
}
pub unsafe fn l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__1___redArg(
    mut v_attrName_4054_: *mut leanh::LeanObject,
    mut v_declName_4055_: *mut leanh::LeanObject,
    mut v___y_4056_: *mut leanh::LeanObject,
    mut v___y_4057_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4064_: u8 = 0;
    let mut v___x_4065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4069_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4059_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1);
    v___x_4060_ = l_Lean_MessageData_ofName(v_attrName_4054_);
    v___x_4061_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4061_, 0, v___x_4059_);
    leanh::lean_ctor_set(v___x_4061_, 1, v___x_4060_);
    v___x_4062_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3_once), _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3);
    v___x_4063_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4063_, 0, v___x_4061_);
    leanh::lean_ctor_set(v___x_4063_, 1, v___x_4062_);
    v___x_4064_ = 0;
    v___x_4065_ = l_Lean_MessageData_ofConstName(v_declName_4055_, v___x_4064_);
    v___x_4066_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4066_, 0, v___x_4063_);
    leanh::lean_ctor_set(v___x_4066_, 1, v___x_4065_);
    v___x_4067_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__1___redArg___closed__1);
    v___x_4068_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4068_, 0, v___x_4066_);
    leanh::lean_ctor_set(v___x_4068_, 1, v___x_4067_);
    v___x_4069_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__6_spec__8___redArg(v___x_4068_, v___y_4056_, v___y_4057_);
    return v___x_4069_;
}
pub unsafe fn l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__1___redArg___boxed(
    mut v_attrName_4070_: *mut leanh::LeanObject,
    mut v_declName_4071_: *mut leanh::LeanObject,
    mut v___y_4072_: *mut leanh::LeanObject,
    mut v___y_4073_: *mut leanh::LeanObject,
    mut v___y_4074_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4075_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4075_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__1___redArg(v_attrName_4070_, v_declName_4071_, v___y_4072_, v___y_4073_);
    leanh::lean_dec(v___y_4073_);
    leanh::lean_dec_ref(v___y_4072_);
    return v_res_4075_;
}
pub unsafe fn l_Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0(
    mut v_attr_4076_: *mut leanh::LeanObject,
    mut v_decl_4077_: *mut leanh::LeanObject,
    mut v___y_4078_: *mut leanh::LeanObject,
    mut v___y_4079_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ext_4084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_4085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4096_: u8 = 0;
    let mut v_asyncMode_4097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4106_: u8 = 0;
    let mut v_unused_4107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ext_4113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_4114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_attr_4115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_4116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4117_: u8 = 0;
    let mut v_toAttributeImplCore_4118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_4119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_attr_4123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toAttributeImplCore_4124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_4125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4108_ = lean_st_ref_get(v___y_4079_);
                v_env_4109_ = leanh::lean_ctor_get(v___x_4108_, 0);
                leanh::lean_inc_ref(v_env_4109_);
                leanh::lean_dec(v___x_4108_);
                v___x_4122_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4109_, v_decl_4077_);
                if leanh::lean_obj_tag(v___x_4122_) == 0 {
                    v___y_4111_ = v___y_4078_;
                    v___y_4112_ = v___y_4079_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_dec_ref_known(v___x_4122_, 1);
                    leanh::lean_dec_ref(v_env_4109_);
                    v_attr_4123_ = leanh::lean_ctor_get(v_attr_4076_, 0);
                    leanh::lean_inc_ref(v_attr_4123_);
                    leanh::lean_dec_ref(v_attr_4076_);
                    v_toAttributeImplCore_4124_ = leanh::lean_ctor_get(v_attr_4123_, 0);
                    leanh::lean_inc_ref(v_toAttributeImplCore_4124_);
                    leanh::lean_dec_ref(v_attr_4123_);
                    v_name_4125_ = leanh::lean_ctor_get(v_toAttributeImplCore_4124_, 1);
                    leanh::lean_inc(v_name_4125_);
                    leanh::lean_dec_ref(v_toAttributeImplCore_4124_);
                    v___x_4126_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__1___redArg(v_name_4125_, v_decl_4077_, v___y_4078_, v___y_4079_);
                    return v___x_4126_;
                }
            }
            1 => {
                v___x_4083_ = lean_st_ref_take(v___y_4082_);
                v_ext_4084_ = leanh::lean_ctor_get(v_attr_4076_, 1);
                leanh::lean_inc_ref(v_ext_4084_);
                leanh::lean_dec_ref(v_attr_4076_);
                v_toEnvExtension_4085_ = leanh::lean_ctor_get(v_ext_4084_, 0);
                v_env_4086_ = leanh::lean_ctor_get(v___x_4083_, 0);
                v_nextMacroScope_4087_ = leanh::lean_ctor_get(v___x_4083_, 1);
                v_ngen_4088_ = leanh::lean_ctor_get(v___x_4083_, 2);
                v_auxDeclNGen_4089_ = leanh::lean_ctor_get(v___x_4083_, 3);
                v_traceState_4090_ = leanh::lean_ctor_get(v___x_4083_, 4);
                v_messages_4091_ = leanh::lean_ctor_get(v___x_4083_, 6);
                v_infoState_4092_ = leanh::lean_ctor_get(v___x_4083_, 7);
                v_snapshotTasks_4093_ = leanh::lean_ctor_get(v___x_4083_, 8);
                v_isSharedCheck_4106_ = (!leanh::lean_is_exclusive(v___x_4083_)) as u8;
                if v_isSharedCheck_4106_ == 0 {
                    v_unused_4107_ = leanh::lean_ctor_get(v___x_4083_, 5);
                    leanh::lean_dec(v_unused_4107_);
                    v___x_4095_ = v___x_4083_;
                    v_isShared_4096_ = v_isSharedCheck_4106_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_4093_);
                    leanh::lean_inc(v_infoState_4092_);
                    leanh::lean_inc(v_messages_4091_);
                    leanh::lean_inc(v_traceState_4090_);
                    leanh::lean_inc(v_auxDeclNGen_4089_);
                    leanh::lean_inc(v_ngen_4088_);
                    leanh::lean_inc(v_nextMacroScope_4087_);
                    leanh::lean_inc(v_env_4086_);
                    leanh::lean_dec(v___x_4083_);
                    v___x_4095_ = leanh::lean_box(0);
                    v_isShared_4096_ = v_isSharedCheck_4106_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_asyncMode_4097_ = leanh::lean_ctor_get(v_toEnvExtension_4085_, 2);
                leanh::lean_inc(v_asyncMode_4097_);
                leanh::lean_inc(v_decl_4077_);
                v___x_4098_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                    v_ext_4084_,
                    v_env_4086_,
                    v_decl_4077_,
                    v_asyncMode_4097_,
                    v_decl_4077_,
                );
                leanh::lean_dec(v_asyncMode_4097_);
                v___x_4099_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__4
                    ),
                    core::ptr::addr_of_mut!(
                        l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__4_once
                    ),
                    _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__4,
                );
                if v_isShared_4096_ == 0 {
                    leanh::lean_ctor_set(v___x_4095_, 5, v___x_4099_);
                    leanh::lean_ctor_set(v___x_4095_, 0, v___x_4098_);
                    v___x_4101_ = v___x_4095_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4105_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4105_, 0, v___x_4098_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4105_, 1, v_nextMacroScope_4087_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4105_, 2, v_ngen_4088_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4105_, 3, v_auxDeclNGen_4089_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4105_, 4, v_traceState_4090_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4105_, 5, v___x_4099_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4105_, 6, v_messages_4091_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4105_, 7, v_infoState_4092_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4105_, 8, v_snapshotTasks_4093_);
                    v___x_4101_ = v_reuseFailAlloc_4105_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4102_ = lean_st_ref_set(v___y_4082_, v___x_4101_);
                v___x_4103_ = leanh::lean_box(0);
                v___x_4104_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4104_, 0, v___x_4103_);
                return v___x_4104_;
            }
            4 => {
                v_ext_4113_ = leanh::lean_ctor_get(v_attr_4076_, 1);
                v_toEnvExtension_4114_ = leanh::lean_ctor_get(v_ext_4113_, 0);
                v_attr_4115_ = leanh::lean_ctor_get(v_attr_4076_, 0);
                v_asyncMode_4116_ = leanh::lean_ctor_get(v_toEnvExtension_4114_, 2);
                leanh::lean_inc(v_decl_4077_);
                leanh::lean_inc_ref(v_env_4109_);
                v___x_4117_ = l_Lean_EnvExtension_asyncMayModify___redArg(
                    v_env_4109_,
                    v_decl_4077_,
                    v_asyncMode_4116_,
                );
                if v___x_4117_ == 0 {
                    leanh::lean_inc_ref(v_attr_4115_);
                    leanh::lean_dec_ref(v_attr_4076_);
                    v_toAttributeImplCore_4118_ = leanh::lean_ctor_get(v_attr_4115_, 0);
                    leanh::lean_inc_ref(v_toAttributeImplCore_4118_);
                    leanh::lean_dec_ref(v_attr_4115_);
                    v_name_4119_ = leanh::lean_ctor_get(v_toAttributeImplCore_4118_, 1);
                    leanh::lean_inc(v_name_4119_);
                    leanh::lean_dec_ref(v_toAttributeImplCore_4118_);
                    v___x_4120_ = l_Lean_Environment_asyncPrefix_x3f(v_env_4109_);
                    v___x_4121_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__0___redArg(v_name_4119_, v_decl_4077_, v___x_4120_, v___y_4111_, v___y_4112_);
                    return v___x_4121_;
                } else {
                    leanh::lean_dec_ref(v_env_4109_);
                    v___y_4082_ = v___y_4112_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0___boxed(
    mut v_attr_4127_: *mut leanh::LeanObject,
    mut v_decl_4128_: *mut leanh::LeanObject,
    mut v___y_4129_: *mut leanh::LeanObject,
    mut v___y_4130_: *mut leanh::LeanObject,
    mut v___y_4131_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4132_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4132_ = l_Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0(v_attr_4127_, v_decl_4128_, v___y_4129_, v___y_4130_);
    leanh::lean_dec(v___y_4130_);
    leanh::lean_dec_ref(v___y_4129_);
    return v_res_4132_;
}
pub unsafe fn l___private_Lean_DefEqAttrib_0__Lean_initFn___lam__0_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2_(
    mut v_declName_4133_: *mut leanh::LeanObject,
    mut v___y_4134_: *mut leanh::LeanObject,
    mut v___y_4135_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4137_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_declName_4133_);
    v___x_4137_ = l_Lean_validateDefEqAttr(v_declName_4133_, v___y_4134_, v___y_4135_);
    if leanh::lean_obj_tag(v___x_4137_) == 0 {
        let mut v___x_4138_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4139_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref_known(v___x_4137_, 1);
        v___x_4138_ = l_Lean_backwardDefeqAttr;
        v___x_4139_ = l_Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0(v___x_4138_, v_declName_4133_, v___y_4134_, v___y_4135_);
        return v___x_4139_;
    } else {
        leanh::lean_dec(v_declName_4133_);
        return v___x_4137_;
    }
}
pub unsafe fn l___private_Lean_DefEqAttrib_0__Lean_initFn___lam__0_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2____boxed(
    mut v_declName_4140_: *mut leanh::LeanObject,
    mut v___y_4141_: *mut leanh::LeanObject,
    mut v___y_4142_: *mut leanh::LeanObject,
    mut v___y_4143_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4144_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4144_ = l___private_Lean_DefEqAttrib_0__Lean_initFn___lam__0_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2_(v_declName_4140_, v___y_4141_, v___y_4142_);
    leanh::lean_dec(v___y_4142_);
    leanh::lean_dec_ref(v___y_4141_);
    return v_res_4144_;
}
pub unsafe fn l___private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___f_4155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4159_: u8 = 0;
    let mut v___x_4160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4161_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_4155_ = l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__0_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2_;
    v___x_4156_ = l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__2_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2_;
    v___x_4157_ = l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__3_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2_;
    v___x_4158_ = l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__5_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2_;
    v___x_4159_ = 0;
    v___x_4160_ = l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__6_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_;
    v___x_4161_ = l_Lean_registerTagAttribute(
        v___x_4156_,
        v___x_4157_,
        v___f_4155_,
        v___x_4158_,
        v___x_4159_,
        v___x_4160_,
    );
    return v___x_4161_;
}
pub unsafe fn l___private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2____boxed(
    mut v_a_4162_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4163_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4163_ = l___private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2_();
    return v_res_4163_;
}
pub unsafe fn l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__0(
    mut v_00_u03b1_4164_: *mut leanh::LeanObject,
    mut v_attrName_4165_: *mut leanh::LeanObject,
    mut v_declName_4166_: *mut leanh::LeanObject,
    mut v_asyncPrefix_x3f_4167_: *mut leanh::LeanObject,
    mut v___y_4168_: *mut leanh::LeanObject,
    mut v___y_4169_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4171_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4171_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__0___redArg(v_attrName_4165_, v_declName_4166_, v_asyncPrefix_x3f_4167_, v___y_4168_, v___y_4169_);
    return v___x_4171_;
}
pub unsafe fn l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__0___boxed(
    mut v_00_u03b1_4172_: *mut leanh::LeanObject,
    mut v_attrName_4173_: *mut leanh::LeanObject,
    mut v_declName_4174_: *mut leanh::LeanObject,
    mut v_asyncPrefix_x3f_4175_: *mut leanh::LeanObject,
    mut v___y_4176_: *mut leanh::LeanObject,
    mut v___y_4177_: *mut leanh::LeanObject,
    mut v___y_4178_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4179_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4179_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b1_4172_, v_attrName_4173_, v_declName_4174_, v_asyncPrefix_x3f_4175_, v___y_4176_, v___y_4177_);
    leanh::lean_dec(v___y_4177_);
    leanh::lean_dec_ref(v___y_4176_);
    return v_res_4179_;
}
pub unsafe fn l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__1(
    mut v_00_u03b1_4180_: *mut leanh::LeanObject,
    mut v_attrName_4181_: *mut leanh::LeanObject,
    mut v_declName_4182_: *mut leanh::LeanObject,
    mut v___y_4183_: *mut leanh::LeanObject,
    mut v___y_4184_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4186_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4186_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__1___redArg(v_attrName_4181_, v_declName_4182_, v___y_4183_, v___y_4184_);
    return v___x_4186_;
}
pub unsafe fn l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__1___boxed(
    mut v_00_u03b1_4187_: *mut leanh::LeanObject,
    mut v_attrName_4188_: *mut leanh::LeanObject,
    mut v_declName_4189_: *mut leanh::LeanObject,
    mut v___y_4190_: *mut leanh::LeanObject,
    mut v___y_4191_: *mut leanh::LeanObject,
    mut v___y_4192_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4193_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4193_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__1(v_00_u03b1_4187_, v_attrName_4188_, v_declName_4189_, v___y_4190_, v___y_4191_);
    leanh::lean_dec(v___y_4191_);
    leanh::lean_dec_ref(v___y_4190_);
    return v_res_4193_;
}
pub unsafe fn l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_docString__1()
-> *mut leanh::LeanObject {
    let mut v___x_4196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4198_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4196_ = l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__5_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2_;
    v___x_4197_ = l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_docString__1___closed__0;
    v___x_4198_ = l_Lean_addBuiltinDocString(v___x_4196_, v___x_4197_);
    return v___x_4198_;
}
pub unsafe fn l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_docString__1___boxed(
    mut v_a_4199_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4200_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4200_ =
        l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_docString__1();
    return v_res_4200_;
}
pub unsafe fn l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3()
-> *mut leanh::LeanObject {
    let mut v___x_4227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4229_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4227_ = l___private_Lean_DefEqAttrib_0__Lean_initFn___closed__5_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2_;
    v___x_4228_ = l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__6;
    v___x_4229_ = l_Lean_addBuiltinDeclarationRanges(v___x_4227_, v___x_4228_);
    return v___x_4229_;
}
pub unsafe fn l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___boxed(
    mut v_a_4230_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4231_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4231_ =
        l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3();
    return v_res_4231_;
}
pub unsafe fn l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg(
    mut v_type_4243_: *mut leanh::LeanObject,
    mut v_proof_4244_: *mut leanh::LeanObject,
    mut v_a_4245_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_body_4247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4250_: u8 = 0;
    let mut v___x_4251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4255_: u8 = 0;
    let mut v___x_4256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4260_: u8 = 0;
    let mut v___x_4261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4262_: u8 = 0;
    let mut v___x_4263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4265_: u8 = 0;
    let mut v___x_4266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4267_: u8 = 0;
    let mut v___x_4268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4274_: u8 = 0;
    let mut v___x_4275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4276_: u8 = 0;
    let mut v___x_4277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_type_4243_) == 7 {
                    if leanh::lean_obj_tag(v_proof_4244_) == 6 {
                        v_body_4247_ = leanh::lean_ctor_get(v_type_4243_, 2);
                        v_body_4248_ = leanh::lean_ctor_get(v_proof_4244_, 2);
                        leanh::lean_inc_ref(v_body_4248_);
                        leanh::lean_dec_ref_known(v_proof_4244_, 3);
                        v_type_4243_ = v_body_4247_;
                        v_proof_4244_ = v_body_4248_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_proof_4244_);
                        v___x_4250_ = 0;
                        v___x_4251_ = leanh::lean_box((v___x_4250_) as usize);
                        v___x_4252_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_4252_, 0, v___x_4251_);
                        return v___x_4252_;
                    }
                } else {
                    v___x_4253_ = l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg___lam__0___closed__1;
                    v___x_4254_ = leanh::lean_unsigned_to_nat(3);
                    v___x_4255_ = l_Lean_Expr_isAppOfArity(v_type_4243_, v___x_4253_, v___x_4254_);
                    if v___x_4255_ == 0 {
                        leanh::lean_dec_ref(v_proof_4244_);
                        v___x_4256_ = leanh::lean_box((v___x_4255_) as usize);
                        v___x_4257_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_4257_, 0, v___x_4256_);
                        return v___x_4257_;
                    } else {
                        v___x_4258_ = l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__1;
                        v___x_4259_ = leanh::lean_unsigned_to_nat(2);
                        v___x_4260_ =
                            l_Lean_Expr_isAppOfArity(v_proof_4244_, v___x_4258_, v___x_4259_);
                        if v___x_4260_ == 0 {
                            v___x_4261_ = l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__3;
                            v___x_4262_ =
                                l_Lean_Expr_isAppOfArity(v_proof_4244_, v___x_4261_, v___x_4259_);
                            if v___x_4262_ == 0 {
                                v___x_4263_ = l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__5;
                                v___x_4264_ = leanh::lean_unsigned_to_nat(4);
                                v___x_4265_ = l_Lean_Expr_isAppOfArity(
                                    v_proof_4244_,
                                    v___x_4263_,
                                    v___x_4264_,
                                );
                                if v___x_4265_ == 0 {
                                    v___x_4266_ = l_Lean_Expr_getAppFn(v_proof_4244_);
                                    leanh::lean_dec_ref(v_proof_4244_);
                                    v___x_4267_ = l_Lean_Expr_isConst(v___x_4266_);
                                    if v___x_4267_ == 0 {
                                        leanh::lean_dec_ref(v___x_4266_);
                                        v___x_4268_ =
                                            leanh::lean_box((v___x_4267_) as usize);
                                        v___x_4269_ =
                                            leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                        leanh::lean_ctor_set(v___x_4269_, 0, v___x_4268_);
                                        return v___x_4269_;
                                    } else {
                                        v___x_4270_ = lean_st_ref_get(v_a_4245_);
                                        v_env_4271_ = leanh::lean_ctor_get(v___x_4270_, 0);
                                        leanh::lean_inc_ref_n(v_env_4271_, 2);
                                        leanh::lean_dec(v___x_4270_);
                                        v___x_4272_ = l_Lean_Expr_constName_x21(v___x_4266_);
                                        leanh::lean_dec_ref(v___x_4266_);
                                        v___x_4273_ = l_Lean_defeqAttr;
                                        leanh::lean_inc(v___x_4272_);
                                        v___x_4274_ = l_Lean_TagAttribute_hasTag(
                                            v___x_4273_,
                                            v_env_4271_,
                                            v___x_4272_,
                                        );
                                        if v___x_4274_ == 0 {
                                            v___x_4275_ = l_Lean_backwardDefeqAttr;
                                            v___x_4276_ = l_Lean_TagAttribute_hasTag(
                                                v___x_4275_,
                                                v_env_4271_,
                                                v___x_4272_,
                                            );
                                            v___x_4277_ =
                                                leanh::lean_box((v___x_4276_) as usize);
                                            v___x_4278_ =
                                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                            leanh::lean_ctor_set(
                                                v___x_4278_,
                                                0,
                                                v___x_4277_,
                                            );
                                            return v___x_4278_;
                                        } else {
                                            leanh::lean_dec(v___x_4272_);
                                            leanh::lean_dec_ref(v_env_4271_);
                                            v___x_4279_ =
                                                leanh::lean_box((v___x_4255_) as usize);
                                            v___x_4280_ =
                                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                            leanh::lean_ctor_set(
                                                v___x_4280_,
                                                0,
                                                v___x_4279_,
                                            );
                                            return v___x_4280_;
                                        }
                                    }
                                } else {
                                    v___x_4281_ = l_Lean_Expr_appArg_x21(v_proof_4244_);
                                    leanh::lean_dec_ref(v_proof_4244_);
                                    v_proof_4244_ = v___x_4281_;
                                    state = 0;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec_ref(v_proof_4244_);
                                v___x_4283_ = leanh::lean_box((v___x_4255_) as usize);
                                v___x_4284_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_4284_, 0, v___x_4283_);
                                return v___x_4284_;
                            }
                        } else {
                            leanh::lean_dec_ref(v_proof_4244_);
                            v___x_4285_ = leanh::lean_box((v___x_4255_) as usize);
                            v___x_4286_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_4286_, 0, v___x_4285_);
                            return v___x_4286_;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___boxed(
    mut v_type_4287_: *mut leanh::LeanObject,
    mut v_proof_4288_: *mut leanh::LeanObject,
    mut v_a_4289_: *mut leanh::LeanObject,
    mut v_a_4290_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4291_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4291_ = l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg(
        v_type_4287_,
        v_proof_4288_,
        v_a_4289_,
    );
    leanh::lean_dec(v_a_4289_);
    leanh::lean_dec_ref(v_type_4287_);
    return v_res_4291_;
}
pub unsafe fn l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore(
    mut v_type_4292_: *mut leanh::LeanObject,
    mut v_proof_4293_: *mut leanh::LeanObject,
    mut v_a_4294_: *mut leanh::LeanObject,
    mut v_a_4295_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4297_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4297_ = l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg(
        v_type_4292_,
        v_proof_4293_,
        v_a_4295_,
    );
    return v___x_4297_;
}
pub unsafe fn l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___boxed(
    mut v_type_4298_: *mut leanh::LeanObject,
    mut v_proof_4299_: *mut leanh::LeanObject,
    mut v_a_4300_: *mut leanh::LeanObject,
    mut v_a_4301_: *mut leanh::LeanObject,
    mut v_a_4302_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4303_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4303_ = l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore(
        v_type_4298_,
        v_proof_4299_,
        v_a_4300_,
        v_a_4301_,
    );
    leanh::lean_dec(v_a_4301_);
    leanh::lean_dec_ref(v_a_4300_);
    leanh::lean_dec_ref(v_type_4298_);
    return v_res_4303_;
}
pub unsafe fn l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__1___redArg(
    mut v_attrName_4304_: *mut leanh::LeanObject,
    mut v_declName_4305_: *mut leanh::LeanObject,
    mut v___y_4306_: *mut leanh::LeanObject,
    mut v___y_4307_: *mut leanh::LeanObject,
    mut v___y_4308_: *mut leanh::LeanObject,
    mut v___y_4309_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4316_: u8 = 0;
    let mut v___x_4317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4321_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4311_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1);
    v___x_4312_ = l_Lean_MessageData_ofName(v_attrName_4304_);
    v___x_4313_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4313_, 0, v___x_4311_);
    leanh::lean_ctor_set(v___x_4313_, 1, v___x_4312_);
    v___x_4314_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3_once), _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3);
    v___x_4315_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4315_, 0, v___x_4313_);
    leanh::lean_ctor_set(v___x_4315_, 1, v___x_4314_);
    v___x_4316_ = 0;
    v___x_4317_ = l_Lean_MessageData_ofConstName(v_declName_4305_, v___x_4316_);
    v___x_4318_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4318_, 0, v___x_4315_);
    leanh::lean_ctor_set(v___x_4318_, 1, v___x_4317_);
    v___x_4319_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__1___redArg___closed__1);
    v___x_4320_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4320_, 0, v___x_4318_);
    leanh::lean_ctor_set(v___x_4320_, 1, v___x_4319_);
    v___x_4321_ =
        l_Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0___redArg(
            v___x_4320_,
            v___y_4306_,
            v___y_4307_,
            v___y_4308_,
            v___y_4309_,
        );
    return v___x_4321_;
}
pub unsafe fn l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__1___redArg___boxed(
    mut v_attrName_4322_: *mut leanh::LeanObject,
    mut v_declName_4323_: *mut leanh::LeanObject,
    mut v___y_4324_: *mut leanh::LeanObject,
    mut v___y_4325_: *mut leanh::LeanObject,
    mut v___y_4326_: *mut leanh::LeanObject,
    mut v___y_4327_: *mut leanh::LeanObject,
    mut v___y_4328_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4329_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4329_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__1___redArg(v_attrName_4322_, v_declName_4323_, v___y_4324_, v___y_4325_, v___y_4326_, v___y_4327_);
    leanh::lean_dec(v___y_4327_);
    leanh::lean_dec_ref(v___y_4326_);
    leanh::lean_dec(v___y_4325_);
    leanh::lean_dec_ref(v___y_4324_);
    return v_res_4329_;
}
pub unsafe fn l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__0___redArg(
    mut v_attrName_4330_: *mut leanh::LeanObject,
    mut v_declName_4331_: *mut leanh::LeanObject,
    mut v_asyncPrefix_x3f_4332_: *mut leanh::LeanObject,
    mut v___y_4333_: *mut leanh::LeanObject,
    mut v___y_4334_: *mut leanh::LeanObject,
    mut v___y_4335_: *mut leanh::LeanObject,
    mut v___y_4336_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4345_: u8 = 0;
    let mut v___x_4346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_asyncPrefix_x3f_4332_) == 0 {
                    v___x_4352_ = l_Lean_MessageData_nil;
                    v___y_4339_ = v___x_4352_;
                    state = 1;
                    continue;
                } else {
                    v_val_4353_ = leanh::lean_ctor_get(v_asyncPrefix_x3f_4332_, 0);
                    leanh::lean_inc(v_val_4353_);
                    leanh::lean_dec_ref_known(v_asyncPrefix_x3f_4332_, 1);
                    v___x_4354_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__7_once), _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__7);
                    v___x_4355_ = l_Lean_MessageData_ofName(v_val_4353_);
                    v___x_4356_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4356_, 0, v___x_4354_);
                    leanh::lean_ctor_set(v___x_4356_, 1, v___x_4355_);
                    v___x_4357_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3);
                    v___x_4358_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4358_, 0, v___x_4356_);
                    leanh::lean_ctor_set(v___x_4358_, 1, v___x_4357_);
                    v___y_4339_ = v___x_4358_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4340_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1);
                v___x_4341_ = l_Lean_MessageData_ofName(v_attrName_4330_);
                v___x_4342_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4342_, 0, v___x_4340_);
                leanh::lean_ctor_set(v___x_4342_, 1, v___x_4341_);
                v___x_4343_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3_once), _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__3);
                v___x_4344_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4344_, 0, v___x_4342_);
                leanh::lean_ctor_set(v___x_4344_, 1, v___x_4343_);
                v___x_4345_ = 0;
                v___x_4346_ = l_Lean_MessageData_ofConstName(v_declName_4331_, v___x_4345_);
                v___x_4347_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4347_, 0, v___x_4344_);
                leanh::lean_ctor_set(v___x_4347_, 1, v___x_4346_);
                v___x_4348_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__5_once), _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__5);
                v___x_4349_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4349_, 0, v___x_4347_);
                leanh::lean_ctor_set(v___x_4349_, 1, v___x_4348_);
                v___x_4350_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4350_, 0, v___x_4349_);
                leanh::lean_ctor_set(v___x_4350_, 1, v___y_4339_);
                v___x_4351_ = l_Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0___redArg(v___x_4350_, v___y_4333_, v___y_4334_, v___y_4335_, v___y_4336_);
                return v___x_4351_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__0___redArg___boxed(
    mut v_attrName_4359_: *mut leanh::LeanObject,
    mut v_declName_4360_: *mut leanh::LeanObject,
    mut v_asyncPrefix_x3f_4361_: *mut leanh::LeanObject,
    mut v___y_4362_: *mut leanh::LeanObject,
    mut v___y_4363_: *mut leanh::LeanObject,
    mut v___y_4364_: *mut leanh::LeanObject,
    mut v___y_4365_: *mut leanh::LeanObject,
    mut v___y_4366_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4367_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4367_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__0___redArg(v_attrName_4359_, v_declName_4360_, v_asyncPrefix_x3f_4361_, v___y_4362_, v___y_4363_, v___y_4364_, v___y_4365_);
    leanh::lean_dec(v___y_4365_);
    leanh::lean_dec_ref(v___y_4364_);
    leanh::lean_dec(v___y_4363_);
    leanh::lean_dec_ref(v___y_4362_);
    return v_res_4367_;
}
pub unsafe fn l_Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0(
    mut v_attr_4368_: *mut leanh::LeanObject,
    mut v_decl_4369_: *mut leanh::LeanObject,
    mut v___y_4370_: *mut leanh::LeanObject,
    mut v___y_4371_: *mut leanh::LeanObject,
    mut v___y_4372_: *mut leanh::LeanObject,
    mut v___y_4373_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ext_4379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_4380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4391_: u8 = 0;
    let mut v_asyncMode_4392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_4401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4405_: u8 = 0;
    let mut v___x_4406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4413_: u8 = 0;
    let mut v_unused_4414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4416_: u8 = 0;
    let mut v_unused_4417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ext_4425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_4426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_attr_4427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_4428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4429_: u8 = 0;
    let mut v_toAttributeImplCore_4430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_4431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_attr_4435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toAttributeImplCore_4436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_4437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4418_ = lean_st_ref_get(v___y_4373_);
                v_env_4419_ = leanh::lean_ctor_get(v___x_4418_, 0);
                leanh::lean_inc_ref(v_env_4419_);
                leanh::lean_dec(v___x_4418_);
                v___x_4434_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4419_, v_decl_4369_);
                if leanh::lean_obj_tag(v___x_4434_) == 0 {
                    v___y_4421_ = v___y_4370_;
                    v___y_4422_ = v___y_4371_;
                    v___y_4423_ = v___y_4372_;
                    v___y_4424_ = v___y_4373_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_dec_ref_known(v___x_4434_, 1);
                    leanh::lean_dec_ref(v_env_4419_);
                    v_attr_4435_ = leanh::lean_ctor_get(v_attr_4368_, 0);
                    leanh::lean_inc_ref(v_attr_4435_);
                    leanh::lean_dec_ref(v_attr_4368_);
                    v_toAttributeImplCore_4436_ = leanh::lean_ctor_get(v_attr_4435_, 0);
                    leanh::lean_inc_ref(v_toAttributeImplCore_4436_);
                    leanh::lean_dec_ref(v_attr_4435_);
                    v_name_4437_ = leanh::lean_ctor_get(v_toAttributeImplCore_4436_, 1);
                    leanh::lean_inc(v_name_4437_);
                    leanh::lean_dec_ref(v_toAttributeImplCore_4436_);
                    v___x_4438_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__1___redArg(v_name_4437_, v_decl_4369_, v___y_4370_, v___y_4371_, v___y_4372_, v___y_4373_);
                    return v___x_4438_;
                }
            }
            1 => {
                v___x_4378_ = lean_st_ref_take(v___y_4377_);
                v_ext_4379_ = leanh::lean_ctor_get(v_attr_4368_, 1);
                leanh::lean_inc_ref(v_ext_4379_);
                leanh::lean_dec_ref(v_attr_4368_);
                v_toEnvExtension_4380_ = leanh::lean_ctor_get(v_ext_4379_, 0);
                v_env_4381_ = leanh::lean_ctor_get(v___x_4378_, 0);
                v_nextMacroScope_4382_ = leanh::lean_ctor_get(v___x_4378_, 1);
                v_ngen_4383_ = leanh::lean_ctor_get(v___x_4378_, 2);
                v_auxDeclNGen_4384_ = leanh::lean_ctor_get(v___x_4378_, 3);
                v_traceState_4385_ = leanh::lean_ctor_get(v___x_4378_, 4);
                v_messages_4386_ = leanh::lean_ctor_get(v___x_4378_, 6);
                v_infoState_4387_ = leanh::lean_ctor_get(v___x_4378_, 7);
                v_snapshotTasks_4388_ = leanh::lean_ctor_get(v___x_4378_, 8);
                v_isSharedCheck_4416_ = (!leanh::lean_is_exclusive(v___x_4378_)) as u8;
                if v_isSharedCheck_4416_ == 0 {
                    v_unused_4417_ = leanh::lean_ctor_get(v___x_4378_, 5);
                    leanh::lean_dec(v_unused_4417_);
                    v___x_4390_ = v___x_4378_;
                    v_isShared_4391_ = v_isSharedCheck_4416_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_4388_);
                    leanh::lean_inc(v_infoState_4387_);
                    leanh::lean_inc(v_messages_4386_);
                    leanh::lean_inc(v_traceState_4385_);
                    leanh::lean_inc(v_auxDeclNGen_4384_);
                    leanh::lean_inc(v_ngen_4383_);
                    leanh::lean_inc(v_nextMacroScope_4382_);
                    leanh::lean_inc(v_env_4381_);
                    leanh::lean_dec(v___x_4378_);
                    v___x_4390_ = leanh::lean_box(0);
                    v_isShared_4391_ = v_isSharedCheck_4416_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_asyncMode_4392_ = leanh::lean_ctor_get(v_toEnvExtension_4380_, 2);
                leanh::lean_inc(v_asyncMode_4392_);
                leanh::lean_inc(v_decl_4369_);
                v___x_4393_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                    v_ext_4379_,
                    v_env_4381_,
                    v_decl_4369_,
                    v_asyncMode_4392_,
                    v_decl_4369_,
                );
                leanh::lean_dec(v_asyncMode_4392_);
                v___x_4394_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__4
                    ),
                    core::ptr::addr_of_mut!(
                        l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__4_once
                    ),
                    _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__4,
                );
                if v_isShared_4391_ == 0 {
                    leanh::lean_ctor_set(v___x_4390_, 5, v___x_4394_);
                    leanh::lean_ctor_set(v___x_4390_, 0, v___x_4393_);
                    v___x_4396_ = v___x_4390_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4415_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4415_, 0, v___x_4393_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4415_, 1, v_nextMacroScope_4382_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4415_, 2, v_ngen_4383_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4415_, 3, v_auxDeclNGen_4384_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4415_, 4, v_traceState_4385_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4415_, 5, v___x_4394_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4415_, 6, v_messages_4386_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4415_, 7, v_infoState_4387_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4415_, 8, v_snapshotTasks_4388_);
                    v___x_4396_ = v_reuseFailAlloc_4415_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4397_ = lean_st_ref_set(v___y_4377_, v___x_4396_);
                v___x_4398_ = lean_st_ref_take(v___y_4376_);
                v_mctx_4399_ = leanh::lean_ctor_get(v___x_4398_, 0);
                v_zetaDeltaFVarIds_4400_ = leanh::lean_ctor_get(v___x_4398_, 2);
                v_postponed_4401_ = leanh::lean_ctor_get(v___x_4398_, 3);
                v_diag_4402_ = leanh::lean_ctor_get(v___x_4398_, 4);
                v_isSharedCheck_4413_ = (!leanh::lean_is_exclusive(v___x_4398_)) as u8;
                if v_isSharedCheck_4413_ == 0 {
                    v_unused_4414_ = leanh::lean_ctor_get(v___x_4398_, 1);
                    leanh::lean_dec(v_unused_4414_);
                    v___x_4404_ = v___x_4398_;
                    v_isShared_4405_ = v_isSharedCheck_4413_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_4402_);
                    leanh::lean_inc(v_postponed_4401_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_4400_);
                    leanh::lean_inc(v_mctx_4399_);
                    leanh::lean_dec(v___x_4398_);
                    v___x_4404_ = leanh::lean_box(0);
                    v_isShared_4405_ = v_isSharedCheck_4413_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4406_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___closed__0);
                if v_isShared_4405_ == 0 {
                    leanh::lean_ctor_set(v___x_4404_, 1, v___x_4406_);
                    v___x_4408_ = v___x_4404_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4412_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4412_, 0, v_mctx_4399_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4412_, 1, v___x_4406_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4412_,
                        2,
                        v_zetaDeltaFVarIds_4400_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_4412_, 3, v_postponed_4401_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4412_, 4, v_diag_4402_);
                    v___x_4408_ = v_reuseFailAlloc_4412_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4409_ = lean_st_ref_set(v___y_4376_, v___x_4408_);
                v___x_4410_ = leanh::lean_box(0);
                v___x_4411_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4411_, 0, v___x_4410_);
                return v___x_4411_;
            }
            6 => {
                v_ext_4425_ = leanh::lean_ctor_get(v_attr_4368_, 1);
                v_toEnvExtension_4426_ = leanh::lean_ctor_get(v_ext_4425_, 0);
                v_attr_4427_ = leanh::lean_ctor_get(v_attr_4368_, 0);
                v_asyncMode_4428_ = leanh::lean_ctor_get(v_toEnvExtension_4426_, 2);
                leanh::lean_inc(v_decl_4369_);
                leanh::lean_inc_ref(v_env_4419_);
                v___x_4429_ = l_Lean_EnvExtension_asyncMayModify___redArg(
                    v_env_4419_,
                    v_decl_4369_,
                    v_asyncMode_4428_,
                );
                if v___x_4429_ == 0 {
                    leanh::lean_inc_ref(v_attr_4427_);
                    leanh::lean_dec_ref(v_attr_4368_);
                    v_toAttributeImplCore_4430_ = leanh::lean_ctor_get(v_attr_4427_, 0);
                    leanh::lean_inc_ref(v_toAttributeImplCore_4430_);
                    leanh::lean_dec_ref(v_attr_4427_);
                    v_name_4431_ = leanh::lean_ctor_get(v_toAttributeImplCore_4430_, 1);
                    leanh::lean_inc(v_name_4431_);
                    leanh::lean_dec_ref(v_toAttributeImplCore_4430_);
                    v___x_4432_ = l_Lean_Environment_asyncPrefix_x3f(v_env_4419_);
                    v___x_4433_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__0___redArg(v_name_4431_, v_decl_4369_, v___x_4432_, v___y_4421_, v___y_4422_, v___y_4423_, v___y_4424_);
                    return v___x_4433_;
                } else {
                    leanh::lean_dec_ref(v_env_4419_);
                    v___y_4376_ = v___y_4422_;
                    v___y_4377_ = v___y_4424_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0___boxed(
    mut v_attr_4439_: *mut leanh::LeanObject,
    mut v_decl_4440_: *mut leanh::LeanObject,
    mut v___y_4441_: *mut leanh::LeanObject,
    mut v___y_4442_: *mut leanh::LeanObject,
    mut v___y_4443_: *mut leanh::LeanObject,
    mut v___y_4444_: *mut leanh::LeanObject,
    mut v___y_4445_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4446_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4446_ = l_Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0(
        v_attr_4439_,
        v_decl_4440_,
        v___y_4441_,
        v___y_4442_,
        v___y_4443_,
        v___y_4444_,
    );
    leanh::lean_dec(v___y_4444_);
    leanh::lean_dec_ref(v___y_4443_);
    leanh::lean_dec(v___y_4442_);
    leanh::lean_dec_ref(v___y_4441_);
    return v_res_4446_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9_spec__11___redArg(
    mut v_msg_4447_: *mut leanh::LeanObject,
    mut v_declHint_4448_: *mut leanh::LeanObject,
    mut v___y_4449_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4453_: u8 = 0;
    let mut v_isExporting_4454_: u8 = 0;
    let mut v___x_4455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: u8 = 0;
    let mut v___x_4458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_4466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4478_: u8 = 0;
    let mut v___x_4479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_4482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4483_: u8 = 0;
    let mut v___x_4484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4510_: u8 = 0;
    let mut v___x_4511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4451_ = lean_st_ref_get(v___y_4449_);
                v_env_4452_ = leanh::lean_ctor_get(v___x_4451_, 0);
                leanh::lean_inc_ref(v_env_4452_);
                leanh::lean_dec(v___x_4451_);
                v___x_4453_ = l_Lean_Name_isAnonymous(v_declHint_4448_);
                if v___x_4453_ == 0 {
                    v_isExporting_4454_ = leanh::lean_ctor_get_uint8(
                        v_env_4452_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_4454_ == 0 {
                        leanh::lean_dec_ref(v_env_4452_);
                        leanh::lean_dec(v_declHint_4448_);
                        v___x_4455_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_4455_, 0, v_msg_4447_);
                        return v___x_4455_;
                    } else {
                        leanh::lean_inc_ref(v_env_4452_);
                        v___x_4456_ = l_Lean_Environment_setExporting(v_env_4452_, v___x_4453_);
                        leanh::lean_inc(v_declHint_4448_);
                        leanh::lean_inc_ref(v___x_4456_);
                        v___x_4457_ = l_Lean_Environment_contains(
                            v___x_4456_,
                            v_declHint_4448_,
                            v_isExporting_4454_,
                        );
                        if v___x_4457_ == 0 {
                            leanh::lean_dec_ref(v___x_4456_);
                            leanh::lean_dec_ref(v_env_4452_);
                            leanh::lean_dec(v_declHint_4448_);
                            v___x_4458_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_4458_, 0, v_msg_4447_);
                            return v___x_4458_;
                        } else {
                            v___x_4459_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__2);
                            v___x_4460_ = leanh::lean_unsigned_to_nat(32);
                            v___x_4461_ = lean_mk_empty_array_with_capacity(v___x_4460_);
                            leanh::lean_dec_ref(v___x_4461_);
                            v___x_4462_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__5);
                            v___x_4463_ = l_Lean_Options_empty;
                            v___x_4464_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            leanh::lean_ctor_set(v___x_4464_, 0, v___x_4456_);
                            leanh::lean_ctor_set(v___x_4464_, 1, v___x_4459_);
                            leanh::lean_ctor_set(v___x_4464_, 2, v___x_4462_);
                            leanh::lean_ctor_set(v___x_4464_, 3, v___x_4463_);
                            leanh::lean_inc(v_declHint_4448_);
                            v___x_4465_ =
                                l_Lean_MessageData_ofConstName(v_declHint_4448_, v___x_4453_);
                            v_c_4466_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            leanh::lean_ctor_set(v_c_4466_, 0, v___x_4464_);
                            leanh::lean_ctor_set(v_c_4466_, 1, v___x_4465_);
                            v___x_4467_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_4452_,
                                v_declHint_4448_,
                            );
                            if leanh::lean_obj_tag(v___x_4467_) == 0 {
                                leanh::lean_dec_ref(v_env_4452_);
                                leanh::lean_dec(v_declHint_4448_);
                                v___x_4468_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7);
                                v___x_4469_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_4469_, 0, v___x_4468_);
                                leanh::lean_ctor_set(v___x_4469_, 1, v_c_4466_);
                                v___x_4470_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__9);
                                v___x_4471_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_4471_, 0, v___x_4469_);
                                leanh::lean_ctor_set(v___x_4471_, 1, v___x_4470_);
                                v___x_4472_ = l_Lean_MessageData_note(v___x_4471_);
                                v___x_4473_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_4473_, 0, v_msg_4447_);
                                leanh::lean_ctor_set(v___x_4473_, 1, v___x_4472_);
                                v___x_4474_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_4474_, 0, v___x_4473_);
                                return v___x_4474_;
                            } else {
                                v_val_4475_ = leanh::lean_ctor_get(v___x_4467_, 0);
                                v_isSharedCheck_4510_ =
                                    (!leanh::lean_is_exclusive(v___x_4467_)) as u8;
                                if v_isSharedCheck_4510_ == 0 {
                                    v___x_4477_ = v___x_4467_;
                                    v_isShared_4478_ = v_isSharedCheck_4510_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_val_4475_);
                                    leanh::lean_dec(v___x_4467_);
                                    v___x_4477_ = leanh::lean_box(0);
                                    v_isShared_4478_ = v_isSharedCheck_4510_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_env_4452_);
                    leanh::lean_dec(v_declHint_4448_);
                    v___x_4511_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4511_, 0, v_msg_4447_);
                    return v___x_4511_;
                }
            }
            1 => {
                v___x_4479_ = leanh::lean_box(0);
                v___x_4480_ = l_Lean_Environment_header(v_env_4452_);
                leanh::lean_dec_ref(v_env_4452_);
                v___x_4481_ = l_Lean_EnvironmentHeader_moduleNames(v___x_4480_);
                v_mod_4482_ = lean_array_get(v___x_4479_, v___x_4481_, v_val_4475_);
                leanh::lean_dec(v_val_4475_);
                leanh::lean_dec_ref(v___x_4481_);
                v___x_4483_ = l_Lean_isPrivateName(v_declHint_4448_);
                leanh::lean_dec(v_declHint_4448_);
                if v___x_4483_ == 0 {
                    v___x_4484_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__11);
                    v___x_4485_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4485_, 0, v___x_4484_);
                    leanh::lean_ctor_set(v___x_4485_, 1, v_c_4466_);
                    v___x_4486_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__13);
                    v___x_4487_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4487_, 0, v___x_4485_);
                    leanh::lean_ctor_set(v___x_4487_, 1, v___x_4486_);
                    v___x_4488_ = l_Lean_MessageData_ofName(v_mod_4482_);
                    v___x_4489_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4489_, 0, v___x_4487_);
                    leanh::lean_ctor_set(v___x_4489_, 1, v___x_4488_);
                    v___x_4490_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__15);
                    v___x_4491_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4491_, 0, v___x_4489_);
                    leanh::lean_ctor_set(v___x_4491_, 1, v___x_4490_);
                    v___x_4492_ = l_Lean_MessageData_note(v___x_4491_);
                    v___x_4493_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4493_, 0, v_msg_4447_);
                    leanh::lean_ctor_set(v___x_4493_, 1, v___x_4492_);
                    if v_isShared_4478_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_4477_, 0);
                        leanh::lean_ctor_set(v___x_4477_, 0, v___x_4493_);
                        v___x_4495_ = v___x_4477_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4496_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4496_, 0, v___x_4493_);
                        v___x_4495_ = v_reuseFailAlloc_4496_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_4497_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7);
                    v___x_4498_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4498_, 0, v___x_4497_);
                    leanh::lean_ctor_set(v___x_4498_, 1, v_c_4466_);
                    v___x_4499_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__17);
                    v___x_4500_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4500_, 0, v___x_4498_);
                    leanh::lean_ctor_set(v___x_4500_, 1, v___x_4499_);
                    v___x_4501_ = l_Lean_MessageData_ofName(v_mod_4482_);
                    v___x_4502_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4502_, 0, v___x_4500_);
                    leanh::lean_ctor_set(v___x_4502_, 1, v___x_4501_);
                    v___x_4503_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__19);
                    v___x_4504_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4504_, 0, v___x_4502_);
                    leanh::lean_ctor_set(v___x_4504_, 1, v___x_4503_);
                    v___x_4505_ = l_Lean_MessageData_note(v___x_4504_);
                    v___x_4506_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4506_, 0, v_msg_4447_);
                    leanh::lean_ctor_set(v___x_4506_, 1, v___x_4505_);
                    if v_isShared_4478_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_4477_, 0);
                        leanh::lean_ctor_set(v___x_4477_, 0, v___x_4506_);
                        v___x_4508_ = v___x_4477_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4509_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4509_, 0, v___x_4506_);
                        v___x_4508_ = v_reuseFailAlloc_4509_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4495_;
            }
            3 => {
                return v___x_4508_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9_spec__11___redArg___boxed(
    mut v_msg_4512_: *mut leanh::LeanObject,
    mut v_declHint_4513_: *mut leanh::LeanObject,
    mut v___y_4514_: *mut leanh::LeanObject,
    mut v___y_4515_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4516_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4516_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9_spec__11___redArg(v_msg_4512_, v_declHint_4513_, v___y_4514_);
    leanh::lean_dec(v___y_4514_);
    return v_res_4516_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9(
    mut v_msg_4517_: *mut leanh::LeanObject,
    mut v_declHint_4518_: *mut leanh::LeanObject,
    mut v___y_4519_: *mut leanh::LeanObject,
    mut v___y_4520_: *mut leanh::LeanObject,
    mut v___y_4521_: *mut leanh::LeanObject,
    mut v___y_4522_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4528_: u8 = 0;
    let mut v___x_4529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4534_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4524_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9_spec__11___redArg(v_msg_4517_, v_declHint_4518_, v___y_4522_);
                v_a_4525_ = leanh::lean_ctor_get(v___x_4524_, 0);
                v_isSharedCheck_4534_ = (!leanh::lean_is_exclusive(v___x_4524_)) as u8;
                if v_isSharedCheck_4534_ == 0 {
                    v___x_4527_ = v___x_4524_;
                    v_isShared_4528_ = v_isSharedCheck_4534_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_4525_);
                    leanh::lean_dec(v___x_4524_);
                    v___x_4527_ = leanh::lean_box(0);
                    v_isShared_4528_ = v_isSharedCheck_4534_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4529_ = l_Lean_unknownIdentifierMessageTag;
                v___x_4530_ = leanh::lean_alloc_ctor(8, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4530_, 0, v___x_4529_);
                leanh::lean_ctor_set(v___x_4530_, 1, v_a_4525_);
                if v_isShared_4528_ == 0 {
                    leanh::lean_ctor_set(v___x_4527_, 0, v___x_4530_);
                    v___x_4532_ = v___x_4527_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4533_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4533_, 0, v___x_4530_);
                    v___x_4532_ = v_reuseFailAlloc_4533_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4532_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9___boxed(
    mut v_msg_4535_: *mut leanh::LeanObject,
    mut v_declHint_4536_: *mut leanh::LeanObject,
    mut v___y_4537_: *mut leanh::LeanObject,
    mut v___y_4538_: *mut leanh::LeanObject,
    mut v___y_4539_: *mut leanh::LeanObject,
    mut v___y_4540_: *mut leanh::LeanObject,
    mut v___y_4541_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4542_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4542_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9(v_msg_4535_, v_declHint_4536_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_);
    leanh::lean_dec(v___y_4540_);
    leanh::lean_dec_ref(v___y_4539_);
    leanh::lean_dec(v___y_4538_);
    leanh::lean_dec_ref(v___y_4537_);
    return v_res_4542_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__10___redArg(
    mut v_ref_4543_: *mut leanh::LeanObject,
    mut v_msg_4544_: *mut leanh::LeanObject,
    mut v___y_4545_: *mut leanh::LeanObject,
    mut v___y_4546_: *mut leanh::LeanObject,
    mut v___y_4547_: *mut leanh::LeanObject,
    mut v___y_4548_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_4550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_4554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_4558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_4559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4562_: u8 = 0;
    let mut v_cancelTk_x3f_4563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4564_: u8 = 0;
    let mut v_inheritedTraceOptions_4565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4568_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fileName_4550_ = leanh::lean_ctor_get(v___y_4547_, 0);
    v_fileMap_4551_ = leanh::lean_ctor_get(v___y_4547_, 1);
    v_options_4552_ = leanh::lean_ctor_get(v___y_4547_, 2);
    v_currRecDepth_4553_ = leanh::lean_ctor_get(v___y_4547_, 3);
    v_maxRecDepth_4554_ = leanh::lean_ctor_get(v___y_4547_, 4);
    v_ref_4555_ = leanh::lean_ctor_get(v___y_4547_, 5);
    v_currNamespace_4556_ = leanh::lean_ctor_get(v___y_4547_, 6);
    v_openDecls_4557_ = leanh::lean_ctor_get(v___y_4547_, 7);
    v_initHeartbeats_4558_ = leanh::lean_ctor_get(v___y_4547_, 8);
    v_maxHeartbeats_4559_ = leanh::lean_ctor_get(v___y_4547_, 9);
    v_quotContext_4560_ = leanh::lean_ctor_get(v___y_4547_, 10);
    v_currMacroScope_4561_ = leanh::lean_ctor_get(v___y_4547_, 11);
    v_diag_4562_ = leanh::lean_ctor_get_uint8(
        v___y_4547_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_4563_ = leanh::lean_ctor_get(v___y_4547_, 12);
    v_suppressElabErrors_4564_ = leanh::lean_ctor_get_uint8(
        v___y_4547_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_4565_ = leanh::lean_ctor_get(v___y_4547_, 13);
    v_ref_4566_ = l_Lean_replaceRef(v_ref_4543_, v_ref_4555_);
    leanh::lean_inc_ref(v_inheritedTraceOptions_4565_);
    leanh::lean_inc(v_cancelTk_x3f_4563_);
    leanh::lean_inc(v_currMacroScope_4561_);
    leanh::lean_inc(v_quotContext_4560_);
    leanh::lean_inc(v_maxHeartbeats_4559_);
    leanh::lean_inc(v_initHeartbeats_4558_);
    leanh::lean_inc(v_openDecls_4557_);
    leanh::lean_inc(v_currNamespace_4556_);
    leanh::lean_inc(v_maxRecDepth_4554_);
    leanh::lean_inc(v_currRecDepth_4553_);
    leanh::lean_inc_ref(v_options_4552_);
    leanh::lean_inc_ref(v_fileMap_4551_);
    leanh::lean_inc_ref(v_fileName_4550_);
    v___x_4567_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
    leanh::lean_ctor_set(v___x_4567_, 0, v_fileName_4550_);
    leanh::lean_ctor_set(v___x_4567_, 1, v_fileMap_4551_);
    leanh::lean_ctor_set(v___x_4567_, 2, v_options_4552_);
    leanh::lean_ctor_set(v___x_4567_, 3, v_currRecDepth_4553_);
    leanh::lean_ctor_set(v___x_4567_, 4, v_maxRecDepth_4554_);
    leanh::lean_ctor_set(v___x_4567_, 5, v_ref_4566_);
    leanh::lean_ctor_set(v___x_4567_, 6, v_currNamespace_4556_);
    leanh::lean_ctor_set(v___x_4567_, 7, v_openDecls_4557_);
    leanh::lean_ctor_set(v___x_4567_, 8, v_initHeartbeats_4558_);
    leanh::lean_ctor_set(v___x_4567_, 9, v_maxHeartbeats_4559_);
    leanh::lean_ctor_set(v___x_4567_, 10, v_quotContext_4560_);
    leanh::lean_ctor_set(v___x_4567_, 11, v_currMacroScope_4561_);
    leanh::lean_ctor_set(v___x_4567_, 12, v_cancelTk_x3f_4563_);
    leanh::lean_ctor_set(v___x_4567_, 13, v_inheritedTraceOptions_4565_);
    leanh::lean_ctor_set_uint8(
        v___x_4567_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
        v_diag_4562_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_4567_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_4564_,
    );
    v___x_4568_ =
        l_Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0___redArg(
            v_msg_4544_,
            v___y_4545_,
            v___y_4546_,
            v___x_4567_,
            v___y_4548_,
        );
    leanh::lean_dec_ref_known(v___x_4567_, 14);
    return v___x_4568_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__10___redArg___boxed(
    mut v_ref_4569_: *mut leanh::LeanObject,
    mut v_msg_4570_: *mut leanh::LeanObject,
    mut v___y_4571_: *mut leanh::LeanObject,
    mut v___y_4572_: *mut leanh::LeanObject,
    mut v___y_4573_: *mut leanh::LeanObject,
    mut v___y_4574_: *mut leanh::LeanObject,
    mut v___y_4575_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4576_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4576_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__10___redArg(v_ref_4569_, v_msg_4570_, v___y_4571_, v___y_4572_, v___y_4573_, v___y_4574_);
    leanh::lean_dec(v___y_4574_);
    leanh::lean_dec_ref(v___y_4573_);
    leanh::lean_dec(v___y_4572_);
    leanh::lean_dec_ref(v___y_4571_);
    leanh::lean_dec(v_ref_4569_);
    return v_res_4576_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7___redArg(
    mut v_ref_4577_: *mut leanh::LeanObject,
    mut v_msg_4578_: *mut leanh::LeanObject,
    mut v_declHint_4579_: *mut leanh::LeanObject,
    mut v___y_4580_: *mut leanh::LeanObject,
    mut v___y_4581_: *mut leanh::LeanObject,
    mut v___y_4582_: *mut leanh::LeanObject,
    mut v___y_4583_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4587_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4585_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9(v_msg_4578_, v_declHint_4579_, v___y_4580_, v___y_4581_, v___y_4582_, v___y_4583_);
    v_a_4586_ = leanh::lean_ctor_get(v___x_4585_, 0);
    leanh::lean_inc(v_a_4586_);
    leanh::lean_dec_ref(v___x_4585_);
    v___x_4587_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__10___redArg(v_ref_4577_, v_a_4586_, v___y_4580_, v___y_4581_, v___y_4582_, v___y_4583_);
    return v___x_4587_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7___redArg___boxed(
    mut v_ref_4588_: *mut leanh::LeanObject,
    mut v_msg_4589_: *mut leanh::LeanObject,
    mut v_declHint_4590_: *mut leanh::LeanObject,
    mut v___y_4591_: *mut leanh::LeanObject,
    mut v___y_4592_: *mut leanh::LeanObject,
    mut v___y_4593_: *mut leanh::LeanObject,
    mut v___y_4594_: *mut leanh::LeanObject,
    mut v___y_4595_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4596_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4596_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7___redArg(v_ref_4588_, v_msg_4589_, v_declHint_4590_, v___y_4591_, v___y_4592_, v___y_4593_, v___y_4594_);
    leanh::lean_dec(v___y_4594_);
    leanh::lean_dec_ref(v___y_4593_);
    leanh::lean_dec(v___y_4592_);
    leanh::lean_dec_ref(v___y_4591_);
    leanh::lean_dec(v_ref_4588_);
    return v_res_4596_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3___redArg(
    mut v_ref_4597_: *mut leanh::LeanObject,
    mut v_constName_4598_: *mut leanh::LeanObject,
    mut v___y_4599_: *mut leanh::LeanObject,
    mut v___y_4600_: *mut leanh::LeanObject,
    mut v___y_4601_: *mut leanh::LeanObject,
    mut v___y_4602_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4605_: u8 = 0;
    let mut v___x_4606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4610_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4604_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__1);
    v___x_4605_ = 0;
    leanh::lean_inc(v_constName_4598_);
    v___x_4606_ = l_Lean_MessageData_ofConstName(v_constName_4598_, v___x_4605_);
    v___x_4607_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4607_, 0, v___x_4604_);
    leanh::lean_ctor_set(v___x_4607_, 1, v___x_4606_);
    v___x_4608_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_validateDefEqAttr_spec__1_spec__2_spec__3___redArg___closed__3);
    v___x_4609_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4609_, 0, v___x_4607_);
    leanh::lean_ctor_set(v___x_4609_, 1, v___x_4608_);
    v___x_4610_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7___redArg(v_ref_4597_, v___x_4609_, v_constName_4598_, v___y_4599_, v___y_4600_, v___y_4601_, v___y_4602_);
    return v___x_4610_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3___redArg___boxed(
    mut v_ref_4611_: *mut leanh::LeanObject,
    mut v_constName_4612_: *mut leanh::LeanObject,
    mut v___y_4613_: *mut leanh::LeanObject,
    mut v___y_4614_: *mut leanh::LeanObject,
    mut v___y_4615_: *mut leanh::LeanObject,
    mut v___y_4616_: *mut leanh::LeanObject,
    mut v___y_4617_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4618_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4618_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3___redArg(v_ref_4611_, v_constName_4612_, v___y_4613_, v___y_4614_, v___y_4615_, v___y_4616_);
    leanh::lean_dec(v___y_4616_);
    leanh::lean_dec_ref(v___y_4615_);
    leanh::lean_dec(v___y_4614_);
    leanh::lean_dec_ref(v___y_4613_);
    leanh::lean_dec(v_ref_4611_);
    return v_res_4618_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3___redArg(
    mut v_constName_4619_: *mut leanh::LeanObject,
    mut v___y_4620_: *mut leanh::LeanObject,
    mut v___y_4621_: *mut leanh::LeanObject,
    mut v___y_4622_: *mut leanh::LeanObject,
    mut v___y_4623_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_4625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4626_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_4625_ = leanh::lean_ctor_get(v___y_4622_, 5);
    v___x_4626_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3___redArg(v_ref_4625_, v_constName_4619_, v___y_4620_, v___y_4621_, v___y_4622_, v___y_4623_);
    return v___x_4626_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3___redArg___boxed(
    mut v_constName_4627_: *mut leanh::LeanObject,
    mut v___y_4628_: *mut leanh::LeanObject,
    mut v___y_4629_: *mut leanh::LeanObject,
    mut v___y_4630_: *mut leanh::LeanObject,
    mut v___y_4631_: *mut leanh::LeanObject,
    mut v___y_4632_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4633_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4633_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3___redArg(v_constName_4627_, v___y_4628_, v___y_4629_, v___y_4630_, v___y_4631_);
    leanh::lean_dec(v___y_4631_);
    leanh::lean_dec_ref(v___y_4630_);
    leanh::lean_dec(v___y_4629_);
    leanh::lean_dec_ref(v___y_4628_);
    return v_res_4633_;
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1(
    mut v_constName_4634_: *mut leanh::LeanObject,
    mut v___y_4635_: *mut leanh::LeanObject,
    mut v___y_4636_: *mut leanh::LeanObject,
    mut v___y_4637_: *mut leanh::LeanObject,
    mut v___y_4638_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4642_: u8 = 0;
    let mut v___x_4643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4648_: u8 = 0;
    let mut v___x_4650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4652_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4640_ = lean_st_ref_get(v___y_4638_);
                v_env_4641_ = leanh::lean_ctor_get(v___x_4640_, 0);
                leanh::lean_inc_ref(v_env_4641_);
                leanh::lean_dec(v___x_4640_);
                v___x_4642_ = 0;
                leanh::lean_inc(v_constName_4634_);
                v___x_4643_ =
                    l_Lean_Environment_find_x3f(v_env_4641_, v_constName_4634_, v___x_4642_);
                if leanh::lean_obj_tag(v___x_4643_) == 0 {
                    v___x_4644_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3___redArg(v_constName_4634_, v___y_4635_, v___y_4636_, v___y_4637_, v___y_4638_);
                    return v___x_4644_;
                } else {
                    leanh::lean_dec(v_constName_4634_);
                    v_val_4645_ = leanh::lean_ctor_get(v___x_4643_, 0);
                    v_isSharedCheck_4652_ = (!leanh::lean_is_exclusive(v___x_4643_)) as u8;
                    if v_isSharedCheck_4652_ == 0 {
                        v___x_4647_ = v___x_4643_;
                        v_isShared_4648_ = v_isSharedCheck_4652_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_4645_);
                        leanh::lean_dec(v___x_4643_);
                        v___x_4647_ = leanh::lean_box(0);
                        v_isShared_4648_ = v_isSharedCheck_4652_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4648_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4647_, 0);
                    v___x_4650_ = v___x_4647_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4651_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4651_, 0, v_val_4645_);
                    v___x_4650_ = v_reuseFailAlloc_4651_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4650_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1___boxed(
    mut v_constName_4653_: *mut leanh::LeanObject,
    mut v___y_4654_: *mut leanh::LeanObject,
    mut v___y_4655_: *mut leanh::LeanObject,
    mut v___y_4656_: *mut leanh::LeanObject,
    mut v___y_4657_: *mut leanh::LeanObject,
    mut v___y_4658_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4659_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4659_ = l_Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1(
        v_constName_4653_,
        v___y_4654_,
        v___y_4655_,
        v___y_4656_,
        v___y_4657_,
    );
    leanh::lean_dec(v___y_4657_);
    leanh::lean_dec_ref(v___y_4656_);
    leanh::lean_dec(v___y_4655_);
    leanh::lean_dec_ref(v___y_4654_);
    return v_res_4659_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0(
    mut v___y_4667_: u8,
    mut v_suppressElabErrors_4668_: u8,
    mut v_x_4669_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_4669_) == 1 {
        let mut v_pre_4670_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_pre_4670_ = leanh::lean_ctor_get(v_x_4669_, 0);
        match leanh::lean_obj_tag(v_pre_4670_) {
            1 => {
                let mut v_pre_4671_: *mut leanh::LeanObject = core::ptr::null_mut();
                v_pre_4671_ = leanh::lean_ctor_get(v_pre_4670_, 0);
                match leanh::lean_obj_tag(v_pre_4671_) {
                    0 => {
                        let mut v_str_4672_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v_str_4673_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_4674_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_4675_: u8 = 0;
                        v_str_4672_ = leanh::lean_ctor_get(v_x_4669_, 1);
                        v_str_4673_ = leanh::lean_ctor_get(v_pre_4670_, 1);
                        v___x_4674_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__0;
                        v___x_4675_ = lean_string_dec_eq(v_str_4673_, v___x_4674_);
                        if v___x_4675_ == 0 {
                            let mut v___x_4676_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_4677_: u8 = 0;
                            v___x_4676_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__1;
                            v___x_4677_ = lean_string_dec_eq(v_str_4673_, v___x_4676_);
                            if v___x_4677_ == 0 {
                                return v___y_4667_;
                            } else {
                                let mut v___x_4678_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_4679_: u8 = 0;
                                v___x_4678_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__2;
                                v___x_4679_ = lean_string_dec_eq(v_str_4672_, v___x_4678_);
                                if v___x_4679_ == 0 {
                                    return v___y_4667_;
                                } else {
                                    return v_suppressElabErrors_4668_;
                                }
                            }
                        } else {
                            let mut v___x_4680_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_4681_: u8 = 0;
                            v___x_4680_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__3;
                            v___x_4681_ = lean_string_dec_eq(v_str_4672_, v___x_4680_);
                            if v___x_4681_ == 0 {
                                return v___y_4667_;
                            } else {
                                return v_suppressElabErrors_4668_;
                            }
                        }
                    }
                    1 => {
                        let mut v_pre_4682_: *mut leanh::LeanObject = core::ptr::null_mut();
                        v_pre_4682_ = leanh::lean_ctor_get(v_pre_4671_, 0);
                        if leanh::lean_obj_tag(v_pre_4682_) == 0 {
                            let mut v_str_4683_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_4684_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_4685_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_4686_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_4687_: u8 = 0;
                            v_str_4683_ = leanh::lean_ctor_get(v_x_4669_, 1);
                            v_str_4684_ = leanh::lean_ctor_get(v_pre_4670_, 1);
                            v_str_4685_ = leanh::lean_ctor_get(v_pre_4671_, 1);
                            v___x_4686_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__4;
                            v___x_4687_ = lean_string_dec_eq(v_str_4685_, v___x_4686_);
                            if v___x_4687_ == 0 {
                                return v___y_4667_;
                            } else {
                                let mut v___x_4688_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_4689_: u8 = 0;
                                v___x_4688_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__5;
                                v___x_4689_ = lean_string_dec_eq(v_str_4684_, v___x_4688_);
                                if v___x_4689_ == 0 {
                                    return v___y_4667_;
                                } else {
                                    let mut v___x_4690_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_4691_: u8 = 0;
                                    v___x_4690_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___closed__6;
                                    v___x_4691_ = lean_string_dec_eq(v_str_4683_, v___x_4690_);
                                    if v___x_4691_ == 0 {
                                        return v___y_4667_;
                                    } else {
                                        return v_suppressElabErrors_4668_;
                                    }
                                }
                            }
                        } else {
                            return v___y_4667_;
                        }
                    }
                    _ => {
                        return v___y_4667_;
                    }
                }
            }
            0 => {
                let mut v_str_4692_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4693_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4694_: u8 = 0;
                v_str_4692_ = leanh::lean_ctor_get(v_x_4669_, 1);
                v___x_4693_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__0_spec__0___closed__0;
                v___x_4694_ = lean_string_dec_eq(v_str_4692_, v___x_4693_);
                if v___x_4694_ == 0 {
                    return v___y_4667_;
                } else {
                    return v_suppressElabErrors_4668_;
                }
            }
            _ => {
                return v___y_4667_;
            }
        }
    } else {
        return v___y_4667_;
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___boxed(
    mut v___y_4695_: *mut leanh::LeanObject,
    mut v_suppressElabErrors_4696_: *mut leanh::LeanObject,
    mut v_x_4697_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_8747__boxed_4698_: u8 = 0;
    let mut v_suppressElabErrors_boxed_4699_: u8 = 0;
    let mut v_res_4700_: u8 = 0;
    let mut v_r_4701_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_8747__boxed_4698_ = (leanh::lean_unbox(v___y_4695_) as u8);
    v_suppressElabErrors_boxed_4699_ = (leanh::lean_unbox(v_suppressElabErrors_4696_) as u8);
    v_res_4700_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0(v___y_8747__boxed_4698_, v_suppressElabErrors_boxed_4699_, v_x_4697_);
    leanh::lean_dec(v_x_4697_);
    v_r_4701_ = leanh::lean_box((v_res_4700_) as usize);
    return v_r_4701_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6(
    mut v_ref_4703_: *mut leanh::LeanObject,
    mut v_msgData_4704_: *mut leanh::LeanObject,
    mut v_severity_4705_: u8,
    mut v_isSilent_4706_: u8,
    mut v___y_4707_: *mut leanh::LeanObject,
    mut v___y_4708_: *mut leanh::LeanObject,
    mut v___y_4709_: *mut leanh::LeanObject,
    mut v___y_4710_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4717_: u8 = 0;
    let mut v___y_4718_: u8 = 0;
    let mut v___y_4719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_4730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4736_: u8 = 0;
    let mut v___x_4737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4747_: u8 = 0;
    let mut v___y_4749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4751_: u8 = 0;
    let mut v___y_4752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4753_: u8 = 0;
    let mut v___y_4754_: u8 = 0;
    let mut v___y_4755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4762_: u8 = 0;
    let mut v___x_4763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4767_: u8 = 0;
    let mut v___x_4768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4772_: u8 = 0;
    let mut v___y_4774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4776_: u8 = 0;
    let mut v___y_4777_: u8 = 0;
    let mut v___y_4778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4780_: u8 = 0;
    let mut v___y_4781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4788_: u8 = 0;
    let mut v___y_4789_: u8 = 0;
    let mut v___y_4790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4791_: u8 = 0;
    let mut v_ref_4792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4796_: u8 = 0;
    let mut v___y_4798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4801_: u8 = 0;
    let mut v___y_4802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4803_: u8 = 0;
    let mut v___y_4804_: u8 = 0;
    let mut v___y_4806_: u8 = 0;
    let mut v_fileName_4807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4811_: u8 = 0;
    let mut v___x_4812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4815_: u8 = 0;
    let mut v___x_4816_: u8 = 0;
    let mut v___x_4817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4818_: u8 = 0;
    let mut v___x_4819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4821_: u8 = 0;
    let mut v___x_4822_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4796_ = 2;
                v___x_4821_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4705_, v___x_4796_);
                if v___x_4821_ == 0 {
                    v___y_4806_ = v___x_4821_;
                    state = 10;
                    continue;
                } else {
                    leanh::lean_inc_ref(v_msgData_4704_);
                    v___x_4822_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_4704_);
                    v___y_4806_ = v___x_4822_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_4722_ = lean_st_ref_take(v___y_4721_);
                v_currNamespace_4723_ = leanh::lean_ctor_get(v___y_4720_, 6);
                v_openDecls_4724_ = leanh::lean_ctor_get(v___y_4720_, 7);
                v_env_4725_ = leanh::lean_ctor_get(v___x_4722_, 0);
                v_nextMacroScope_4726_ = leanh::lean_ctor_get(v___x_4722_, 1);
                v_ngen_4727_ = leanh::lean_ctor_get(v___x_4722_, 2);
                v_auxDeclNGen_4728_ = leanh::lean_ctor_get(v___x_4722_, 3);
                v_traceState_4729_ = leanh::lean_ctor_get(v___x_4722_, 4);
                v_cache_4730_ = leanh::lean_ctor_get(v___x_4722_, 5);
                v_messages_4731_ = leanh::lean_ctor_get(v___x_4722_, 6);
                v_infoState_4732_ = leanh::lean_ctor_get(v___x_4722_, 7);
                v_snapshotTasks_4733_ = leanh::lean_ctor_get(v___x_4722_, 8);
                v_isSharedCheck_4747_ = (!leanh::lean_is_exclusive(v___x_4722_)) as u8;
                if v_isSharedCheck_4747_ == 0 {
                    v___x_4735_ = v___x_4722_;
                    v_isShared_4736_ = v_isSharedCheck_4747_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_4733_);
                    leanh::lean_inc(v_infoState_4732_);
                    leanh::lean_inc(v_messages_4731_);
                    leanh::lean_inc(v_cache_4730_);
                    leanh::lean_inc(v_traceState_4729_);
                    leanh::lean_inc(v_auxDeclNGen_4728_);
                    leanh::lean_inc(v_ngen_4727_);
                    leanh::lean_inc(v_nextMacroScope_4726_);
                    leanh::lean_inc(v_env_4725_);
                    leanh::lean_dec(v___x_4722_);
                    v___x_4735_ = leanh::lean_box(0);
                    v_isShared_4736_ = v_isSharedCheck_4747_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc(v_openDecls_4724_);
                leanh::lean_inc(v_currNamespace_4723_);
                v___x_4737_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4737_, 0, v_currNamespace_4723_);
                leanh::lean_ctor_set(v___x_4737_, 1, v_openDecls_4724_);
                v___x_4738_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4738_, 0, v___x_4737_);
                leanh::lean_ctor_set(v___x_4738_, 1, v___y_4716_);
                leanh::lean_inc_ref(v___y_4719_);
                leanh::lean_inc_ref(v___y_4714_);
                v___x_4739_ = leanh::lean_alloc_ctor(0, 5, (3) as u32);
                leanh::lean_ctor_set(v___x_4739_, 0, v___y_4714_);
                leanh::lean_ctor_set(v___x_4739_, 1, v___y_4715_);
                leanh::lean_ctor_set(v___x_4739_, 2, v___y_4713_);
                leanh::lean_ctor_set(v___x_4739_, 3, v___y_4719_);
                leanh::lean_ctor_set(v___x_4739_, 4, v___x_4738_);
                leanh::lean_ctor_set_uint8(
                    v___x_4739_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                    v___y_4717_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_4739_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 1) as u32,
                    v___y_4718_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_4739_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 2) as u32,
                    v_isSilent_4706_,
                );
                v___x_4740_ = l_Lean_MessageLog_add(v___x_4739_, v_messages_4731_);
                if v_isShared_4736_ == 0 {
                    leanh::lean_ctor_set(v___x_4735_, 6, v___x_4740_);
                    v___x_4742_ = v___x_4735_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4746_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4746_, 0, v_env_4725_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4746_, 1, v_nextMacroScope_4726_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4746_, 2, v_ngen_4727_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4746_, 3, v_auxDeclNGen_4728_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4746_, 4, v_traceState_4729_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4746_, 5, v_cache_4730_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4746_, 6, v___x_4740_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4746_, 7, v_infoState_4732_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4746_, 8, v_snapshotTasks_4733_);
                    v___x_4742_ = v_reuseFailAlloc_4746_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4743_ = lean_st_ref_set(v___y_4721_, v___x_4742_);
                v___x_4744_ = leanh::lean_box(0);
                v___x_4745_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4745_, 0, v___x_4744_);
                return v___x_4745_;
            }
            4 => {
                v___x_4757_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_4704_,
                    );
                v___x_4758_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs_spec__0_spec__0(v___x_4757_, v___y_4707_, v___y_4708_, v___y_4709_, v___y_4710_);
                v_a_4759_ = leanh::lean_ctor_get(v___x_4758_, 0);
                v_isSharedCheck_4772_ = (!leanh::lean_is_exclusive(v___x_4758_)) as u8;
                if v_isSharedCheck_4772_ == 0 {
                    v___x_4761_ = v___x_4758_;
                    v_isShared_4762_ = v_isSharedCheck_4772_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_inc(v_a_4759_);
                    leanh::lean_dec(v___x_4758_);
                    v___x_4761_ = leanh::lean_box(0);
                    v_isShared_4762_ = v_isSharedCheck_4772_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                leanh::lean_inc_ref_n(v___y_4755_, 2);
                v___x_4763_ = l_Lean_FileMap_toPosition(v___y_4755_, v___y_4752_);
                leanh::lean_dec(v___y_4752_);
                v___x_4764_ = l_Lean_FileMap_toPosition(v___y_4755_, v___y_4756_);
                leanh::lean_dec(v___y_4756_);
                v___x_4765_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4765_, 0, v___x_4764_);
                v___x_4766_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___closed__0;
                if v___y_4753_ == 0 {
                    leanh::lean_del_object(v___x_4761_);
                    leanh::lean_dec_ref(v___y_4749_);
                    v___y_4713_ = v___x_4765_;
                    v___y_4714_ = v___y_4750_;
                    v___y_4715_ = v___x_4763_;
                    v___y_4716_ = v_a_4759_;
                    v___y_4717_ = v___y_4751_;
                    v___y_4718_ = v___y_4754_;
                    v___y_4719_ = v___x_4766_;
                    v___y_4720_ = v___y_4709_;
                    v___y_4721_ = v___y_4710_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_4759_);
                    v___x_4767_ = l_Lean_MessageData_hasTag(v___y_4749_, v_a_4759_);
                    if v___x_4767_ == 0 {
                        leanh::lean_dec_ref_known(v___x_4765_, 1);
                        leanh::lean_dec_ref(v___x_4763_);
                        leanh::lean_dec(v_a_4759_);
                        v___x_4768_ = leanh::lean_box(0);
                        if v_isShared_4762_ == 0 {
                            leanh::lean_ctor_set(v___x_4761_, 0, v___x_4768_);
                            v___x_4770_ = v___x_4761_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_4771_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4771_, 0, v___x_4768_);
                            v___x_4770_ = v_reuseFailAlloc_4771_;
                            state = 6;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_4761_);
                        v___y_4713_ = v___x_4765_;
                        v___y_4714_ = v___y_4750_;
                        v___y_4715_ = v___x_4763_;
                        v___y_4716_ = v_a_4759_;
                        v___y_4717_ = v___y_4751_;
                        v___y_4718_ = v___y_4754_;
                        v___y_4719_ = v___x_4766_;
                        v___y_4720_ = v___y_4709_;
                        v___y_4721_ = v___y_4710_;
                        state = 1;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_4770_;
            }
            7 => {
                v___x_4782_ = l_Lean_Syntax_getTailPos_x3f(v___y_4778_, v___y_4776_);
                leanh::lean_dec(v___y_4778_);
                if leanh::lean_obj_tag(v___x_4782_) == 0 {
                    leanh::lean_inc(v___y_4781_);
                    v___y_4749_ = v___y_4774_;
                    v___y_4750_ = v___y_4775_;
                    v___y_4751_ = v___y_4776_;
                    v___y_4752_ = v___y_4781_;
                    v___y_4753_ = v___y_4777_;
                    v___y_4754_ = v___y_4780_;
                    v___y_4755_ = v___y_4779_;
                    v___y_4756_ = v___y_4781_;
                    state = 4;
                    continue;
                } else {
                    v_val_4783_ = leanh::lean_ctor_get(v___x_4782_, 0);
                    leanh::lean_inc(v_val_4783_);
                    leanh::lean_dec_ref_known(v___x_4782_, 1);
                    v___y_4749_ = v___y_4774_;
                    v___y_4750_ = v___y_4775_;
                    v___y_4751_ = v___y_4776_;
                    v___y_4752_ = v___y_4781_;
                    v___y_4753_ = v___y_4777_;
                    v___y_4754_ = v___y_4780_;
                    v___y_4755_ = v___y_4779_;
                    v___y_4756_ = v_val_4783_;
                    state = 4;
                    continue;
                }
            }
            8 => {
                v_ref_4792_ = l_Lean_replaceRef(v_ref_4703_, v___y_4787_);
                v___x_4793_ = l_Lean_Syntax_getPos_x3f(v_ref_4792_, v___y_4788_);
                if leanh::lean_obj_tag(v___x_4793_) == 0 {
                    v___x_4794_ = leanh::lean_unsigned_to_nat(0);
                    v___y_4774_ = v___y_4785_;
                    v___y_4775_ = v___y_4786_;
                    v___y_4776_ = v___y_4788_;
                    v___y_4777_ = v___y_4789_;
                    v___y_4778_ = v_ref_4792_;
                    v___y_4779_ = v___y_4790_;
                    v___y_4780_ = v___y_4791_;
                    v___y_4781_ = v___x_4794_;
                    state = 7;
                    continue;
                } else {
                    v_val_4795_ = leanh::lean_ctor_get(v___x_4793_, 0);
                    leanh::lean_inc(v_val_4795_);
                    leanh::lean_dec_ref_known(v___x_4793_, 1);
                    v___y_4774_ = v___y_4785_;
                    v___y_4775_ = v___y_4786_;
                    v___y_4776_ = v___y_4788_;
                    v___y_4777_ = v___y_4789_;
                    v___y_4778_ = v_ref_4792_;
                    v___y_4779_ = v___y_4790_;
                    v___y_4780_ = v___y_4791_;
                    v___y_4781_ = v_val_4795_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                if v___y_4804_ == 0 {
                    v___y_4785_ = v___y_4798_;
                    v___y_4786_ = v___y_4799_;
                    v___y_4787_ = v___y_4800_;
                    v___y_4788_ = v___y_4803_;
                    v___y_4789_ = v___y_4801_;
                    v___y_4790_ = v___y_4802_;
                    v___y_4791_ = v_severity_4705_;
                    state = 8;
                    continue;
                } else {
                    v___y_4785_ = v___y_4798_;
                    v___y_4786_ = v___y_4799_;
                    v___y_4787_ = v___y_4800_;
                    v___y_4788_ = v___y_4803_;
                    v___y_4789_ = v___y_4801_;
                    v___y_4790_ = v___y_4802_;
                    v___y_4791_ = v___x_4796_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                if v___y_4806_ == 0 {
                    v_fileName_4807_ = leanh::lean_ctor_get(v___y_4709_, 0);
                    v_fileMap_4808_ = leanh::lean_ctor_get(v___y_4709_, 1);
                    v_options_4809_ = leanh::lean_ctor_get(v___y_4709_, 2);
                    v_ref_4810_ = leanh::lean_ctor_get(v___y_4709_, 5);
                    v_suppressElabErrors_4811_ = leanh::lean_ctor_get_uint8(
                        v___y_4709_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                    );
                    v___x_4812_ = leanh::lean_box((v___y_4806_) as usize);
                    v___x_4813_ = leanh::lean_box((v_suppressElabErrors_4811_) as usize);
                    v___f_4814_ = leanh::lean_alloc_closure(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    leanh::lean_closure_set(v___f_4814_, 0, v___x_4812_);
                    leanh::lean_closure_set(v___f_4814_, 1, v___x_4813_);
                    v___x_4815_ = 1;
                    v___x_4816_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4705_, v___x_4815_);
                    if v___x_4816_ == 0 {
                        v___y_4798_ = v___f_4814_;
                        v___y_4799_ = v_fileName_4807_;
                        v___y_4800_ = v_ref_4810_;
                        v___y_4801_ = v_suppressElabErrors_4811_;
                        v___y_4802_ = v_fileMap_4808_;
                        v___y_4803_ = v___y_4806_;
                        v___y_4804_ = v___x_4816_;
                        state = 9;
                        continue;
                    } else {
                        v___x_4817_ = l_Lean_warningAsError;
                        v___x_4818_ = l_Lean_Option_get___at___00__private_Lean_DefEqAttrib_0__Lean_isDefEqCareful_spec__1(v_options_4809_, v___x_4817_);
                        v___y_4798_ = v___f_4814_;
                        v___y_4799_ = v_fileName_4807_;
                        v___y_4800_ = v_ref_4810_;
                        v___y_4801_ = v_suppressElabErrors_4811_;
                        v___y_4802_ = v_fileMap_4808_;
                        v___y_4803_ = v___y_4806_;
                        v___y_4804_ = v___x_4818_;
                        state = 9;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_msgData_4704_);
                    v___x_4819_ = leanh::lean_box(0);
                    v___x_4820_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4820_, 0, v___x_4819_);
                    return v___x_4820_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6___boxed(
    mut v_ref_4823_: *mut leanh::LeanObject,
    mut v_msgData_4824_: *mut leanh::LeanObject,
    mut v_severity_4825_: *mut leanh::LeanObject,
    mut v_isSilent_4826_: *mut leanh::LeanObject,
    mut v___y_4827_: *mut leanh::LeanObject,
    mut v___y_4828_: *mut leanh::LeanObject,
    mut v___y_4829_: *mut leanh::LeanObject,
    mut v___y_4830_: *mut leanh::LeanObject,
    mut v___y_4831_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_severity_boxed_4832_: u8 = 0;
    let mut v_isSilent_boxed_4833_: u8 = 0;
    let mut v_res_4834_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_4832_ = (leanh::lean_unbox(v_severity_4825_) as u8);
    v_isSilent_boxed_4833_ = (leanh::lean_unbox(v_isSilent_4826_) as u8);
    v_res_4834_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6(v_ref_4823_, v_msgData_4824_, v_severity_boxed_4832_, v_isSilent_boxed_4833_, v___y_4827_, v___y_4828_, v___y_4829_, v___y_4830_);
    leanh::lean_dec(v___y_4830_);
    leanh::lean_dec_ref(v___y_4829_);
    leanh::lean_dec(v___y_4828_);
    leanh::lean_dec_ref(v___y_4827_);
    leanh::lean_dec(v_ref_4823_);
    return v_res_4834_;
}
pub unsafe fn l_Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5(
    mut v_msgData_4835_: *mut leanh::LeanObject,
    mut v_severity_4836_: u8,
    mut v_isSilent_4837_: u8,
    mut v___y_4838_: *mut leanh::LeanObject,
    mut v___y_4839_: *mut leanh::LeanObject,
    mut v___y_4840_: *mut leanh::LeanObject,
    mut v___y_4841_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_4843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4844_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_4843_ = leanh::lean_ctor_get(v___y_4840_, 5);
    v___x_4844_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5_spec__6(v_ref_4843_, v_msgData_4835_, v_severity_4836_, v_isSilent_4837_, v___y_4838_, v___y_4839_, v___y_4840_, v___y_4841_);
    return v___x_4844_;
}
pub unsafe fn l_Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5___boxed(
    mut v_msgData_4845_: *mut leanh::LeanObject,
    mut v_severity_4846_: *mut leanh::LeanObject,
    mut v_isSilent_4847_: *mut leanh::LeanObject,
    mut v___y_4848_: *mut leanh::LeanObject,
    mut v___y_4849_: *mut leanh::LeanObject,
    mut v___y_4850_: *mut leanh::LeanObject,
    mut v___y_4851_: *mut leanh::LeanObject,
    mut v___y_4852_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_severity_boxed_4853_: u8 = 0;
    let mut v_isSilent_boxed_4854_: u8 = 0;
    let mut v_res_4855_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_4853_ = (leanh::lean_unbox(v_severity_4846_) as u8);
    v_isSilent_boxed_4854_ = (leanh::lean_unbox(v_isSilent_4847_) as u8);
    v_res_4855_ = l_Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5(
        v_msgData_4845_,
        v_severity_boxed_4853_,
        v_isSilent_boxed_4854_,
        v___y_4848_,
        v___y_4849_,
        v___y_4850_,
        v___y_4851_,
    );
    leanh::lean_dec(v___y_4851_);
    leanh::lean_dec_ref(v___y_4850_);
    leanh::lean_dec(v___y_4849_);
    leanh::lean_dec_ref(v___y_4848_);
    return v_res_4855_;
}
pub unsafe fn l_Lean_logError___at___00Lean_inferDefEqAttr_spec__2(
    mut v_msgData_4856_: *mut leanh::LeanObject,
    mut v___y_4857_: *mut leanh::LeanObject,
    mut v___y_4858_: *mut leanh::LeanObject,
    mut v___y_4859_: *mut leanh::LeanObject,
    mut v___y_4860_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4862_: u8 = 0;
    let mut v___x_4863_: u8 = 0;
    let mut v___x_4864_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4862_ = 2;
    v___x_4863_ = 0;
    v___x_4864_ = l_Lean_log___at___00Lean_logError___at___00Lean_inferDefEqAttr_spec__2_spec__5(
        v_msgData_4856_,
        v___x_4862_,
        v___x_4863_,
        v___y_4857_,
        v___y_4858_,
        v___y_4859_,
        v___y_4860_,
    );
    return v___x_4864_;
}
pub unsafe fn l_Lean_logError___at___00Lean_inferDefEqAttr_spec__2___boxed(
    mut v_msgData_4865_: *mut leanh::LeanObject,
    mut v___y_4866_: *mut leanh::LeanObject,
    mut v___y_4867_: *mut leanh::LeanObject,
    mut v___y_4868_: *mut leanh::LeanObject,
    mut v___y_4869_: *mut leanh::LeanObject,
    mut v___y_4870_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4871_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4871_ = l_Lean_logError___at___00Lean_inferDefEqAttr_spec__2(
        v_msgData_4865_,
        v___y_4866_,
        v___y_4867_,
        v___y_4868_,
        v___y_4869_,
    );
    leanh::lean_dec(v___y_4869_);
    leanh::lean_dec_ref(v___y_4868_);
    leanh::lean_dec(v___y_4867_);
    leanh::lean_dec_ref(v___y_4866_);
    return v_res_4871_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7___redArg___lam__0(
    mut v___y_4872_: *mut leanh::LeanObject,
    mut v_isExporting_4873_: u8,
    mut v___x_4874_: *mut leanh::LeanObject,
    mut v___y_4875_: *mut leanh::LeanObject,
    mut v___x_4876_: *mut leanh::LeanObject,
    mut v_a_x3f_4877_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4890_: u8 = 0;
    let mut v___x_4891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_4898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4902_: u8 = 0;
    let mut v___x_4904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4909_: u8 = 0;
    let mut v_unused_4910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4912_: u8 = 0;
    let mut v_unused_4913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4879_ = lean_st_ref_take(v___y_4872_);
                v_env_4880_ = leanh::lean_ctor_get(v___x_4879_, 0);
                v_nextMacroScope_4881_ = leanh::lean_ctor_get(v___x_4879_, 1);
                v_ngen_4882_ = leanh::lean_ctor_get(v___x_4879_, 2);
                v_auxDeclNGen_4883_ = leanh::lean_ctor_get(v___x_4879_, 3);
                v_traceState_4884_ = leanh::lean_ctor_get(v___x_4879_, 4);
                v_messages_4885_ = leanh::lean_ctor_get(v___x_4879_, 6);
                v_infoState_4886_ = leanh::lean_ctor_get(v___x_4879_, 7);
                v_snapshotTasks_4887_ = leanh::lean_ctor_get(v___x_4879_, 8);
                v_isSharedCheck_4912_ = (!leanh::lean_is_exclusive(v___x_4879_)) as u8;
                if v_isSharedCheck_4912_ == 0 {
                    v_unused_4913_ = leanh::lean_ctor_get(v___x_4879_, 5);
                    leanh::lean_dec(v_unused_4913_);
                    v___x_4889_ = v___x_4879_;
                    v_isShared_4890_ = v_isSharedCheck_4912_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_4887_);
                    leanh::lean_inc(v_infoState_4886_);
                    leanh::lean_inc(v_messages_4885_);
                    leanh::lean_inc(v_traceState_4884_);
                    leanh::lean_inc(v_auxDeclNGen_4883_);
                    leanh::lean_inc(v_ngen_4882_);
                    leanh::lean_inc(v_nextMacroScope_4881_);
                    leanh::lean_inc(v_env_4880_);
                    leanh::lean_dec(v___x_4879_);
                    v___x_4889_ = leanh::lean_box(0);
                    v_isShared_4890_ = v_isSharedCheck_4912_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4891_ = l_Lean_Environment_setExporting(v_env_4880_, v_isExporting_4873_);
                if v_isShared_4890_ == 0 {
                    leanh::lean_ctor_set(v___x_4889_, 5, v___x_4874_);
                    leanh::lean_ctor_set(v___x_4889_, 0, v___x_4891_);
                    v___x_4893_ = v___x_4889_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4911_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4911_, 0, v___x_4891_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4911_, 1, v_nextMacroScope_4881_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4911_, 2, v_ngen_4882_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4911_, 3, v_auxDeclNGen_4883_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4911_, 4, v_traceState_4884_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4911_, 5, v___x_4874_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4911_, 6, v_messages_4885_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4911_, 7, v_infoState_4886_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4911_, 8, v_snapshotTasks_4887_);
                    v___x_4893_ = v_reuseFailAlloc_4911_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4894_ = lean_st_ref_set(v___y_4872_, v___x_4893_);
                v___x_4895_ = lean_st_ref_take(v___y_4875_);
                v_mctx_4896_ = leanh::lean_ctor_get(v___x_4895_, 0);
                v_zetaDeltaFVarIds_4897_ = leanh::lean_ctor_get(v___x_4895_, 2);
                v_postponed_4898_ = leanh::lean_ctor_get(v___x_4895_, 3);
                v_diag_4899_ = leanh::lean_ctor_get(v___x_4895_, 4);
                v_isSharedCheck_4909_ = (!leanh::lean_is_exclusive(v___x_4895_)) as u8;
                if v_isSharedCheck_4909_ == 0 {
                    v_unused_4910_ = leanh::lean_ctor_get(v___x_4895_, 1);
                    leanh::lean_dec(v_unused_4910_);
                    v___x_4901_ = v___x_4895_;
                    v_isShared_4902_ = v_isSharedCheck_4909_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_4899_);
                    leanh::lean_inc(v_postponed_4898_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_4897_);
                    leanh::lean_inc(v_mctx_4896_);
                    leanh::lean_dec(v___x_4895_);
                    v___x_4901_ = leanh::lean_box(0);
                    v_isShared_4902_ = v_isSharedCheck_4909_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4902_ == 0 {
                    leanh::lean_ctor_set(v___x_4901_, 1, v___x_4876_);
                    v___x_4904_ = v___x_4901_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4908_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4908_, 0, v_mctx_4896_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4908_, 1, v___x_4876_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4908_,
                        2,
                        v_zetaDeltaFVarIds_4897_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_4908_, 3, v_postponed_4898_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4908_, 4, v_diag_4899_);
                    v___x_4904_ = v_reuseFailAlloc_4908_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4905_ = lean_st_ref_set(v___y_4875_, v___x_4904_);
                v___x_4906_ = leanh::lean_box(0);
                v___x_4907_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4907_, 0, v___x_4906_);
                return v___x_4907_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7___redArg___lam__0___boxed(
    mut v___y_4914_: *mut leanh::LeanObject,
    mut v_isExporting_4915_: *mut leanh::LeanObject,
    mut v___x_4916_: *mut leanh::LeanObject,
    mut v___y_4917_: *mut leanh::LeanObject,
    mut v___x_4918_: *mut leanh::LeanObject,
    mut v_a_x3f_4919_: *mut leanh::LeanObject,
    mut v___y_4920_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isExporting_boxed_4921_: u8 = 0;
    let mut v_res_4922_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_4921_ = (leanh::lean_unbox(v_isExporting_4915_) as u8);
    v_res_4922_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7___redArg___lam__0(v___y_4914_, v_isExporting_boxed_4921_, v___x_4916_, v___y_4917_, v___x_4918_, v_a_x3f_4919_);
    leanh::lean_dec(v_a_x3f_4919_);
    leanh::lean_dec(v___y_4917_);
    leanh::lean_dec(v___y_4914_);
    return v_res_4922_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7___redArg(
    mut v_declName_4923_: *mut leanh::LeanObject,
    mut v_isExporting_4924_: u8,
    mut v___y_4925_: *mut leanh::LeanObject,
    mut v___y_4926_: *mut leanh::LeanObject,
    mut v___y_4927_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isExporting_4931_: u8 = 0;
    let mut v___x_4932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4943_: u8 = 0;
    let mut v___x_4944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_4952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4956_: u8 = 0;
    let mut v___x_4957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4965_: u8 = 0;
    let mut v___x_4967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4971_: u8 = 0;
    let mut v___x_4973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4975_: u8 = 0;
    let mut v_unused_4976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4978_: u8 = 0;
    let mut v_a_4979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4984_: u8 = 0;
    let mut v___x_4986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4988_: u8 = 0;
    let mut v_unused_4989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4991_: u8 = 0;
    let mut v_unused_4992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4994_: u8 = 0;
    let mut v_unused_4995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4929_ = lean_st_ref_get(v___y_4927_);
                v_env_4930_ = leanh::lean_ctor_get(v___x_4929_, 0);
                leanh::lean_inc_ref(v_env_4930_);
                leanh::lean_dec(v___x_4929_);
                v_isExporting_4931_ = leanh::lean_ctor_get_uint8(
                    v_env_4930_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                );
                leanh::lean_dec_ref(v_env_4930_);
                v___x_4932_ = lean_st_ref_take(v___y_4927_);
                v_env_4933_ = leanh::lean_ctor_get(v___x_4932_, 0);
                v_nextMacroScope_4934_ = leanh::lean_ctor_get(v___x_4932_, 1);
                v_ngen_4935_ = leanh::lean_ctor_get(v___x_4932_, 2);
                v_auxDeclNGen_4936_ = leanh::lean_ctor_get(v___x_4932_, 3);
                v_traceState_4937_ = leanh::lean_ctor_get(v___x_4932_, 4);
                v_messages_4938_ = leanh::lean_ctor_get(v___x_4932_, 6);
                v_infoState_4939_ = leanh::lean_ctor_get(v___x_4932_, 7);
                v_snapshotTasks_4940_ = leanh::lean_ctor_get(v___x_4932_, 8);
                v_isSharedCheck_4994_ = (!leanh::lean_is_exclusive(v___x_4932_)) as u8;
                if v_isSharedCheck_4994_ == 0 {
                    v_unused_4995_ = leanh::lean_ctor_get(v___x_4932_, 5);
                    leanh::lean_dec(v_unused_4995_);
                    v___x_4942_ = v___x_4932_;
                    v_isShared_4943_ = v_isSharedCheck_4994_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_4940_);
                    leanh::lean_inc(v_infoState_4939_);
                    leanh::lean_inc(v_messages_4938_);
                    leanh::lean_inc(v_traceState_4937_);
                    leanh::lean_inc(v_auxDeclNGen_4936_);
                    leanh::lean_inc(v_ngen_4935_);
                    leanh::lean_inc(v_nextMacroScope_4934_);
                    leanh::lean_inc(v_env_4933_);
                    leanh::lean_dec(v___x_4932_);
                    v___x_4942_ = leanh::lean_box(0);
                    v_isShared_4943_ = v_isSharedCheck_4994_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4944_ = l_Lean_Environment_setExporting(v_env_4933_, v_isExporting_4924_);
                v___x_4945_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__4
                    ),
                    core::ptr::addr_of_mut!(
                        l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__4_once
                    ),
                    _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__4,
                );
                if v_isShared_4943_ == 0 {
                    leanh::lean_ctor_set(v___x_4942_, 5, v___x_4945_);
                    leanh::lean_ctor_set(v___x_4942_, 0, v___x_4944_);
                    v___x_4947_ = v___x_4942_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4993_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4993_, 0, v___x_4944_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4993_, 1, v_nextMacroScope_4934_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4993_, 2, v_ngen_4935_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4993_, 3, v_auxDeclNGen_4936_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4993_, 4, v_traceState_4937_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4993_, 5, v___x_4945_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4993_, 6, v_messages_4938_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4993_, 7, v_infoState_4939_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4993_, 8, v_snapshotTasks_4940_);
                    v___x_4947_ = v_reuseFailAlloc_4993_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4948_ = lean_st_ref_set(v___y_4927_, v___x_4947_);
                v___x_4949_ = lean_st_ref_take(v___y_4925_);
                v_mctx_4950_ = leanh::lean_ctor_get(v___x_4949_, 0);
                v_zetaDeltaFVarIds_4951_ = leanh::lean_ctor_get(v___x_4949_, 2);
                v_postponed_4952_ = leanh::lean_ctor_get(v___x_4949_, 3);
                v_diag_4953_ = leanh::lean_ctor_get(v___x_4949_, 4);
                v_isSharedCheck_4991_ = (!leanh::lean_is_exclusive(v___x_4949_)) as u8;
                if v_isSharedCheck_4991_ == 0 {
                    v_unused_4992_ = leanh::lean_ctor_get(v___x_4949_, 1);
                    leanh::lean_dec(v_unused_4992_);
                    v___x_4955_ = v___x_4949_;
                    v_isShared_4956_ = v_isSharedCheck_4991_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_4953_);
                    leanh::lean_inc(v_postponed_4952_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_4951_);
                    leanh::lean_inc(v_mctx_4950_);
                    leanh::lean_dec(v___x_4949_);
                    v___x_4955_ = leanh::lean_box(0);
                    v_isShared_4956_ = v_isSharedCheck_4991_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4957_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___redArg___closed__0);
                if v_isShared_4956_ == 0 {
                    leanh::lean_ctor_set(v___x_4955_, 1, v___x_4957_);
                    v___x_4959_ = v___x_4955_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4990_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4990_, 0, v_mctx_4950_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4990_, 1, v___x_4957_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4990_,
                        2,
                        v_zetaDeltaFVarIds_4951_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_4990_, 3, v_postponed_4952_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4990_, 4, v_diag_4953_);
                    v___x_4959_ = v_reuseFailAlloc_4990_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4960_ = lean_st_ref_set(v___y_4925_, v___x_4959_);
                v_r_4961_ = l_Lean_validateDefEqAttr(v_declName_4923_, v___y_4926_, v___y_4927_);
                if leanh::lean_obj_tag(v_r_4961_) == 0 {
                    v_a_4962_ = leanh::lean_ctor_get(v_r_4961_, 0);
                    v_isSharedCheck_4978_ = (!leanh::lean_is_exclusive(v_r_4961_)) as u8;
                    if v_isSharedCheck_4978_ == 0 {
                        v___x_4964_ = v_r_4961_;
                        v_isShared_4965_ = v_isSharedCheck_4978_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4962_);
                        leanh::lean_dec(v_r_4961_);
                        v___x_4964_ = leanh::lean_box(0);
                        v_isShared_4965_ = v_isSharedCheck_4978_;
                        state = 5;
                        continue;
                    }
                } else {
                    v_a_4979_ = leanh::lean_ctor_get(v_r_4961_, 0);
                    leanh::lean_inc(v_a_4979_);
                    leanh::lean_dec_ref_known(v_r_4961_, 1);
                    v___x_4980_ = leanh::lean_box(0);
                    v___x_4981_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7___redArg___lam__0(v___y_4927_, v_isExporting_4931_, v___x_4945_, v___y_4925_, v___x_4957_, v___x_4980_);
                    v_isSharedCheck_4988_ = (!leanh::lean_is_exclusive(v___x_4981_)) as u8;
                    if v_isSharedCheck_4988_ == 0 {
                        v_unused_4989_ = leanh::lean_ctor_get(v___x_4981_, 0);
                        leanh::lean_dec(v_unused_4989_);
                        v___x_4983_ = v___x_4981_;
                        v_isShared_4984_ = v_isSharedCheck_4988_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_4981_);
                        v___x_4983_ = leanh::lean_box(0);
                        v_isShared_4984_ = v_isSharedCheck_4988_;
                        state = 9;
                        continue;
                    }
                }
            }
            5 => {
                leanh::lean_inc(v_a_4962_);
                if v_isShared_4965_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4964_, 1);
                    v___x_4967_ = v___x_4964_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4977_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4977_, 0, v_a_4962_);
                    v___x_4967_ = v_reuseFailAlloc_4977_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_4968_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7___redArg___lam__0(v___y_4927_, v_isExporting_4931_, v___x_4945_, v___y_4925_, v___x_4957_, v___x_4967_);
                leanh::lean_dec_ref(v___x_4967_);
                v_isSharedCheck_4975_ = (!leanh::lean_is_exclusive(v___x_4968_)) as u8;
                if v_isSharedCheck_4975_ == 0 {
                    v_unused_4976_ = leanh::lean_ctor_get(v___x_4968_, 0);
                    leanh::lean_dec(v_unused_4976_);
                    v___x_4970_ = v___x_4968_;
                    v_isShared_4971_ = v_isSharedCheck_4975_;
                    state = 7;
                    continue;
                } else {
                    leanh::lean_dec(v___x_4968_);
                    v___x_4970_ = leanh::lean_box(0);
                    v_isShared_4971_ = v_isSharedCheck_4975_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_4971_ == 0 {
                    leanh::lean_ctor_set(v___x_4970_, 0, v_a_4962_);
                    v___x_4973_ = v___x_4970_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4974_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4974_, 0, v_a_4962_);
                    v___x_4973_ = v_reuseFailAlloc_4974_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4973_;
            }
            9 => {
                if v_isShared_4984_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4983_, 1);
                    leanh::lean_ctor_set(v___x_4983_, 0, v_a_4979_);
                    v___x_4986_ = v___x_4983_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4987_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4987_, 0, v_a_4979_);
                    v___x_4986_ = v_reuseFailAlloc_4987_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4986_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7___redArg___boxed(
    mut v_declName_4996_: *mut leanh::LeanObject,
    mut v_isExporting_4997_: *mut leanh::LeanObject,
    mut v___y_4998_: *mut leanh::LeanObject,
    mut v___y_4999_: *mut leanh::LeanObject,
    mut v___y_5000_: *mut leanh::LeanObject,
    mut v___y_5001_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isExporting_boxed_5002_: u8 = 0;
    let mut v_res_5003_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_5002_ = (leanh::lean_unbox(v_isExporting_4997_) as u8);
    v_res_5003_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7___redArg(v_declName_4996_, v_isExporting_boxed_5002_, v___y_4998_, v___y_4999_, v___y_5000_);
    leanh::lean_dec(v___y_5000_);
    leanh::lean_dec_ref(v___y_4999_);
    leanh::lean_dec(v___y_4998_);
    return v_res_5003_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7(
    mut v_declName_5004_: *mut leanh::LeanObject,
    mut v_isExporting_5005_: u8,
    mut v___y_5006_: *mut leanh::LeanObject,
    mut v___y_5007_: *mut leanh::LeanObject,
    mut v___y_5008_: *mut leanh::LeanObject,
    mut v___y_5009_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5011_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5011_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7___redArg(v_declName_5004_, v_isExporting_5005_, v___y_5007_, v___y_5008_, v___y_5009_);
    return v___x_5011_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7___boxed(
    mut v_declName_5012_: *mut leanh::LeanObject,
    mut v_isExporting_5013_: *mut leanh::LeanObject,
    mut v___y_5014_: *mut leanh::LeanObject,
    mut v___y_5015_: *mut leanh::LeanObject,
    mut v___y_5016_: *mut leanh::LeanObject,
    mut v___y_5017_: *mut leanh::LeanObject,
    mut v___y_5018_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isExporting_boxed_5019_: u8 = 0;
    let mut v_res_5020_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_5019_ = (leanh::lean_unbox(v_isExporting_5013_) as u8);
    v_res_5020_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7(v_declName_5012_, v_isExporting_boxed_5019_, v___y_5014_, v___y_5015_, v___y_5016_, v___y_5017_);
    leanh::lean_dec(v___y_5017_);
    leanh::lean_dec_ref(v___y_5016_);
    leanh::lean_dec(v___y_5015_);
    leanh::lean_dec_ref(v___y_5014_);
    return v_res_5020_;
}
pub unsafe fn _init_l_Lean_inferDefEqAttr___lam__0___closed__0() -> u64 {
    let mut v___x_5021_: u8 = 0;
    let mut v___x_5022_: u64 = 0;
    v___x_5021_ = 3;
    v___x_5022_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_5021_);
    return v___x_5022_;
}
pub unsafe fn l_Lean_inferDefEqAttr___lam__0(
    mut v_lhs_5023_: *mut leanh::LeanObject,
    mut v_rhs_5024_: *mut leanh::LeanObject,
    mut v___y_5025_: *mut leanh::LeanObject,
    mut v___y_5026_: *mut leanh::LeanObject,
    mut v___y_5027_: *mut leanh::LeanObject,
    mut v___y_5028_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_foApprox_5031_: u8 = 0;
    let mut v_ctxApprox_5032_: u8 = 0;
    let mut v_quasiPatternApprox_5033_: u8 = 0;
    let mut v_constApprox_5034_: u8 = 0;
    let mut v_isDefEqStuckEx_5035_: u8 = 0;
    let mut v_unificationHints_5036_: u8 = 0;
    let mut v_proofIrrelevance_5037_: u8 = 0;
    let mut v_assignSyntheticOpaque_5038_: u8 = 0;
    let mut v_offsetCnstrs_5039_: u8 = 0;
    let mut v_etaStruct_5040_: u8 = 0;
    let mut v_univApprox_5041_: u8 = 0;
    let mut v_iota_5042_: u8 = 0;
    let mut v_beta_5043_: u8 = 0;
    let mut v_proj_5044_: u8 = 0;
    let mut v_zeta_5045_: u8 = 0;
    let mut v_zetaDelta_5046_: u8 = 0;
    let mut v_zetaUnused_5047_: u8 = 0;
    let mut v_zetaHave_5048_: u8 = 0;
    let mut v___x_5050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5051_: u8 = 0;
    let mut v_trackZetaDelta_5052_: u8 = 0;
    let mut v_zetaDeltaSet_5053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_5054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_5055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_5056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_5057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_5058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_5059_: u8 = 0;
    let mut v_inTypeClassResolution_5060_: u8 = 0;
    let mut v_cacheInferType_5061_: u8 = 0;
    let mut v___x_5062_: u8 = 0;
    let mut v_config_5064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5065_: u64 = 0;
    let mut v___x_5066_: u64 = 0;
    let mut v___x_5067_: u64 = 0;
    let mut v___x_5068_: u64 = 0;
    let mut v___x_5069_: u64 = 0;
    let mut v_key_5070_: u64 = 0;
    let mut v___x_5071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5075_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5030_ = l_Lean_Meta_Context_config(v___y_5025_);
                v_foApprox_5031_ = leanh::lean_ctor_get_uint8(v___x_5030_, 0 as u32);
                v_ctxApprox_5032_ = leanh::lean_ctor_get_uint8(v___x_5030_, 1 as u32);
                v_quasiPatternApprox_5033_ =
                    leanh::lean_ctor_get_uint8(v___x_5030_, 2 as u32);
                v_constApprox_5034_ = leanh::lean_ctor_get_uint8(v___x_5030_, 3 as u32);
                v_isDefEqStuckEx_5035_ = leanh::lean_ctor_get_uint8(v___x_5030_, 4 as u32);
                v_unificationHints_5036_ = leanh::lean_ctor_get_uint8(v___x_5030_, 5 as u32);
                v_proofIrrelevance_5037_ = leanh::lean_ctor_get_uint8(v___x_5030_, 6 as u32);
                v_assignSyntheticOpaque_5038_ =
                    leanh::lean_ctor_get_uint8(v___x_5030_, 7 as u32);
                v_offsetCnstrs_5039_ = leanh::lean_ctor_get_uint8(v___x_5030_, 8 as u32);
                v_etaStruct_5040_ = leanh::lean_ctor_get_uint8(v___x_5030_, 10 as u32);
                v_univApprox_5041_ = leanh::lean_ctor_get_uint8(v___x_5030_, 11 as u32);
                v_iota_5042_ = leanh::lean_ctor_get_uint8(v___x_5030_, 12 as u32);
                v_beta_5043_ = leanh::lean_ctor_get_uint8(v___x_5030_, 13 as u32);
                v_proj_5044_ = leanh::lean_ctor_get_uint8(v___x_5030_, 14 as u32);
                v_zeta_5045_ = leanh::lean_ctor_get_uint8(v___x_5030_, 15 as u32);
                v_zetaDelta_5046_ = leanh::lean_ctor_get_uint8(v___x_5030_, 16 as u32);
                v_zetaUnused_5047_ = leanh::lean_ctor_get_uint8(v___x_5030_, 17 as u32);
                v_zetaHave_5048_ = leanh::lean_ctor_get_uint8(v___x_5030_, 18 as u32);
                v_isSharedCheck_5075_ = (!leanh::lean_is_exclusive(v___x_5030_)) as u8;
                if v_isSharedCheck_5075_ == 0 {
                    v___x_5050_ = v___x_5030_;
                    v_isShared_5051_ = v_isSharedCheck_5075_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v___x_5030_);
                    v___x_5050_ = leanh::lean_box(0);
                    v_isShared_5051_ = v_isSharedCheck_5075_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_trackZetaDelta_5052_ = leanh::lean_ctor_get_uint8(
                    v___y_5025_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_5053_ = leanh::lean_ctor_get(v___y_5025_, 1);
                v_lctx_5054_ = leanh::lean_ctor_get(v___y_5025_, 2);
                v_localInstances_5055_ = leanh::lean_ctor_get(v___y_5025_, 3);
                v_defEqCtx_x3f_5056_ = leanh::lean_ctor_get(v___y_5025_, 4);
                v_synthPendingDepth_5057_ = leanh::lean_ctor_get(v___y_5025_, 5);
                v_canUnfold_x3f_5058_ = leanh::lean_ctor_get(v___y_5025_, 6);
                v_univApprox_5059_ = leanh::lean_ctor_get_uint8(
                    v___y_5025_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_5060_ = leanh::lean_ctor_get_uint8(
                    v___y_5025_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_5061_ = leanh::lean_ctor_get_uint8(
                    v___y_5025_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                );
                v___x_5062_ = 3;
                if v_isShared_5051_ == 0 {
                    v_config_5064_ = v___x_5050_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5074_ = leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5074_,
                        0 as u32,
                        v_foApprox_5031_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5074_,
                        1 as u32,
                        v_ctxApprox_5032_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5074_,
                        2 as u32,
                        v_quasiPatternApprox_5033_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5074_,
                        3 as u32,
                        v_constApprox_5034_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5074_,
                        4 as u32,
                        v_isDefEqStuckEx_5035_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5074_,
                        5 as u32,
                        v_unificationHints_5036_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5074_,
                        6 as u32,
                        v_proofIrrelevance_5037_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5074_,
                        7 as u32,
                        v_assignSyntheticOpaque_5038_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5074_,
                        8 as u32,
                        v_offsetCnstrs_5039_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5074_,
                        10 as u32,
                        v_etaStruct_5040_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5074_,
                        11 as u32,
                        v_univApprox_5041_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5074_,
                        12 as u32,
                        v_iota_5042_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5074_,
                        13 as u32,
                        v_beta_5043_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5074_,
                        14 as u32,
                        v_proj_5044_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5074_,
                        15 as u32,
                        v_zeta_5045_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5074_,
                        16 as u32,
                        v_zetaDelta_5046_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5074_,
                        17 as u32,
                        v_zetaUnused_5047_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5074_,
                        18 as u32,
                        v_zetaHave_5048_,
                    );
                    v_config_5064_ = v_reuseFailAlloc_5074_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_ctor_set_uint8(v_config_5064_, 9 as u32, v___x_5062_);
                v___x_5065_ = l_Lean_Meta_Context_configKey(v___y_5025_);
                v___x_5066_ = 3u64;
                v___x_5067_ = lean_uint64_shift_right(v___x_5065_, v___x_5066_);
                v___x_5068_ = lean_uint64_shift_left(v___x_5067_, v___x_5066_);
                v___x_5069_ = leanh::lean_uint64_once(
                    core::ptr::addr_of_mut!(l_Lean_inferDefEqAttr___lam__0___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_inferDefEqAttr___lam__0___closed__0_once),
                    _init_l_Lean_inferDefEqAttr___lam__0___closed__0,
                );
                v_key_5070_ = lean_uint64_lor(v___x_5068_, v___x_5069_);
                v___x_5071_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                leanh::lean_ctor_set(v___x_5071_, 0, v_config_5064_);
                leanh::lean_ctor_set_uint64(
                    v___x_5071_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v_key_5070_,
                );
                leanh::lean_inc(v_canUnfold_x3f_5058_);
                leanh::lean_inc(v_synthPendingDepth_5057_);
                leanh::lean_inc(v_defEqCtx_x3f_5056_);
                leanh::lean_inc_ref(v_localInstances_5055_);
                leanh::lean_inc_ref(v_lctx_5054_);
                leanh::lean_inc(v_zetaDeltaSet_5053_);
                v___x_5072_ = leanh::lean_alloc_ctor(0, 7, (4) as u32);
                leanh::lean_ctor_set(v___x_5072_, 0, v___x_5071_);
                leanh::lean_ctor_set(v___x_5072_, 1, v_zetaDeltaSet_5053_);
                leanh::lean_ctor_set(v___x_5072_, 2, v_lctx_5054_);
                leanh::lean_ctor_set(v___x_5072_, 3, v_localInstances_5055_);
                leanh::lean_ctor_set(v___x_5072_, 4, v_defEqCtx_x3f_5056_);
                leanh::lean_ctor_set(v___x_5072_, 5, v_synthPendingDepth_5057_);
                leanh::lean_ctor_set(v___x_5072_, 6, v_canUnfold_x3f_5058_);
                leanh::lean_ctor_set_uint8(
                    v___x_5072_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_5052_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_5072_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_5059_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_5072_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_5060_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_5072_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_5061_,
                );
                v___x_5073_ = l_Lean_Meta_isExprDefEq(
                    v_lhs_5023_,
                    v_rhs_5024_,
                    v___x_5072_,
                    v___y_5026_,
                    v___y_5027_,
                    v___y_5028_,
                );
                leanh::lean_dec_ref_known(v___x_5072_, 7);
                return v___x_5073_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_inferDefEqAttr___lam__0___boxed(
    mut v_lhs_5076_: *mut leanh::LeanObject,
    mut v_rhs_5077_: *mut leanh::LeanObject,
    mut v___y_5078_: *mut leanh::LeanObject,
    mut v___y_5079_: *mut leanh::LeanObject,
    mut v___y_5080_: *mut leanh::LeanObject,
    mut v___y_5081_: *mut leanh::LeanObject,
    mut v___y_5082_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5083_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5083_ = l_Lean_inferDefEqAttr___lam__0(
        v_lhs_5076_,
        v_rhs_5077_,
        v___y_5078_,
        v___y_5079_,
        v___y_5080_,
        v___y_5081_,
    );
    leanh::lean_dec(v___y_5081_);
    leanh::lean_dec_ref(v___y_5080_);
    leanh::lean_dec(v___y_5079_);
    leanh::lean_dec_ref(v___y_5078_);
    return v_res_5083_;
}
pub unsafe fn _init_l_Lean_inferDefEqAttr___lam__1___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_5085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5086_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5085_ = l_Lean_inferDefEqAttr___lam__1___closed__0;
    v___x_5086_ = l_Lean_stringToMessageData(v___x_5085_);
    return v___x_5086_;
}
pub unsafe fn _init_l_Lean_inferDefEqAttr___lam__1___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_5088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5089_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5088_ = l_Lean_inferDefEqAttr___lam__1___closed__2;
    v___x_5089_ = l_Lean_stringToMessageData(v___x_5088_);
    return v___x_5089_;
}
pub unsafe fn l_Lean_inferDefEqAttr___lam__1(
    mut v_declName_5090_: *mut leanh::LeanObject,
    mut v___f_5091_: *mut leanh::LeanObject,
    mut v___y_5092_: *mut leanh::LeanObject,
    mut v___y_5093_: *mut leanh::LeanObject,
    mut v___y_5094_: *mut leanh::LeanObject,
    mut v___y_5095_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_5098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5109_: u8 = 0;
    let mut v___x_5110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5115_: u8 = 0;
    let mut v___x_5116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5119_: u8 = 0;
    let mut v___x_5120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5127_: u8 = 0;
    let mut v___x_5128_: u8 = 0;
    let mut v___x_5129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5139_: u8 = 0;
    let mut v___x_5140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5142_: u8 = 0;
    let mut v___x_5143_: u8 = 0;
    let mut v___x_5144_: u8 = 0;
    let mut v___x_5145_: u8 = 0;
    let mut v___x_5146_: u8 = 0;
    let mut v_a_5147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5150_: u8 = 0;
    let mut v___x_5152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5154_: u8 = 0;
    let mut v_a_5155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5158_: u8 = 0;
    let mut v___x_5160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5162_: u8 = 0;
    let mut v_a_5163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5166_: u8 = 0;
    let mut v___x_5168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5170_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_declName_5090_);
                v___x_5107_ = l_Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1(
                    v_declName_5090_,
                    v___y_5092_,
                    v___y_5093_,
                    v___y_5094_,
                    v___y_5095_,
                );
                if leanh::lean_obj_tag(v___x_5107_) == 0 {
                    v_a_5108_ = leanh::lean_ctor_get(v___x_5107_, 0);
                    leanh::lean_inc_n(v_a_5108_, 2);
                    leanh::lean_dec_ref_known(v___x_5107_, 1);
                    v___x_5109_ = 1;
                    v___x_5110_ = l_Lean_ConstantInfo_value_x3f(v_a_5108_, v___x_5109_);
                    if leanh::lean_obj_tag(v___x_5110_) == 1 {
                        v_val_5111_ = leanh::lean_ctor_get(v___x_5110_, 0);
                        leanh::lean_inc(v_val_5111_);
                        leanh::lean_dec_ref_known(v___x_5110_, 1);
                        v___x_5112_ = l_Lean_ConstantInfo_type(v_a_5108_);
                        leanh::lean_dec(v_a_5108_);
                        v___x_5113_ = l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg(
                            v___x_5112_,
                            v_val_5111_,
                            v___y_5095_,
                        );
                        if leanh::lean_obj_tag(v___x_5113_) == 0 {
                            v_a_5114_ = leanh::lean_ctor_get(v___x_5113_, 0);
                            leanh::lean_inc(v_a_5114_);
                            leanh::lean_dec_ref_known(v___x_5113_, 1);
                            v___x_5115_ = (leanh::lean_unbox(v_a_5114_) as u8);
                            if v___x_5115_ == 0 {
                                leanh::lean_dec(v_a_5114_);
                                leanh::lean_dec_ref(v___x_5112_);
                                leanh::lean_dec_ref(v___f_5091_);
                                leanh::lean_dec(v_declName_5090_);
                                state = 2;
                                continue;
                            } else {
                                v___x_5116_ =
                                    l___private_Lean_DefEqAttrib_0__Lean_withEqLhsRhs___redArg(
                                        v___x_5112_,
                                        v___f_5091_,
                                        v___y_5092_,
                                        v___y_5093_,
                                        v___y_5094_,
                                        v___y_5095_,
                                    );
                                if leanh::lean_obj_tag(v___x_5116_) == 0 {
                                    v_a_5117_ = leanh::lean_ctor_get(v___x_5116_, 0);
                                    leanh::lean_inc(v_a_5117_);
                                    leanh::lean_dec_ref_known(v___x_5116_, 1);
                                    v___x_5144_ = l_Lean_isPrivateName(v_declName_5090_);
                                    if v___x_5144_ == 0 {
                                        v___x_5145_ = (leanh::lean_unbox(v_a_5114_) as u8);
                                        leanh::lean_dec(v_a_5114_);
                                        v___y_5139_ = v___x_5145_;
                                        state = 6;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v_a_5114_);
                                        v___x_5146_ = 0;
                                        v___y_5139_ = v___x_5146_;
                                        state = 6;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec(v_a_5114_);
                                    leanh::lean_dec(v_declName_5090_);
                                    v_a_5147_ = leanh::lean_ctor_get(v___x_5116_, 0);
                                    v_isSharedCheck_5154_ =
                                        (!leanh::lean_is_exclusive(v___x_5116_)) as u8;
                                    if v_isSharedCheck_5154_ == 0 {
                                        v___x_5149_ = v___x_5116_;
                                        v_isShared_5150_ = v_isSharedCheck_5154_;
                                        state = 7;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_5147_);
                                        leanh::lean_dec(v___x_5116_);
                                        v___x_5149_ = leanh::lean_box(0);
                                        v_isShared_5150_ = v_isSharedCheck_5154_;
                                        state = 7;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v___x_5112_);
                            leanh::lean_dec_ref(v___f_5091_);
                            leanh::lean_dec(v_declName_5090_);
                            v_a_5155_ = leanh::lean_ctor_get(v___x_5113_, 0);
                            v_isSharedCheck_5162_ =
                                (!leanh::lean_is_exclusive(v___x_5113_)) as u8;
                            if v_isSharedCheck_5162_ == 0 {
                                v___x_5157_ = v___x_5113_;
                                v_isShared_5158_ = v_isSharedCheck_5162_;
                                state = 9;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5155_);
                                leanh::lean_dec(v___x_5113_);
                                v___x_5157_ = leanh::lean_box(0);
                                v_isShared_5158_ = v_isSharedCheck_5162_;
                                state = 9;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v___x_5110_);
                        leanh::lean_dec(v_a_5108_);
                        leanh::lean_dec_ref(v___f_5091_);
                        leanh::lean_dec(v_declName_5090_);
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v___f_5091_);
                    leanh::lean_dec(v_declName_5090_);
                    v_a_5163_ = leanh::lean_ctor_get(v___x_5107_, 0);
                    v_isSharedCheck_5170_ = (!leanh::lean_is_exclusive(v___x_5107_)) as u8;
                    if v_isSharedCheck_5170_ == 0 {
                        v___x_5165_ = v___x_5107_;
                        v_isShared_5166_ = v_isSharedCheck_5170_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5163_);
                        leanh::lean_dec(v___x_5107_);
                        v___x_5165_ = leanh::lean_box(0);
                        v_isShared_5166_ = v_isSharedCheck_5170_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5102_ = l_Lean_backwardDefeqAttr;
                v___x_5103_ = l_Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0(
                    v___x_5102_,
                    v_declName_5090_,
                    v___y_5098_,
                    v___y_5099_,
                    v___y_5100_,
                    v___y_5101_,
                );
                return v___x_5103_;
            }
            2 => {
                v___x_5105_ = leanh::lean_box(0);
                v___x_5106_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5106_, 0, v___x_5105_);
                return v___x_5106_;
            }
            3 => {
                v___x_5119_ = (leanh::lean_unbox(v_a_5117_) as u8);
                leanh::lean_dec(v_a_5117_);
                if v___x_5119_ == 0 {
                    v___y_5098_ = v___y_5092_;
                    v___y_5099_ = v___y_5093_;
                    v___y_5100_ = v___y_5094_;
                    v___y_5101_ = v___y_5095_;
                    state = 1;
                    continue;
                } else {
                    v___x_5120_ = l_Lean_defeqAttr;
                    leanh::lean_inc(v_declName_5090_);
                    v___x_5121_ = l_Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0(
                        v___x_5120_,
                        v_declName_5090_,
                        v___y_5092_,
                        v___y_5093_,
                        v___y_5094_,
                        v___y_5095_,
                    );
                    if leanh::lean_obj_tag(v___x_5121_) == 0 {
                        leanh::lean_dec_ref_known(v___x_5121_, 1);
                        v___y_5098_ = v___y_5092_;
                        v___y_5099_ = v___y_5093_;
                        v___y_5100_ = v___y_5094_;
                        v___y_5101_ = v___y_5095_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_declName_5090_);
                        return v___x_5121_;
                    }
                }
            }
            4 => {
                if leanh::lean_obj_tag(v___y_5123_) == 0 {
                    leanh::lean_dec_ref_known(v___y_5123_, 1);
                    state = 3;
                    continue;
                } else {
                    leanh::lean_dec(v_a_5117_);
                    leanh::lean_dec(v_declName_5090_);
                    return v___y_5123_;
                }
            }
            5 => {
                if v___y_5127_ == 0 {
                    leanh::lean_dec_ref(v___y_5126_);
                    v___x_5128_ = (leanh::lean_unbox(v_a_5117_) as u8);
                    if v___x_5128_ == 0 {
                        v___x_5129_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_inferDefEqAttr___lam__1___closed__1),
                            core::ptr::addr_of_mut!(
                                l_Lean_inferDefEqAttr___lam__1___closed__1_once
                            ),
                            _init_l_Lean_inferDefEqAttr___lam__1___closed__1,
                        );
                        leanh::lean_inc(v_declName_5090_);
                        v___x_5130_ = l_Lean_MessageData_ofName(v_declName_5090_);
                        v___x_5131_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_5131_, 0, v___x_5129_);
                        leanh::lean_ctor_set(v___x_5131_, 1, v___x_5130_);
                        v___x_5132_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_inferDefEqAttr___lam__1___closed__3),
                            core::ptr::addr_of_mut!(
                                l_Lean_inferDefEqAttr___lam__1___closed__3_once
                            ),
                            _init_l_Lean_inferDefEqAttr___lam__1___closed__3,
                        );
                        v___x_5133_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_5133_, 0, v___x_5131_);
                        leanh::lean_ctor_set(v___x_5133_, 1, v___x_5132_);
                        v___x_5134_ = l_Lean_Exception_toMessageData(v___y_5125_);
                        v___x_5135_ = l_Lean_indentD(v___x_5134_);
                        v___x_5136_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_5136_, 0, v___x_5133_);
                        leanh::lean_ctor_set(v___x_5136_, 1, v___x_5135_);
                        v___x_5137_ = l_Lean_logError___at___00Lean_inferDefEqAttr_spec__2(
                            v___x_5136_,
                            v___y_5092_,
                            v___y_5093_,
                            v___y_5094_,
                            v___y_5095_,
                        );
                        v___y_5123_ = v___x_5137_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v___y_5125_);
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v___y_5125_);
                    v___y_5123_ = v___y_5126_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                leanh::lean_inc(v_declName_5090_);
                v___x_5140_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0_spec__0___at___00Lean_inferDefEqAttr_spec__7___redArg(v_declName_5090_, v___y_5139_, v___y_5093_, v___y_5094_, v___y_5095_);
                if leanh::lean_obj_tag(v___x_5140_) == 0 {
                    v___y_5123_ = v___x_5140_;
                    state = 4;
                    continue;
                } else {
                    v_a_5141_ = leanh::lean_ctor_get(v___x_5140_, 0);
                    leanh::lean_inc(v_a_5141_);
                    v___x_5142_ = l_Lean_Exception_isInterrupt(v_a_5141_);
                    if v___x_5142_ == 0 {
                        leanh::lean_inc(v_a_5141_);
                        v___x_5143_ = l_Lean_Exception_isRuntime(v_a_5141_);
                        v___y_5125_ = v_a_5141_;
                        v___y_5126_ = v___x_5140_;
                        v___y_5127_ = v___x_5143_;
                        state = 5;
                        continue;
                    } else {
                        v___y_5125_ = v_a_5141_;
                        v___y_5126_ = v___x_5140_;
                        v___y_5127_ = v___x_5142_;
                        state = 5;
                        continue;
                    }
                }
            }
            7 => {
                if v_isShared_5150_ == 0 {
                    v___x_5152_ = v___x_5149_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5153_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5153_, 0, v_a_5147_);
                    v___x_5152_ = v_reuseFailAlloc_5153_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5152_;
            }
            9 => {
                if v_isShared_5158_ == 0 {
                    v___x_5160_ = v___x_5157_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5161_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5161_, 0, v_a_5155_);
                    v___x_5160_ = v_reuseFailAlloc_5161_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5160_;
            }
            11 => {
                if v_isShared_5166_ == 0 {
                    v___x_5168_ = v___x_5165_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5169_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5169_, 0, v_a_5163_);
                    v___x_5168_ = v_reuseFailAlloc_5169_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5168_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_inferDefEqAttr___lam__1___boxed(
    mut v_declName_5171_: *mut leanh::LeanObject,
    mut v___f_5172_: *mut leanh::LeanObject,
    mut v___y_5173_: *mut leanh::LeanObject,
    mut v___y_5174_: *mut leanh::LeanObject,
    mut v___y_5175_: *mut leanh::LeanObject,
    mut v___y_5176_: *mut leanh::LeanObject,
    mut v___y_5177_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5178_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5178_ = l_Lean_inferDefEqAttr___lam__1(
        v_declName_5171_,
        v___f_5172_,
        v___y_5173_,
        v___y_5174_,
        v___y_5175_,
        v___y_5176_,
    );
    leanh::lean_dec(v___y_5176_);
    leanh::lean_dec_ref(v___y_5175_);
    leanh::lean_dec(v___y_5174_);
    leanh::lean_dec_ref(v___y_5173_);
    return v_res_5178_;
}
pub unsafe fn l_Lean_inferDefEqAttr(
    mut v_declName_5180_: *mut leanh::LeanObject,
    mut v_a_5181_: *mut leanh::LeanObject,
    mut v_a_5182_: *mut leanh::LeanObject,
    mut v_a_5183_: *mut leanh::LeanObject,
    mut v_a_5184_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5188_: u8 = 0;
    let mut v___x_5189_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_5186_ = l_Lean_inferDefEqAttr___closed__0;
    v___f_5187_ = leanh::lean_alloc_closure(
        l_Lean_inferDefEqAttr___lam__1___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___f_5187_, 0, v_declName_5180_);
    leanh::lean_closure_set(v___f_5187_, 1, v___f_5186_);
    v___x_5188_ = 1;
    v___x_5189_ = l_Lean_withoutExporting___at___00Lean_validateDefEqAttr_spec__0___redArg(
        v___f_5187_,
        v___x_5188_,
        v_a_5181_,
        v_a_5182_,
        v_a_5183_,
        v_a_5184_,
    );
    return v___x_5189_;
}
pub unsafe fn l_Lean_inferDefEqAttr___boxed(
    mut v_declName_5190_: *mut leanh::LeanObject,
    mut v_a_5191_: *mut leanh::LeanObject,
    mut v_a_5192_: *mut leanh::LeanObject,
    mut v_a_5193_: *mut leanh::LeanObject,
    mut v_a_5194_: *mut leanh::LeanObject,
    mut v_a_5195_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5196_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5196_ =
        l_Lean_inferDefEqAttr(v_declName_5190_, v_a_5191_, v_a_5192_, v_a_5193_, v_a_5194_);
    leanh::lean_dec(v_a_5194_);
    leanh::lean_dec_ref(v_a_5193_);
    leanh::lean_dec(v_a_5192_);
    leanh::lean_dec_ref(v_a_5191_);
    return v_res_5196_;
}
pub unsafe fn l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__0(
    mut v_00_u03b1_5197_: *mut leanh::LeanObject,
    mut v_attrName_5198_: *mut leanh::LeanObject,
    mut v_declName_5199_: *mut leanh::LeanObject,
    mut v_asyncPrefix_x3f_5200_: *mut leanh::LeanObject,
    mut v___y_5201_: *mut leanh::LeanObject,
    mut v___y_5202_: *mut leanh::LeanObject,
    mut v___y_5203_: *mut leanh::LeanObject,
    mut v___y_5204_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5206_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5206_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__0___redArg(v_attrName_5198_, v_declName_5199_, v_asyncPrefix_x3f_5200_, v___y_5201_, v___y_5202_, v___y_5203_, v___y_5204_);
    return v___x_5206_;
}
pub unsafe fn l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__0___boxed(
    mut v_00_u03b1_5207_: *mut leanh::LeanObject,
    mut v_attrName_5208_: *mut leanh::LeanObject,
    mut v_declName_5209_: *mut leanh::LeanObject,
    mut v_asyncPrefix_x3f_5210_: *mut leanh::LeanObject,
    mut v___y_5211_: *mut leanh::LeanObject,
    mut v___y_5212_: *mut leanh::LeanObject,
    mut v___y_5213_: *mut leanh::LeanObject,
    mut v___y_5214_: *mut leanh::LeanObject,
    mut v___y_5215_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5216_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5216_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__0(v_00_u03b1_5207_, v_attrName_5208_, v_declName_5209_, v_asyncPrefix_x3f_5210_, v___y_5211_, v___y_5212_, v___y_5213_, v___y_5214_);
    leanh::lean_dec(v___y_5214_);
    leanh::lean_dec_ref(v___y_5213_);
    leanh::lean_dec(v___y_5212_);
    leanh::lean_dec_ref(v___y_5211_);
    return v_res_5216_;
}
pub unsafe fn l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__1(
    mut v_00_u03b1_5217_: *mut leanh::LeanObject,
    mut v_attrName_5218_: *mut leanh::LeanObject,
    mut v_declName_5219_: *mut leanh::LeanObject,
    mut v___y_5220_: *mut leanh::LeanObject,
    mut v___y_5221_: *mut leanh::LeanObject,
    mut v___y_5222_: *mut leanh::LeanObject,
    mut v___y_5223_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5225_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5225_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__1___redArg(v_attrName_5218_, v_declName_5219_, v___y_5220_, v___y_5221_, v___y_5222_, v___y_5223_);
    return v___x_5225_;
}
pub unsafe fn l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__1___boxed(
    mut v_00_u03b1_5226_: *mut leanh::LeanObject,
    mut v_attrName_5227_: *mut leanh::LeanObject,
    mut v_declName_5228_: *mut leanh::LeanObject,
    mut v___y_5229_: *mut leanh::LeanObject,
    mut v___y_5230_: *mut leanh::LeanObject,
    mut v___y_5231_: *mut leanh::LeanObject,
    mut v___y_5232_: *mut leanh::LeanObject,
    mut v___y_5233_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5234_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5234_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_inferDefEqAttr_spec__0_spec__1(v_00_u03b1_5226_, v_attrName_5227_, v_declName_5228_, v___y_5229_, v___y_5230_, v___y_5231_, v___y_5232_);
    leanh::lean_dec(v___y_5232_);
    leanh::lean_dec_ref(v___y_5231_);
    leanh::lean_dec(v___y_5230_);
    leanh::lean_dec_ref(v___y_5229_);
    return v_res_5234_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3(
    mut v_00_u03b1_5235_: *mut leanh::LeanObject,
    mut v_constName_5236_: *mut leanh::LeanObject,
    mut v___y_5237_: *mut leanh::LeanObject,
    mut v___y_5238_: *mut leanh::LeanObject,
    mut v___y_5239_: *mut leanh::LeanObject,
    mut v___y_5240_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5242_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5242_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3___redArg(v_constName_5236_, v___y_5237_, v___y_5238_, v___y_5239_, v___y_5240_);
    return v___x_5242_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3___boxed(
    mut v_00_u03b1_5243_: *mut leanh::LeanObject,
    mut v_constName_5244_: *mut leanh::LeanObject,
    mut v___y_5245_: *mut leanh::LeanObject,
    mut v___y_5246_: *mut leanh::LeanObject,
    mut v___y_5247_: *mut leanh::LeanObject,
    mut v___y_5248_: *mut leanh::LeanObject,
    mut v___y_5249_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5250_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5250_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3(v_00_u03b1_5243_, v_constName_5244_, v___y_5245_, v___y_5246_, v___y_5247_, v___y_5248_);
    leanh::lean_dec(v___y_5248_);
    leanh::lean_dec_ref(v___y_5247_);
    leanh::lean_dec(v___y_5246_);
    leanh::lean_dec_ref(v___y_5245_);
    return v_res_5250_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3(
    mut v_00_u03b1_5251_: *mut leanh::LeanObject,
    mut v_ref_5252_: *mut leanh::LeanObject,
    mut v_constName_5253_: *mut leanh::LeanObject,
    mut v___y_5254_: *mut leanh::LeanObject,
    mut v___y_5255_: *mut leanh::LeanObject,
    mut v___y_5256_: *mut leanh::LeanObject,
    mut v___y_5257_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5259_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5259_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3___redArg(v_ref_5252_, v_constName_5253_, v___y_5254_, v___y_5255_, v___y_5256_, v___y_5257_);
    return v___x_5259_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3___boxed(
    mut v_00_u03b1_5260_: *mut leanh::LeanObject,
    mut v_ref_5261_: *mut leanh::LeanObject,
    mut v_constName_5262_: *mut leanh::LeanObject,
    mut v___y_5263_: *mut leanh::LeanObject,
    mut v___y_5264_: *mut leanh::LeanObject,
    mut v___y_5265_: *mut leanh::LeanObject,
    mut v___y_5266_: *mut leanh::LeanObject,
    mut v___y_5267_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5268_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5268_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3(v_00_u03b1_5260_, v_ref_5261_, v_constName_5262_, v___y_5263_, v___y_5264_, v___y_5265_, v___y_5266_);
    leanh::lean_dec(v___y_5266_);
    leanh::lean_dec_ref(v___y_5265_);
    leanh::lean_dec(v___y_5264_);
    leanh::lean_dec_ref(v___y_5263_);
    leanh::lean_dec(v_ref_5261_);
    return v_res_5268_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7(
    mut v_00_u03b1_5269_: *mut leanh::LeanObject,
    mut v_ref_5270_: *mut leanh::LeanObject,
    mut v_msg_5271_: *mut leanh::LeanObject,
    mut v_declHint_5272_: *mut leanh::LeanObject,
    mut v___y_5273_: *mut leanh::LeanObject,
    mut v___y_5274_: *mut leanh::LeanObject,
    mut v___y_5275_: *mut leanh::LeanObject,
    mut v___y_5276_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5278_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5278_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7___redArg(v_ref_5270_, v_msg_5271_, v_declHint_5272_, v___y_5273_, v___y_5274_, v___y_5275_, v___y_5276_);
    return v___x_5278_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7___boxed(
    mut v_00_u03b1_5279_: *mut leanh::LeanObject,
    mut v_ref_5280_: *mut leanh::LeanObject,
    mut v_msg_5281_: *mut leanh::LeanObject,
    mut v_declHint_5282_: *mut leanh::LeanObject,
    mut v___y_5283_: *mut leanh::LeanObject,
    mut v___y_5284_: *mut leanh::LeanObject,
    mut v___y_5285_: *mut leanh::LeanObject,
    mut v___y_5286_: *mut leanh::LeanObject,
    mut v___y_5287_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5288_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5288_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7(v_00_u03b1_5279_, v_ref_5280_, v_msg_5281_, v_declHint_5282_, v___y_5283_, v___y_5284_, v___y_5285_, v___y_5286_);
    leanh::lean_dec(v___y_5286_);
    leanh::lean_dec_ref(v___y_5285_);
    leanh::lean_dec(v___y_5284_);
    leanh::lean_dec_ref(v___y_5283_);
    leanh::lean_dec(v_ref_5280_);
    return v_res_5288_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9_spec__11(
    mut v_msg_5289_: *mut leanh::LeanObject,
    mut v_declHint_5290_: *mut leanh::LeanObject,
    mut v___y_5291_: *mut leanh::LeanObject,
    mut v___y_5292_: *mut leanh::LeanObject,
    mut v___y_5293_: *mut leanh::LeanObject,
    mut v___y_5294_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5296_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5296_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9_spec__11___redArg(v_msg_5289_, v_declHint_5290_, v___y_5294_);
    return v___x_5296_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9_spec__11___boxed(
    mut v_msg_5297_: *mut leanh::LeanObject,
    mut v_declHint_5298_: *mut leanh::LeanObject,
    mut v___y_5299_: *mut leanh::LeanObject,
    mut v___y_5300_: *mut leanh::LeanObject,
    mut v___y_5301_: *mut leanh::LeanObject,
    mut v___y_5302_: *mut leanh::LeanObject,
    mut v___y_5303_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5304_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5304_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__9_spec__11(v_msg_5297_, v_declHint_5298_, v___y_5299_, v___y_5300_, v___y_5301_, v___y_5302_);
    leanh::lean_dec(v___y_5302_);
    leanh::lean_dec_ref(v___y_5301_);
    leanh::lean_dec(v___y_5300_);
    leanh::lean_dec_ref(v___y_5299_);
    return v_res_5304_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__10(
    mut v_00_u03b1_5305_: *mut leanh::LeanObject,
    mut v_ref_5306_: *mut leanh::LeanObject,
    mut v_msg_5307_: *mut leanh::LeanObject,
    mut v___y_5308_: *mut leanh::LeanObject,
    mut v___y_5309_: *mut leanh::LeanObject,
    mut v___y_5310_: *mut leanh::LeanObject,
    mut v___y_5311_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5313_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5313_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__10___redArg(v_ref_5306_, v_msg_5307_, v___y_5308_, v___y_5309_, v___y_5310_, v___y_5311_);
    return v___x_5313_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__10___boxed(
    mut v_00_u03b1_5314_: *mut leanh::LeanObject,
    mut v_ref_5315_: *mut leanh::LeanObject,
    mut v_msg_5316_: *mut leanh::LeanObject,
    mut v___y_5317_: *mut leanh::LeanObject,
    mut v___y_5318_: *mut leanh::LeanObject,
    mut v___y_5319_: *mut leanh::LeanObject,
    mut v___y_5320_: *mut leanh::LeanObject,
    mut v___y_5321_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5322_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5322_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_inferDefEqAttr_spec__1_spec__3_spec__3_spec__7_spec__10(v_00_u03b1_5314_, v_ref_5315_, v_msg_5316_, v___y_5317_, v___y_5318_, v___y_5319_, v___y_5320_);
    leanh::lean_dec(v___y_5320_);
    leanh::lean_dec_ref(v___y_5319_);
    leanh::lean_dec(v___y_5318_);
    leanh::lean_dec_ref(v___y_5317_);
    leanh::lean_dec(v_ref_5315_);
    return v_res_5322_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_DefEqAttrib(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Check(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_WHNF(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_4069019935____hygCtx___hyg_4_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_backward_defeqAttrib_useBackward = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_backward_defeqAttrib_useBackward);
    leanh::lean_dec_ref(res);
    res = l___private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_1921203779____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_backwardDefeqAttr = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_backwardDefeqAttr);
    leanh::lean_dec_ref(res);
    res = l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_docString__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_DefEqAttrib_0__Lean_backwardDefeqAttr___regBuiltin_Lean_backwardDefeqAttr_declRange__3();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_DefEqAttrib_0__Lean_initFn_00___x40_Lean_DefEqAttrib_3492555791____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_defeqAttr = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_defeqAttr);
    leanh::lean_dec_ref(res);
    res = l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_docString__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_DefEqAttrib_0__Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_DefEqAttrib(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_DefEqAttrib(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Check(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_WHNF(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_DefEqAttrib(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_DefEqAttrib(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_DefEqAttrib(builtin);
}