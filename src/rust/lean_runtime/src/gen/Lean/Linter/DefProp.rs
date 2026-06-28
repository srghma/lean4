// Lean compiler output
// Module: Lean.Linter.DefProp
// Imports: Lean.Linter.Basic Lean.Linter.Util
use crate::r#gen::Init::Data::List::BasicAux::l_List_head_x21___redArg;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr2, l_Lean_Name_mkStr4, l_Lean_Syntax_getPos_x3f, l_Lean_Syntax_getTailPos_x3f,
    l_Lean_replaceRef,
};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::Options::lean_register_option;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Data::Position::l_Lean_FileMap_toPosition;
use crate::r#gen::Lean::Declaration::{l_Lean_ConstantInfo_isDefinition, l_Lean_ConstantInfo_type};
use crate::r#gen::Lean::Elab::Command::Scope::l_Lean_Elab_Command_instInhabitedScope_default;
use crate::r#gen::Lean::Elab::Command::{
    l_Lean_Elab_Command_addLinter, l_Lean_Elab_Command_getRef___redArg,
    l_Lean_Elab_Command_getScope___redArg, l_Lean_Elab_Command_liftTermElabM___redArg,
};
use crate::r#gen::Lean::EnvExtension::l_Lean_SimplePersistentEnvExtension_getState___redArg;
use crate::r#gen::Lean::Environment::l_Lean_Environment_find_x3f;
use crate::r#gen::Lean::Linter::Basic::{
    initialize_Lean_Linter_Basic, l_Lean_withSetOptionIn___boxed,
    runtime_initialize_Lean_Linter_Basic,
};
use crate::r#gen::Lean::Linter::Init::{
    l_Lean_Linter_getLinterValue, l_Lean_Linter_linterMessageTag, l_Lean_Linter_linterSetsExt,
};
use crate::r#gen::Lean::Linter::Util::{
    initialize_Lean_Linter_Util, l_Lean_Linter_getDeclsByBody, runtime_initialize_Lean_Linter_Util,
};
use crate::r#gen::Lean::Log::{
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed, l_Lean_warningAsError,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_hasSyntheticSorry, l_Lean_MessageData_hasTag, l_Lean_MessageData_note,
    l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofName, l_Lean_MessageLog_add,
    l_Lean_MessageLog_hasErrors, l_Lean_instBEqMessageSeverity_beq, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::InferType::l_Lean_Meta_isProp;
use crate::lean_imports_rs::Init::Data::Array::Basic::{lean_array_size, lean_array_uget_borrowed};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_dec_lt};
use crate::lean_imports_rs::Init::Prelude::{
    lean_mk_empty_array_with_capacity, lean_string_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
pub static l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [108, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [100, 101, 102, 80, 114, 111, 112, 0]};
static mut l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,5701751079888345786 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,2059996878919343056 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<175> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 175, m_capacity: 175, m_length: 174, m_data: [101, 110, 97, 98, 108, 101, 32, 116, 104, 101, 32, 96, 100, 101, 102, 80, 114, 111, 112, 96, 32, 108, 105, 110, 116, 101, 114, 44, 32, 119, 104, 105, 99, 104, 32, 119, 97, 114, 110, 115, 32, 119, 104, 101, 110, 32, 97, 32, 96, 100, 101, 102, 96, 32, 105, 115, 32, 117, 115, 101, 100, 32, 116, 111, 32, 105, 110, 116, 114, 111, 100, 117, 99, 101, 32, 97, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 119, 104, 111, 115, 101, 32, 116, 121, 112, 101, 32, 105, 115, 32, 97, 32, 96, 80, 114, 111, 112, 96, 59, 32, 115, 117, 99, 104, 32, 97, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 115, 104, 111, 117, 108, 100, 32, 98, 101, 32, 119, 114, 105, 116, 116, 101, 110, 32, 117, 115, 105, 110, 103, 32, 96, 116, 104, 101, 111, 114, 101, 109, 96, 32, 105, 110, 115, 116, 101, 97, 100, 46, 0]};
static mut l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [76, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,8071394701935581384 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,6326339448686113589 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,17709351088905653771 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7___lam__0___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7___closed__0_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3___closed__0_value: crate::leanh::LeanStringObject<46> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 46, m_capacity: 46, m_length: 45, m_data: [84, 104, 105, 115, 32, 108, 105, 110, 116, 101, 114, 32, 99, 97, 110, 32, 98, 101, 32, 100, 105, 115, 97, 98, 108, 101, 100, 32, 119, 105, 116, 104, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 0]};
static mut l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3___closed__2_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [32, 102, 97, 108, 115, 101, 96, 0]};
static mut l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___closed__0_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [68, 101, 102, 105, 110, 105, 116, 105, 111, 110, 32, 96, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___closed__2_value: crate::leanh::LeanStringObject<51> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 51, m_capacity: 51, m_length: 50, m_data: [96, 32, 105, 115, 32, 97, 32, 112, 114, 111, 112, 111, 115, 105, 116, 105, 111, 110, 59, 32, 117, 115, 101, 32, 96, 116, 104, 101, 111, 114, 101, 109, 96, 32, 105, 110, 115, 116, 101, 97, 100, 32, 111, 102, 32, 96, 100, 101, 102, 96, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__9_spec__11___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__9_spec__11___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__9_spec__11___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__7_spec__11___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__7_spec__11___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__7_spec__11___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_DefProp_defPropLinter___closed__0_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Linter_DefProp_defPropLinter___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Linter_DefProp_defPropLinter___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_DefProp_defPropLinter___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_DefProp_defPropLinter___closed__1_value: crate::leanh::LeanClosureObject<
    1,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_withSetOptionIn___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Linter_DefProp_defPropLinter___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Linter_DefProp_defPropLinter___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_DefProp_defPropLinter___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_DefProp_defPropLinter___closed__2_value: crate::leanh::LeanStringObject<
    8,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [68, 101, 102, 80, 114, 111, 112, 0],
};
static mut l_Lean_Linter_DefProp_defPropLinter___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_DefProp_defPropLinter___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_DefProp_defPropLinter___closed__3_value: crate::leanh::LeanStringObject<
    14,
> = crate::leanh::LeanStringObject {
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
        100, 101, 102, 80, 114, 111, 112, 76, 105, 110, 116, 101, 114, 0,
    ],
};
static mut l_Lean_Linter_DefProp_defPropLinter___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_DefProp_defPropLinter___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Linter_DefProp_defPropLinter___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Linter_DefProp_defPropLinter___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter_DefProp_defPropLinter___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,8071394701935581384 as *mut crate::leanh::LeanObject] };
static l_Lean_Linter_DefProp_defPropLinter___closed__4_value_aux_2: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Linter_DefProp_defPropLinter___closed__4_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_DefProp_defPropLinter___closed__2_value)
            as *mut crate::leanh::LeanObject,
        15042266981743045221 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Linter_DefProp_defPropLinter___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Linter_DefProp_defPropLinter___closed__4_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_DefProp_defPropLinter___closed__3_value)
                as *mut crate::leanh::LeanObject,
            11491196682244663709 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Linter_DefProp_defPropLinter___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_DefProp_defPropLinter___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_DefProp_defPropLinter___closed__5_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_DefProp_defPropLinter___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_DefProp_defPropLinter___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Linter_DefProp_defPropLinter___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_DefProp_defPropLinter___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Linter_DefProp_defPropLinter: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_DefProp_defPropLinter___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Linter_DefProp_0__Lean_Linter_initFn_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__spec__0(
    mut v_name_956_: *mut crate::leanh::LeanObject,
    mut v_decl_957_: *mut crate::leanh::LeanObject,
    mut v_ref_958_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_defValue_960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_descr_961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_964_: u8 = 0;
    let mut v___x_965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_969_: u8 = 0;
    let mut v___x_970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_974_: u8 = 0;
    let mut v_unused_975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_979_: u8 = 0;
    let mut v___x_981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_983_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_960_ = crate::leanh::lean_ctor_get(v_decl_957_, 0);
                v_descr_961_ = crate::leanh::lean_ctor_get(v_decl_957_, 1);
                v_deprecation_x3f_962_ = crate::leanh::lean_ctor_get(v_decl_957_, 2);
                v___x_963_ = crate::leanh::lean_alloc_ctor(1, 0, (1) as u32);
                v___x_964_ = (crate::leanh::lean_unbox(v_defValue_960_) as u8);
                crate::leanh::lean_ctor_set_uint8(v___x_963_, 0 as u32, v___x_964_);
                crate::leanh::lean_inc(v_deprecation_x3f_962_);
                crate::leanh::lean_inc_ref(v_descr_961_);
                crate::leanh::lean_inc_n(v_name_956_, 2);
                v___x_965_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_965_, 0, v_name_956_);
                crate::leanh::lean_ctor_set(v___x_965_, 1, v_ref_958_);
                crate::leanh::lean_ctor_set(v___x_965_, 2, v___x_963_);
                crate::leanh::lean_ctor_set(v___x_965_, 3, v_descr_961_);
                crate::leanh::lean_ctor_set(v___x_965_, 4, v_deprecation_x3f_962_);
                v___x_966_ = lean_register_option(v_name_956_, v___x_965_);
                if crate::leanh::lean_obj_tag(v___x_966_) == 0 {
                    v_isSharedCheck_974_ = (!crate::leanh::lean_is_exclusive(v___x_966_)) as u8;
                    if v_isSharedCheck_974_ == 0 {
                        v_unused_975_ = crate::leanh::lean_ctor_get(v___x_966_, 0);
                        crate::leanh::lean_dec(v_unused_975_);
                        v___x_968_ = v___x_966_;
                        v_isShared_969_ = v_isSharedCheck_974_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_966_);
                        v___x_968_ = crate::leanh::lean_box(0);
                        v_isShared_969_ = v_isSharedCheck_974_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_name_956_);
                    v_a_976_ = crate::leanh::lean_ctor_get(v___x_966_, 0);
                    v_isSharedCheck_983_ = (!crate::leanh::lean_is_exclusive(v___x_966_)) as u8;
                    if v_isSharedCheck_983_ == 0 {
                        v___x_978_ = v___x_966_;
                        v_isShared_979_ = v_isSharedCheck_983_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_976_);
                        crate::leanh::lean_dec(v___x_966_);
                        v___x_978_ = crate::leanh::lean_box(0);
                        v_isShared_979_ = v_isSharedCheck_983_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_defValue_960_);
                v___x_970_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_970_, 0, v_name_956_);
                crate::leanh::lean_ctor_set(v___x_970_, 1, v_defValue_960_);
                if v_isShared_969_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_968_, 0, v___x_970_);
                    v___x_972_ = v___x_968_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_973_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_973_, 0, v___x_970_);
                    v___x_972_ = v_reuseFailAlloc_973_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_972_;
            }
            3 => {
                if v_isShared_979_ == 0 {
                    v___x_981_ = v___x_978_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_982_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_982_, 0, v_a_976_);
                    v___x_981_ = v_reuseFailAlloc_982_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_981_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Linter_DefProp_0__Lean_Linter_initFn_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__spec__0___boxed(
    mut v_name_984_: *mut crate::leanh::LeanObject,
    mut v_decl_985_: *mut crate::leanh::LeanObject,
    mut v_ref_986_: *mut crate::leanh::LeanObject,
    mut v_a_987_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_988_ = l_Lean_Option_register___at___00__private_Lean_Linter_DefProp_0__Lean_Linter_initFn_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__spec__0(v_name_984_, v_decl_985_, v_ref_986_);
    crate::leanh::lean_dec_ref(v_decl_985_);
    return v_res_988_;
}
pub unsafe fn l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1008_ = l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4_;
    v___x_1009_ = l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4_;
    v___x_1010_ = l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4_;
    v___x_1011_ = l_Lean_Option_register___at___00__private_Lean_Linter_DefProp_0__Lean_Linter_initFn_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__spec__0(v___x_1008_, v___x_1009_, v___x_1010_);
    return v___x_1011_;
}
pub unsafe fn l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4____boxed(
    mut v_a_1012_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1013_ = l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4_();
    return v_res_1013_;
}
pub unsafe fn l_Lean_Elab_getInfoTrees___at___00Lean_Linter_DefProp_defPropLinter_spec__1___redArg(
    mut v___y_1014_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trees_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1016_ = lean_st_ref_get(v___y_1014_);
    v_infoState_1017_ = crate::leanh::lean_ctor_get(v___x_1016_, 8);
    crate::leanh::lean_inc_ref(v_infoState_1017_);
    crate::leanh::lean_dec(v___x_1016_);
    v_trees_1018_ = crate::leanh::lean_ctor_get(v_infoState_1017_, 2);
    crate::leanh::lean_inc_ref(v_trees_1018_);
    crate::leanh::lean_dec_ref(v_infoState_1017_);
    v___x_1019_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1019_, 0, v_trees_1018_);
    return v___x_1019_;
}
pub unsafe fn l_Lean_Elab_getInfoTrees___at___00Lean_Linter_DefProp_defPropLinter_spec__1___redArg___boxed(
    mut v___y_1020_: *mut crate::leanh::LeanObject,
    mut v___y_1021_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1022_ =
        l_Lean_Elab_getInfoTrees___at___00Lean_Linter_DefProp_defPropLinter_spec__1___redArg(
            v___y_1020_,
        );
    crate::leanh::lean_dec(v___y_1020_);
    return v_res_1022_;
}
pub unsafe fn l_Lean_Elab_getInfoTrees___at___00Lean_Linter_DefProp_defPropLinter_spec__1(
    mut v___y_1023_: *mut crate::leanh::LeanObject,
    mut v___y_1024_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1026_ =
        l_Lean_Elab_getInfoTrees___at___00Lean_Linter_DefProp_defPropLinter_spec__1___redArg(
            v___y_1024_,
        );
    return v___x_1026_;
}
pub unsafe fn l_Lean_Elab_getInfoTrees___at___00Lean_Linter_DefProp_defPropLinter_spec__1___boxed(
    mut v___y_1027_: *mut crate::leanh::LeanObject,
    mut v___y_1028_: *mut crate::leanh::LeanObject,
    mut v___y_1029_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1030_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_DefProp_defPropLinter_spec__1(
        v___y_1027_,
        v___y_1028_,
    );
    crate::leanh::lean_dec(v___y_1028_);
    crate::leanh::lean_dec_ref(v___y_1027_);
    return v_res_1030_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_DefProp_defPropLinter_spec__0_spec__0___redArg(
    mut v_o_1031_: *mut crate::leanh::LeanObject,
    mut v___y_1032_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_1037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_1038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_linterSets_1041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1034_ = lean_st_ref_get(v___y_1032_);
    v_env_1035_ = crate::leanh::lean_ctor_get(v___x_1034_, 0);
    crate::leanh::lean_inc_ref(v_env_1035_);
    crate::leanh::lean_dec(v___x_1034_);
    v___x_1036_ = l_Lean_Linter_linterSetsExt;
    v_toEnvExtension_1037_ = crate::leanh::lean_ctor_get(v___x_1036_, 0);
    v_asyncMode_1038_ = crate::leanh::lean_ctor_get(v_toEnvExtension_1037_, 2);
    v___x_1039_ = crate::leanh::lean_box(1);
    v___x_1040_ = crate::leanh::lean_box(0);
    v_linterSets_1041_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
        v___x_1039_,
        v___x_1036_,
        v_env_1035_,
        v_asyncMode_1038_,
        v___x_1040_,
    );
    v___x_1042_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1042_, 0, v_o_1031_);
    crate::leanh::lean_ctor_set(v___x_1042_, 1, v_linterSets_1041_);
    v___x_1043_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1043_, 0, v___x_1042_);
    return v___x_1043_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_DefProp_defPropLinter_spec__0_spec__0___redArg___boxed(
    mut v_o_1044_: *mut crate::leanh::LeanObject,
    mut v___y_1045_: *mut crate::leanh::LeanObject,
    mut v___y_1046_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1047_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_DefProp_defPropLinter_spec__0_spec__0___redArg(v_o_1044_, v___y_1045_);
    crate::leanh::lean_dec(v___y_1045_);
    return v_res_1047_;
}
pub unsafe fn l_Lean_Linter_getLinterOptions___at___00Lean_Linter_DefProp_defPropLinter_spec__0(
    mut v___y_1048_: *mut crate::leanh::LeanObject,
    mut v___y_1049_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_1052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_1055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1051_ = lean_st_ref_get(v___y_1049_);
    v_scopes_1052_ = crate::leanh::lean_ctor_get(v___x_1051_, 2);
    crate::leanh::lean_inc(v_scopes_1052_);
    crate::leanh::lean_dec(v___x_1051_);
    v___x_1053_ = l_Lean_Elab_Command_instInhabitedScope_default;
    v___x_1054_ = l_List_head_x21___redArg(v___x_1053_, v_scopes_1052_);
    crate::leanh::lean_dec(v_scopes_1052_);
    v_opts_1055_ = crate::leanh::lean_ctor_get(v___x_1054_, 1);
    crate::leanh::lean_inc_ref(v_opts_1055_);
    crate::leanh::lean_dec(v___x_1054_);
    v___x_1056_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_DefProp_defPropLinter_spec__0_spec__0___redArg(v_opts_1055_, v___y_1049_);
    return v___x_1056_;
}
pub unsafe fn l_Lean_Linter_getLinterOptions___at___00Lean_Linter_DefProp_defPropLinter_spec__0___boxed(
    mut v___y_1057_: *mut crate::leanh::LeanObject,
    mut v___y_1058_: *mut crate::leanh::LeanObject,
    mut v___y_1059_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1060_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_DefProp_defPropLinter_spec__0(
        v___y_1057_,
        v___y_1058_,
    );
    crate::leanh::lean_dec(v___y_1058_);
    crate::leanh::lean_dec_ref(v___y_1057_);
    return v_res_1060_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7___lam__0(
    mut v___y_1062_: u8,
    mut v_suppressElabErrors_1063_: u8,
    mut v_x_1064_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_1064_) == 1 {
        let mut v_pre_1065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_pre_1065_ = crate::leanh::lean_ctor_get(v_x_1064_, 0);
        if crate::leanh::lean_obj_tag(v_pre_1065_) == 0 {
            let mut v_str_1066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1068_: u8 = 0;
            v_str_1066_ = crate::leanh::lean_ctor_get(v_x_1064_, 1);
            v___x_1067_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7___lam__0___closed__0;
            v___x_1068_ = lean_string_dec_eq(v_str_1066_, v___x_1067_);
            if v___x_1068_ == 0 {
                return v___y_1062_;
            } else {
                return v_suppressElabErrors_1063_;
            }
        } else {
            return v___y_1062_;
        }
    } else {
        return v___y_1062_;
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7___lam__0___boxed(
    mut v___y_1069_: *mut crate::leanh::LeanObject,
    mut v_suppressElabErrors_1070_: *mut crate::leanh::LeanObject,
    mut v_x_1071_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_9100__boxed_1072_: u8 = 0;
    let mut v_suppressElabErrors_boxed_1073_: u8 = 0;
    let mut v_res_1074_: u8 = 0;
    let mut v_r_1075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_9100__boxed_1072_ = (crate::leanh::lean_unbox(v___y_1069_) as u8);
    v_suppressElabErrors_boxed_1073_ = (crate::leanh::lean_unbox(v_suppressElabErrors_1070_) as u8);
    v_res_1074_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7___lam__0(v___y_9100__boxed_1072_, v_suppressElabErrors_boxed_1073_, v_x_1071_);
    crate::leanh::lean_dec(v_x_1071_);
    v_r_1075_ = crate::leanh::lean_box((v_res_1074_) as usize);
    return v_r_1075_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1076_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1076_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1077_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__0);
    v___x_1078_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1078_, 0, v___x_1077_);
    return v___x_1078_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1079_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__1);
    v___x_1080_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1081_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1081_, 0, v___x_1080_);
    crate::leanh::lean_ctor_set(v___x_1081_, 1, v___x_1080_);
    crate::leanh::lean_ctor_set(v___x_1081_, 2, v___x_1080_);
    crate::leanh::lean_ctor_set(v___x_1081_, 3, v___x_1080_);
    crate::leanh::lean_ctor_set(v___x_1081_, 4, v___x_1079_);
    crate::leanh::lean_ctor_set(v___x_1081_, 5, v___x_1079_);
    crate::leanh::lean_ctor_set(v___x_1081_, 6, v___x_1079_);
    crate::leanh::lean_ctor_set(v___x_1081_, 7, v___x_1079_);
    crate::leanh::lean_ctor_set(v___x_1081_, 8, v___x_1079_);
    crate::leanh::lean_ctor_set(v___x_1081_, 9, v___x_1079_);
    return v___x_1081_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1082_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1083_ = lean_mk_empty_array_with_capacity(v___x_1082_);
    v___x_1084_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1084_, 0, v___x_1083_);
    return v___x_1084_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1085_: usize = 0;
    let mut v___x_1086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1085_ = 5usize;
    v___x_1086_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1087_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1088_ = lean_mk_empty_array_with_capacity(v___x_1087_);
    v___x_1089_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__3);
    v___x_1090_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_1090_, 0, v___x_1089_);
    crate::leanh::lean_ctor_set(v___x_1090_, 1, v___x_1088_);
    crate::leanh::lean_ctor_set(v___x_1090_, 2, v___x_1086_);
    crate::leanh::lean_ctor_set(v___x_1090_, 3, v___x_1086_);
    crate::leanh::lean_ctor_set_usize(v___x_1090_, 4, v___x_1085_);
    return v___x_1090_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1091_ = crate::leanh::lean_box(1);
    v___x_1092_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__4);
    v___x_1093_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__1);
    v___x_1094_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1094_, 0, v___x_1093_);
    crate::leanh::lean_ctor_set(v___x_1094_, 1, v___x_1092_);
    crate::leanh::lean_ctor_set(v___x_1094_, 2, v___x_1091_);
    return v___x_1094_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg(
    mut v_msgData_1095_: *mut crate::leanh::LeanObject,
    mut v___y_1096_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_1101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1098_ = lean_st_ref_get(v___y_1096_);
    v_env_1099_ = crate::leanh::lean_ctor_get(v___x_1098_, 0);
    crate::leanh::lean_inc_ref(v_env_1099_);
    crate::leanh::lean_dec(v___x_1098_);
    v___x_1100_ = lean_st_ref_get(v___y_1096_);
    v_scopes_1101_ = crate::leanh::lean_ctor_get(v___x_1100_, 2);
    crate::leanh::lean_inc(v_scopes_1101_);
    crate::leanh::lean_dec(v___x_1100_);
    v___x_1102_ = l_Lean_Elab_Command_instInhabitedScope_default;
    v___x_1103_ = l_List_head_x21___redArg(v___x_1102_, v_scopes_1101_);
    crate::leanh::lean_dec(v_scopes_1101_);
    v_opts_1104_ = crate::leanh::lean_ctor_get(v___x_1103_, 1);
    crate::leanh::lean_inc_ref(v_opts_1104_);
    crate::leanh::lean_dec(v___x_1103_);
    v___x_1105_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__2);
    v___x_1106_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__5);
    v___x_1107_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1107_, 0, v_env_1099_);
    crate::leanh::lean_ctor_set(v___x_1107_, 1, v___x_1105_);
    crate::leanh::lean_ctor_set(v___x_1107_, 2, v___x_1106_);
    crate::leanh::lean_ctor_set(v___x_1107_, 3, v_opts_1104_);
    v___x_1108_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1108_, 0, v___x_1107_);
    crate::leanh::lean_ctor_set(v___x_1108_, 1, v_msgData_1095_);
    v___x_1109_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1109_, 0, v___x_1108_);
    return v___x_1109_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___boxed(
    mut v_msgData_1110_: *mut crate::leanh::LeanObject,
    mut v___y_1111_: *mut crate::leanh::LeanObject,
    mut v___y_1112_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1113_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg(v_msgData_1110_, v___y_1111_);
    crate::leanh::lean_dec(v___y_1111_);
    return v_res_1113_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__11(
    mut v_opts_1114_: *mut crate::leanh::LeanObject,
    mut v_opt_1115_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_1117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_1116_ = crate::leanh::lean_ctor_get(v_opt_1115_, 0);
    v_defValue_1117_ = crate::leanh::lean_ctor_get(v_opt_1115_, 1);
    v_map_1118_ = crate::leanh::lean_ctor_get(v_opts_1114_, 0);
    v___x_1119_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_1118_,
            v_name_1116_,
        );
    if crate::leanh::lean_obj_tag(v___x_1119_) == 0 {
        let mut v___x_1120_: u8 = 0;
        v___x_1120_ = (crate::leanh::lean_unbox(v_defValue_1117_) as u8);
        return v___x_1120_;
    } else {
        let mut v_val_1121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1121_ = crate::leanh::lean_ctor_get(v___x_1119_, 0);
        crate::leanh::lean_inc(v_val_1121_);
        crate::leanh::lean_dec_ref_known(v___x_1119_, 1);
        if crate::leanh::lean_obj_tag(v_val_1121_) == 1 {
            let mut v_v_1122_: u8 = 0;
            v_v_1122_ = crate::leanh::lean_ctor_get_uint8(v_val_1121_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_1121_, 0);
            return v_v_1122_;
        } else {
            let mut v___x_1123_: u8 = 0;
            crate::leanh::lean_dec(v_val_1121_);
            v___x_1123_ = (crate::leanh::lean_unbox(v_defValue_1117_) as u8);
            return v___x_1123_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__11___boxed(
    mut v_opts_1124_: *mut crate::leanh::LeanObject,
    mut v_opt_1125_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1126_: u8 = 0;
    let mut v_r_1127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1126_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__11(v_opts_1124_, v_opt_1125_);
    crate::leanh::lean_dec_ref(v_opt_1125_);
    crate::leanh::lean_dec_ref(v_opts_1124_);
    v_r_1127_ = crate::leanh::lean_box((v_res_1126_) as usize);
    return v_r_1127_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7(
    mut v_ref_1129_: *mut crate::leanh::LeanObject,
    mut v_msgData_1130_: *mut crate::leanh::LeanObject,
    mut v_severity_1131_: u8,
    mut v_isSilent_1132_: u8,
    mut v___y_1133_: *mut crate::leanh::LeanObject,
    mut v___y_1134_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1137_: u8 = 0;
    let mut v___y_1138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1140_: u8 = 0;
    let mut v___y_1141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1151_: u8 = 0;
    let mut v___x_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_1157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1168_: u8 = 0;
    let mut v___x_1169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1181_: u8 = 0;
    let mut v_isSharedCheck_1182_: u8 = 0;
    let mut v_a_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1186_: u8 = 0;
    let mut v___x_1188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1190_: u8 = 0;
    let mut v_a_1191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1194_: u8 = 0;
    let mut v___x_1196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1198_: u8 = 0;
    let mut v___y_1200_: u8 = 0;
    let mut v___y_1201_: u8 = 0;
    let mut v___y_1202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1203_: u8 = 0;
    let mut v___y_1204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_1205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1207_: u8 = 0;
    let mut v___x_1208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1213_: u8 = 0;
    let mut v___x_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: u8 = 0;
    let mut v___x_1222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1226_: u8 = 0;
    let mut v___y_1228_: u8 = 0;
    let mut v___y_1229_: u8 = 0;
    let mut v___y_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1231_: u8 = 0;
    let mut v___y_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1236_: u8 = 0;
    let mut v___y_1237_: u8 = 0;
    let mut v___y_1238_: u8 = 0;
    let mut v___x_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1248_: u8 = 0;
    let mut v___x_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1252_: u8 = 0;
    let mut v___x_1253_: u8 = 0;
    let mut v___y_1255_: u8 = 0;
    let mut v___y_1256_: u8 = 0;
    let mut v___y_1257_: u8 = 0;
    let mut v___y_1259_: u8 = 0;
    let mut v___x_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1265_: u8 = 0;
    let mut v___x_1266_: u8 = 0;
    let mut v___x_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: u8 = 0;
    let mut v___x_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: u8 = 0;
    let mut v___x_1272_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1253_ = 2;
                v___x_1271_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1131_, v___x_1253_);
                if v___x_1271_ == 0 {
                    v___y_1259_ = v___x_1271_;
                    state = 18;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_msgData_1130_);
                    v___x_1272_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1130_);
                    v___y_1259_ = v___x_1272_;
                    state = 18;
                    continue;
                }
            }
            1 => {
                v___x_1145_ = l_Lean_Elab_Command_getScope___redArg(v___y_1144_);
                if crate::leanh::lean_obj_tag(v___x_1145_) == 0 {
                    v_a_1146_ = crate::leanh::lean_ctor_get(v___x_1145_, 0);
                    crate::leanh::lean_inc(v_a_1146_);
                    crate::leanh::lean_dec_ref_known(v___x_1145_, 1);
                    v___x_1147_ = l_Lean_Elab_Command_getScope___redArg(v___y_1144_);
                    if crate::leanh::lean_obj_tag(v___x_1147_) == 0 {
                        v_a_1148_ = crate::leanh::lean_ctor_get(v___x_1147_, 0);
                        v_isSharedCheck_1182_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1147_)) as u8;
                        if v_isSharedCheck_1182_ == 0 {
                            v___x_1150_ = v___x_1147_;
                            v_isShared_1151_ = v_isSharedCheck_1182_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1148_);
                            crate::leanh::lean_dec(v___x_1147_);
                            v___x_1150_ = crate::leanh::lean_box(0);
                            v_isShared_1151_ = v_isSharedCheck_1182_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_1146_);
                        crate::leanh::lean_dec_ref(v___y_1143_);
                        crate::leanh::lean_dec_ref(v___y_1142_);
                        crate::leanh::lean_dec(v___y_1139_);
                        v_a_1183_ = crate::leanh::lean_ctor_get(v___x_1147_, 0);
                        v_isSharedCheck_1190_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1147_)) as u8;
                        if v_isSharedCheck_1190_ == 0 {
                            v___x_1185_ = v___x_1147_;
                            v_isShared_1186_ = v_isSharedCheck_1190_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1183_);
                            crate::leanh::lean_dec(v___x_1147_);
                            v___x_1185_ = crate::leanh::lean_box(0);
                            v_isShared_1186_ = v_isSharedCheck_1190_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_1143_);
                    crate::leanh::lean_dec_ref(v___y_1142_);
                    crate::leanh::lean_dec(v___y_1139_);
                    v_a_1191_ = crate::leanh::lean_ctor_get(v___x_1145_, 0);
                    v_isSharedCheck_1198_ = (!crate::leanh::lean_is_exclusive(v___x_1145_)) as u8;
                    if v_isSharedCheck_1198_ == 0 {
                        v___x_1193_ = v___x_1145_;
                        v_isShared_1194_ = v_isSharedCheck_1198_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1191_);
                        crate::leanh::lean_dec(v___x_1145_);
                        v___x_1193_ = crate::leanh::lean_box(0);
                        v_isShared_1194_ = v_isSharedCheck_1198_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1152_ = lean_st_ref_take(v___y_1144_);
                v_currNamespace_1153_ = crate::leanh::lean_ctor_get(v_a_1146_, 2);
                crate::leanh::lean_inc(v_currNamespace_1153_);
                crate::leanh::lean_dec(v_a_1146_);
                v_openDecls_1154_ = crate::leanh::lean_ctor_get(v_a_1148_, 3);
                crate::leanh::lean_inc(v_openDecls_1154_);
                crate::leanh::lean_dec(v_a_1148_);
                v_env_1155_ = crate::leanh::lean_ctor_get(v___x_1152_, 0);
                v_messages_1156_ = crate::leanh::lean_ctor_get(v___x_1152_, 1);
                v_scopes_1157_ = crate::leanh::lean_ctor_get(v___x_1152_, 2);
                v_usedQuotCtxts_1158_ = crate::leanh::lean_ctor_get(v___x_1152_, 3);
                v_nextMacroScope_1159_ = crate::leanh::lean_ctor_get(v___x_1152_, 4);
                v_maxRecDepth_1160_ = crate::leanh::lean_ctor_get(v___x_1152_, 5);
                v_ngen_1161_ = crate::leanh::lean_ctor_get(v___x_1152_, 6);
                v_auxDeclNGen_1162_ = crate::leanh::lean_ctor_get(v___x_1152_, 7);
                v_infoState_1163_ = crate::leanh::lean_ctor_get(v___x_1152_, 8);
                v_traceState_1164_ = crate::leanh::lean_ctor_get(v___x_1152_, 9);
                v_snapshotTasks_1165_ = crate::leanh::lean_ctor_get(v___x_1152_, 10);
                v_isSharedCheck_1181_ = (!crate::leanh::lean_is_exclusive(v___x_1152_)) as u8;
                if v_isSharedCheck_1181_ == 0 {
                    v___x_1167_ = v___x_1152_;
                    v_isShared_1168_ = v_isSharedCheck_1181_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_1165_);
                    crate::leanh::lean_inc(v_traceState_1164_);
                    crate::leanh::lean_inc(v_infoState_1163_);
                    crate::leanh::lean_inc(v_auxDeclNGen_1162_);
                    crate::leanh::lean_inc(v_ngen_1161_);
                    crate::leanh::lean_inc(v_maxRecDepth_1160_);
                    crate::leanh::lean_inc(v_nextMacroScope_1159_);
                    crate::leanh::lean_inc(v_usedQuotCtxts_1158_);
                    crate::leanh::lean_inc(v_scopes_1157_);
                    crate::leanh::lean_inc(v_messages_1156_);
                    crate::leanh::lean_inc(v_env_1155_);
                    crate::leanh::lean_dec(v___x_1152_);
                    v___x_1167_ = crate::leanh::lean_box(0);
                    v_isShared_1168_ = v_isSharedCheck_1181_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1169_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1169_, 0, v_currNamespace_1153_);
                crate::leanh::lean_ctor_set(v___x_1169_, 1, v_openDecls_1154_);
                v___x_1170_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1170_, 0, v___x_1169_);
                crate::leanh::lean_ctor_set(v___x_1170_, 1, v___y_1142_);
                crate::leanh::lean_inc_ref(v___y_1141_);
                crate::leanh::lean_inc_ref(v___y_1138_);
                v___x_1171_ = crate::leanh::lean_alloc_ctor(0, 5, (3) as u32);
                crate::leanh::lean_ctor_set(v___x_1171_, 0, v___y_1138_);
                crate::leanh::lean_ctor_set(v___x_1171_, 1, v___y_1143_);
                crate::leanh::lean_ctor_set(v___x_1171_, 2, v___y_1139_);
                crate::leanh::lean_ctor_set(v___x_1171_, 3, v___y_1141_);
                crate::leanh::lean_ctor_set(v___x_1171_, 4, v___x_1170_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1171_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    v___y_1137_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1171_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
                    v___y_1140_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1171_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 2) as u32,
                    v_isSilent_1132_,
                );
                v___x_1172_ = l_Lean_MessageLog_add(v___x_1171_, v_messages_1156_);
                if v_isShared_1168_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1167_, 1, v___x_1172_);
                    v___x_1174_ = v___x_1167_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1180_ = crate::leanh::lean_alloc_ctor(0, 11, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1180_, 0, v_env_1155_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1180_, 1, v___x_1172_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1180_, 2, v_scopes_1157_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1180_, 3, v_usedQuotCtxts_1158_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1180_, 4, v_nextMacroScope_1159_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1180_, 5, v_maxRecDepth_1160_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1180_, 6, v_ngen_1161_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1180_, 7, v_auxDeclNGen_1162_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1180_, 8, v_infoState_1163_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1180_, 9, v_traceState_1164_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1180_, 10, v_snapshotTasks_1165_);
                    v___x_1174_ = v_reuseFailAlloc_1180_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1175_ = lean_st_ref_set(v___y_1144_, v___x_1174_);
                v___x_1176_ = crate::leanh::lean_box(0);
                if v_isShared_1151_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1150_, 0, v___x_1176_);
                    v___x_1178_ = v___x_1150_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1179_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1179_, 0, v___x_1176_);
                    v___x_1178_ = v_reuseFailAlloc_1179_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1178_;
            }
            6 => {
                if v_isShared_1186_ == 0 {
                    v___x_1188_ = v___x_1185_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1189_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1189_, 0, v_a_1183_);
                    v___x_1188_ = v_reuseFailAlloc_1189_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1188_;
            }
            8 => {
                if v_isShared_1194_ == 0 {
                    v___x_1196_ = v___x_1193_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1197_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1197_, 0, v_a_1191_);
                    v___x_1196_ = v_reuseFailAlloc_1197_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1196_;
            }
            10 => {
                v_fileName_1205_ = crate::leanh::lean_ctor_get(v___y_1133_, 0);
                v_fileMap_1206_ = crate::leanh::lean_ctor_get(v___y_1133_, 1);
                v_suppressElabErrors_1207_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_1133_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                v___x_1208_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_1130_,
                    );
                v___x_1209_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg(v___x_1208_, v___y_1134_);
                v_a_1210_ = crate::leanh::lean_ctor_get(v___x_1209_, 0);
                v_isSharedCheck_1226_ = (!crate::leanh::lean_is_exclusive(v___x_1209_)) as u8;
                if v_isSharedCheck_1226_ == 0 {
                    v___x_1212_ = v___x_1209_;
                    v_isShared_1213_ = v_isSharedCheck_1226_;
                    state = 11;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1210_);
                    crate::leanh::lean_dec(v___x_1209_);
                    v___x_1212_ = crate::leanh::lean_box(0);
                    v_isShared_1213_ = v_isSharedCheck_1226_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                crate::leanh::lean_inc_ref_n(v_fileMap_1206_, 2);
                v___x_1214_ = l_Lean_FileMap_toPosition(v_fileMap_1206_, v___y_1202_);
                crate::leanh::lean_dec(v___y_1202_);
                v___x_1215_ = l_Lean_FileMap_toPosition(v_fileMap_1206_, v___y_1204_);
                crate::leanh::lean_dec(v___y_1204_);
                v___x_1216_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1216_, 0, v___x_1215_);
                v___x_1217_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7___closed__0;
                if v_suppressElabErrors_1207_ == 0 {
                    crate::leanh::lean_del_object(v___x_1212_);
                    v___y_1137_ = v___y_1201_;
                    v___y_1138_ = v_fileName_1205_;
                    v___y_1139_ = v___x_1216_;
                    v___y_1140_ = v___y_1203_;
                    v___y_1141_ = v___x_1217_;
                    v___y_1142_ = v_a_1210_;
                    v___y_1143_ = v___x_1214_;
                    v___y_1144_ = v___y_1134_;
                    state = 1;
                    continue;
                } else {
                    v___x_1218_ = crate::leanh::lean_box((v___y_1200_) as usize);
                    v___x_1219_ = crate::leanh::lean_box((v_suppressElabErrors_1207_) as usize);
                    v___f_1220_ = crate::leanh::lean_alloc_closure(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    crate::leanh::lean_closure_set(v___f_1220_, 0, v___x_1218_);
                    crate::leanh::lean_closure_set(v___f_1220_, 1, v___x_1219_);
                    crate::leanh::lean_inc(v_a_1210_);
                    v___x_1221_ = l_Lean_MessageData_hasTag(v___f_1220_, v_a_1210_);
                    if v___x_1221_ == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_1216_, 1);
                        crate::leanh::lean_dec_ref(v___x_1214_);
                        crate::leanh::lean_dec(v_a_1210_);
                        v___x_1222_ = crate::leanh::lean_box(0);
                        if v_isShared_1213_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1212_, 0, v___x_1222_);
                            v___x_1224_ = v___x_1212_;
                            state = 12;
                            continue;
                        } else {
                            v_reuseFailAlloc_1225_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1225_, 0, v___x_1222_);
                            v___x_1224_ = v_reuseFailAlloc_1225_;
                            state = 12;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_1212_);
                        v___y_1137_ = v___y_1201_;
                        v___y_1138_ = v_fileName_1205_;
                        v___y_1139_ = v___x_1216_;
                        v___y_1140_ = v___y_1203_;
                        v___y_1141_ = v___x_1217_;
                        v___y_1142_ = v_a_1210_;
                        v___y_1143_ = v___x_1214_;
                        v___y_1144_ = v___y_1134_;
                        state = 1;
                        continue;
                    }
                }
            }
            12 => {
                return v___x_1224_;
            }
            13 => {
                v___x_1233_ = l_Lean_Syntax_getTailPos_x3f(v___y_1230_, v___y_1229_);
                crate::leanh::lean_dec(v___y_1230_);
                if crate::leanh::lean_obj_tag(v___x_1233_) == 0 {
                    crate::leanh::lean_inc(v___y_1232_);
                    v___y_1200_ = v___y_1228_;
                    v___y_1201_ = v___y_1229_;
                    v___y_1202_ = v___y_1232_;
                    v___y_1203_ = v___y_1231_;
                    v___y_1204_ = v___y_1232_;
                    state = 10;
                    continue;
                } else {
                    v_val_1234_ = crate::leanh::lean_ctor_get(v___x_1233_, 0);
                    crate::leanh::lean_inc(v_val_1234_);
                    crate::leanh::lean_dec_ref_known(v___x_1233_, 1);
                    v___y_1200_ = v___y_1228_;
                    v___y_1201_ = v___y_1229_;
                    v___y_1202_ = v___y_1232_;
                    v___y_1203_ = v___y_1231_;
                    v___y_1204_ = v_val_1234_;
                    state = 10;
                    continue;
                }
            }
            14 => {
                v___x_1239_ = l_Lean_Elab_Command_getRef___redArg(v___y_1133_);
                if crate::leanh::lean_obj_tag(v___x_1239_) == 0 {
                    v_a_1240_ = crate::leanh::lean_ctor_get(v___x_1239_, 0);
                    crate::leanh::lean_inc(v_a_1240_);
                    crate::leanh::lean_dec_ref_known(v___x_1239_, 1);
                    v_ref_1241_ = l_Lean_replaceRef(v_ref_1129_, v_a_1240_);
                    crate::leanh::lean_dec(v_a_1240_);
                    v___x_1242_ = l_Lean_Syntax_getPos_x3f(v_ref_1241_, v___y_1237_);
                    if crate::leanh::lean_obj_tag(v___x_1242_) == 0 {
                        v___x_1243_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___y_1228_ = v___y_1236_;
                        v___y_1229_ = v___y_1237_;
                        v___y_1230_ = v_ref_1241_;
                        v___y_1231_ = v___y_1238_;
                        v___y_1232_ = v___x_1243_;
                        state = 13;
                        continue;
                    } else {
                        v_val_1244_ = crate::leanh::lean_ctor_get(v___x_1242_, 0);
                        crate::leanh::lean_inc(v_val_1244_);
                        crate::leanh::lean_dec_ref_known(v___x_1242_, 1);
                        v___y_1228_ = v___y_1236_;
                        v___y_1229_ = v___y_1237_;
                        v___y_1230_ = v_ref_1241_;
                        v___y_1231_ = v___y_1238_;
                        v___y_1232_ = v_val_1244_;
                        state = 13;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_msgData_1130_);
                    v_a_1245_ = crate::leanh::lean_ctor_get(v___x_1239_, 0);
                    v_isSharedCheck_1252_ = (!crate::leanh::lean_is_exclusive(v___x_1239_)) as u8;
                    if v_isSharedCheck_1252_ == 0 {
                        v___x_1247_ = v___x_1239_;
                        v_isShared_1248_ = v_isSharedCheck_1252_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1245_);
                        crate::leanh::lean_dec(v___x_1239_);
                        v___x_1247_ = crate::leanh::lean_box(0);
                        v_isShared_1248_ = v_isSharedCheck_1252_;
                        state = 15;
                        continue;
                    }
                }
            }
            15 => {
                if v_isShared_1248_ == 0 {
                    v___x_1250_ = v___x_1247_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1251_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_a_1245_);
                    v___x_1250_ = v_reuseFailAlloc_1251_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_1250_;
            }
            17 => {
                if v___y_1257_ == 0 {
                    v___y_1236_ = v___y_1255_;
                    v___y_1237_ = v___y_1256_;
                    v___y_1238_ = v_severity_1131_;
                    state = 14;
                    continue;
                } else {
                    v___y_1236_ = v___y_1255_;
                    v___y_1237_ = v___y_1256_;
                    v___y_1238_ = v___x_1253_;
                    state = 14;
                    continue;
                }
            }
            18 => {
                if v___y_1259_ == 0 {
                    v___x_1260_ = lean_st_ref_get(v___y_1134_);
                    v_scopes_1261_ = crate::leanh::lean_ctor_get(v___x_1260_, 2);
                    crate::leanh::lean_inc(v_scopes_1261_);
                    crate::leanh::lean_dec(v___x_1260_);
                    v___x_1262_ = l_Lean_Elab_Command_instInhabitedScope_default;
                    v___x_1263_ = l_List_head_x21___redArg(v___x_1262_, v_scopes_1261_);
                    crate::leanh::lean_dec(v_scopes_1261_);
                    v_opts_1264_ = crate::leanh::lean_ctor_get(v___x_1263_, 1);
                    crate::leanh::lean_inc_ref(v_opts_1264_);
                    crate::leanh::lean_dec(v___x_1263_);
                    v___x_1265_ = 1;
                    v___x_1266_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1131_, v___x_1265_);
                    if v___x_1266_ == 0 {
                        crate::leanh::lean_dec_ref(v_opts_1264_);
                        v___y_1255_ = v___y_1259_;
                        v___y_1256_ = v___y_1259_;
                        v___y_1257_ = v___x_1266_;
                        state = 17;
                        continue;
                    } else {
                        v___x_1267_ = l_Lean_warningAsError;
                        v___x_1268_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__11(v_opts_1264_, v___x_1267_);
                        crate::leanh::lean_dec_ref(v_opts_1264_);
                        v___y_1255_ = v___y_1259_;
                        v___y_1256_ = v___y_1259_;
                        v___y_1257_ = v___x_1268_;
                        state = 17;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_msgData_1130_);
                    v___x_1269_ = crate::leanh::lean_box(0);
                    v___x_1270_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1270_, 0, v___x_1269_);
                    return v___x_1270_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7___boxed(
    mut v_ref_1273_: *mut crate::leanh::LeanObject,
    mut v_msgData_1274_: *mut crate::leanh::LeanObject,
    mut v_severity_1275_: *mut crate::leanh::LeanObject,
    mut v_isSilent_1276_: *mut crate::leanh::LeanObject,
    mut v___y_1277_: *mut crate::leanh::LeanObject,
    mut v___y_1278_: *mut crate::leanh::LeanObject,
    mut v___y_1279_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_1280_: u8 = 0;
    let mut v_isSilent_boxed_1281_: u8 = 0;
    let mut v_res_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_1280_ = (crate::leanh::lean_unbox(v_severity_1275_) as u8);
    v_isSilent_boxed_1281_ = (crate::leanh::lean_unbox(v_isSilent_1276_) as u8);
    v_res_1282_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7(v_ref_1273_, v_msgData_1274_, v_severity_boxed_1280_, v_isSilent_boxed_1281_, v___y_1277_, v___y_1278_);
    crate::leanh::lean_dec(v___y_1278_);
    crate::leanh::lean_dec_ref(v___y_1277_);
    crate::leanh::lean_dec(v_ref_1273_);
    return v_res_1282_;
}
pub unsafe fn l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4(
    mut v_ref_1283_: *mut crate::leanh::LeanObject,
    mut v_msgData_1284_: *mut crate::leanh::LeanObject,
    mut v___y_1285_: *mut crate::leanh::LeanObject,
    mut v___y_1286_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1288_: u8 = 0;
    let mut v___x_1289_: u8 = 0;
    let mut v___x_1290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1288_ = 1;
    v___x_1289_ = 0;
    v___x_1290_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7(v_ref_1283_, v_msgData_1284_, v___x_1288_, v___x_1289_, v___y_1285_, v___y_1286_);
    return v___x_1290_;
}
pub unsafe fn l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4___boxed(
    mut v_ref_1291_: *mut crate::leanh::LeanObject,
    mut v_msgData_1292_: *mut crate::leanh::LeanObject,
    mut v___y_1293_: *mut crate::leanh::LeanObject,
    mut v___y_1294_: *mut crate::leanh::LeanObject,
    mut v___y_1295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1296_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4(v_ref_1291_, v_msgData_1292_, v___y_1293_, v___y_1294_);
    crate::leanh::lean_dec(v___y_1294_);
    crate::leanh::lean_dec_ref(v___y_1293_);
    crate::leanh::lean_dec(v_ref_1291_);
    return v_res_1296_;
}
pub unsafe fn _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1298_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3___closed__0;
    v___x_1299_ = l_Lean_stringToMessageData(v___x_1298_);
    return v___x_1299_;
}
pub unsafe fn _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1301_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3___closed__2;
    v___x_1302_ = l_Lean_stringToMessageData(v___x_1301_);
    return v___x_1302_;
}
pub unsafe fn l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3(
    mut v_linterOption_1303_: *mut crate::leanh::LeanObject,
    mut v_stx_1304_: *mut crate::leanh::LeanObject,
    mut v_msg_1305_: *mut crate::leanh::LeanObject,
    mut v___y_1306_: *mut crate::leanh::LeanObject,
    mut v___y_1307_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1312_: u8 = 0;
    let mut v___x_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_disable_1319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1326_: u8 = 0;
    let mut v_unused_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_1309_ = crate::leanh::lean_ctor_get(v_linterOption_1303_, 0);
                v_isSharedCheck_1326_ =
                    (!crate::leanh::lean_is_exclusive(v_linterOption_1303_)) as u8;
                if v_isSharedCheck_1326_ == 0 {
                    v_unused_1327_ = crate::leanh::lean_ctor_get(v_linterOption_1303_, 1);
                    crate::leanh::lean_dec(v_unused_1327_);
                    v___x_1311_ = v_linterOption_1303_;
                    v_isShared_1312_ = v_isSharedCheck_1326_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_name_1309_);
                    crate::leanh::lean_dec(v_linterOption_1303_);
                    v___x_1311_ = crate::leanh::lean_box(0);
                    v_isShared_1312_ = v_isSharedCheck_1326_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1313_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3___closed__1), core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3___closed__1_once), _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3___closed__1);
                crate::leanh::lean_inc(v_name_1309_);
                v___x_1314_ = l_Lean_MessageData_ofName(v_name_1309_);
                if v_isShared_1312_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1311_, 7);
                    crate::leanh::lean_ctor_set(v___x_1311_, 1, v___x_1314_);
                    crate::leanh::lean_ctor_set(v___x_1311_, 0, v___x_1313_);
                    v___x_1316_ = v___x_1311_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1325_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1325_, 0, v___x_1313_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1325_, 1, v___x_1314_);
                    v___x_1316_ = v_reuseFailAlloc_1325_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1317_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3___closed__3), core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3___closed__3_once), _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3___closed__3);
                v___x_1318_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1318_, 0, v___x_1316_);
                crate::leanh::lean_ctor_set(v___x_1318_, 1, v___x_1317_);
                v_disable_1319_ = l_Lean_MessageData_note(v___x_1318_);
                v___x_1320_ = l_Lean_Linter_linterMessageTag;
                v___x_1321_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1321_, 0, v_msg_1305_);
                crate::leanh::lean_ctor_set(v___x_1321_, 1, v_disable_1319_);
                v___x_1322_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1322_, 0, v___x_1320_);
                crate::leanh::lean_ctor_set(v___x_1322_, 1, v___x_1321_);
                v___x_1323_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1323_, 0, v_name_1309_);
                crate::leanh::lean_ctor_set(v___x_1323_, 1, v___x_1322_);
                v___x_1324_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4(v_stx_1304_, v___x_1323_, v___y_1306_, v___y_1307_);
                return v___x_1324_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3___boxed(
    mut v_linterOption_1328_: *mut crate::leanh::LeanObject,
    mut v_stx_1329_: *mut crate::leanh::LeanObject,
    mut v_msg_1330_: *mut crate::leanh::LeanObject,
    mut v___y_1331_: *mut crate::leanh::LeanObject,
    mut v___y_1332_: *mut crate::leanh::LeanObject,
    mut v___y_1333_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1334_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3(v_linterOption_1328_, v_stx_1329_, v_msg_1330_, v___y_1331_, v___y_1332_);
    crate::leanh::lean_dec(v___y_1332_);
    crate::leanh::lean_dec_ref(v___y_1331_);
    crate::leanh::lean_dec(v_stx_1329_);
    return v_res_1334_;
}
pub unsafe fn l_Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2(
    mut v_linterOption_1335_: *mut crate::leanh::LeanObject,
    mut v_stx_1336_: *mut crate::leanh::LeanObject,
    mut v_msg_1337_: *mut crate::leanh::LeanObject,
    mut v___y_1338_: *mut crate::leanh::LeanObject,
    mut v___y_1339_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1345_: u8 = 0;
    let mut v___x_1346_: u8 = 0;
    let mut v___x_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1352_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1341_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_DefProp_defPropLinter_spec__0(v___y_1338_, v___y_1339_);
                v_a_1342_ = crate::leanh::lean_ctor_get(v___x_1341_, 0);
                v_isSharedCheck_1352_ = (!crate::leanh::lean_is_exclusive(v___x_1341_)) as u8;
                if v_isSharedCheck_1352_ == 0 {
                    v___x_1344_ = v___x_1341_;
                    v_isShared_1345_ = v_isSharedCheck_1352_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1342_);
                    crate::leanh::lean_dec(v___x_1341_);
                    v___x_1344_ = crate::leanh::lean_box(0);
                    v_isShared_1345_ = v_isSharedCheck_1352_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1346_ = l_Lean_Linter_getLinterValue(v_linterOption_1335_, v_a_1342_);
                crate::leanh::lean_dec(v_a_1342_);
                if v___x_1346_ == 0 {
                    crate::leanh::lean_dec_ref(v_msg_1337_);
                    crate::leanh::lean_dec_ref(v_linterOption_1335_);
                    v___x_1347_ = crate::leanh::lean_box(0);
                    if v_isShared_1345_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1344_, 0, v___x_1347_);
                        v___x_1349_ = v___x_1344_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1350_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1350_, 0, v___x_1347_);
                        v___x_1349_ = v_reuseFailAlloc_1350_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1344_);
                    v___x_1351_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3(v_linterOption_1335_, v_stx_1336_, v_msg_1337_, v___y_1338_, v___y_1339_);
                    return v___x_1351_;
                }
            }
            2 => {
                return v___x_1349_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2___boxed(
    mut v_linterOption_1353_: *mut crate::leanh::LeanObject,
    mut v_stx_1354_: *mut crate::leanh::LeanObject,
    mut v_msg_1355_: *mut crate::leanh::LeanObject,
    mut v___y_1356_: *mut crate::leanh::LeanObject,
    mut v___y_1357_: *mut crate::leanh::LeanObject,
    mut v___y_1358_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1359_ = l_Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2(
        v_linterOption_1353_,
        v_stx_1354_,
        v_msg_1355_,
        v___y_1356_,
        v___y_1357_,
    );
    crate::leanh::lean_dec(v___y_1357_);
    crate::leanh::lean_dec_ref(v___y_1356_);
    crate::leanh::lean_dec(v_stx_1354_);
    return v_res_1359_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___lam__0(
    mut v___x_1360_: *mut crate::leanh::LeanObject,
    mut v___y_1361_: *mut crate::leanh::LeanObject,
    mut v___y_1362_: *mut crate::leanh::LeanObject,
    mut v___y_1363_: *mut crate::leanh::LeanObject,
    mut v___y_1364_: *mut crate::leanh::LeanObject,
    mut v___y_1365_: *mut crate::leanh::LeanObject,
    mut v___y_1366_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1368_ = l_Lean_Meta_isProp(
        v___x_1360_,
        v___y_1363_,
        v___y_1364_,
        v___y_1365_,
        v___y_1366_,
    );
    return v___x_1368_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___lam__0___boxed(
    mut v___x_1369_: *mut crate::leanh::LeanObject,
    mut v___y_1370_: *mut crate::leanh::LeanObject,
    mut v___y_1371_: *mut crate::leanh::LeanObject,
    mut v___y_1372_: *mut crate::leanh::LeanObject,
    mut v___y_1373_: *mut crate::leanh::LeanObject,
    mut v___y_1374_: *mut crate::leanh::LeanObject,
    mut v___y_1375_: *mut crate::leanh::LeanObject,
    mut v___y_1376_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1377_ =
        l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___lam__0(
            v___x_1369_,
            v___y_1370_,
            v___y_1371_,
            v___y_1372_,
            v___y_1373_,
            v___y_1374_,
            v___y_1375_,
        );
    crate::leanh::lean_dec(v___y_1375_);
    crate::leanh::lean_dec_ref(v___y_1374_);
    crate::leanh::lean_dec(v___y_1373_);
    crate::leanh::lean_dec_ref(v___y_1372_);
    crate::leanh::lean_dec(v___y_1371_);
    crate::leanh::lean_dec_ref(v___y_1370_);
    return v_res_1377_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1379_ = l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___closed__0;
    v___x_1380_ = l_Lean_stringToMessageData(v___x_1379_);
    return v___x_1380_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1382_ = l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___closed__2;
    v___x_1383_ = l_Lean_stringToMessageData(v___x_1382_);
    return v___x_1383_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg(
    mut v___x_1384_: *mut crate::leanh::LeanObject,
    mut v___x_1385_: u8,
    mut v_as_x27_1386_: *mut crate::leanh::LeanObject,
    mut v_b_1387_: *mut crate::leanh::LeanObject,
    mut v___y_1388_: *mut crate::leanh::LeanObject,
    mut v___y_1389_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: u8 = 0;
    let mut v___x_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: u8 = 0;
    let mut v___x_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1418_: u8 = 0;
    let mut v___x_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1422_: u8 = 0;
    let mut v_a_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1426_: u8 = 0;
    let mut v___x_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1430_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_1386_) == 0 {
                    crate::leanh::lean_dec_ref(v___x_1384_);
                    v___x_1391_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1391_, 0, v_b_1387_);
                    return v___x_1391_;
                } else {
                    v_head_1392_ = crate::leanh::lean_ctor_get(v_as_x27_1386_, 0);
                    v_tail_1393_ = crate::leanh::lean_ctor_get(v_as_x27_1386_, 1);
                    v___x_1394_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc(v_head_1392_);
                    crate::leanh::lean_inc_ref(v___x_1384_);
                    v___x_1395_ =
                        l_Lean_Environment_find_x3f(v___x_1384_, v_head_1392_, v___x_1385_);
                    if crate::leanh::lean_obj_tag(v___x_1395_) == 1 {
                        v_val_1396_ = crate::leanh::lean_ctor_get(v___x_1395_, 0);
                        crate::leanh::lean_inc(v_val_1396_);
                        crate::leanh::lean_dec_ref_known(v___x_1395_, 1);
                        v___x_1397_ = l_Lean_ConstantInfo_isDefinition(v_val_1396_);
                        if v___x_1397_ == 0 {
                            crate::leanh::lean_dec(v_val_1396_);
                            v_as_x27_1386_ = v_tail_1393_;
                            v_b_1387_ = v___x_1394_;
                            state = 0;
                            continue;
                        } else {
                            v___x_1399_ = l_Lean_ConstantInfo_type(v_val_1396_);
                            crate::leanh::lean_dec(v_val_1396_);
                            v___f_1400_ = crate::leanh::lean_alloc_closure(l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                            crate::leanh::lean_closure_set(v___f_1400_, 0, v___x_1399_);
                            v___x_1401_ = l_Lean_Elab_Command_liftTermElabM___redArg(
                                v___f_1400_,
                                v___y_1388_,
                                v___y_1389_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_1401_) == 0 {
                                v_a_1402_ = crate::leanh::lean_ctor_get(v___x_1401_, 0);
                                crate::leanh::lean_inc(v_a_1402_);
                                crate::leanh::lean_dec_ref_known(v___x_1401_, 1);
                                v___x_1403_ = (crate::leanh::lean_unbox(v_a_1402_) as u8);
                                crate::leanh::lean_dec(v_a_1402_);
                                if v___x_1403_ == 0 {
                                    v_as_x27_1386_ = v_tail_1393_;
                                    v_b_1387_ = v___x_1394_;
                                    state = 0;
                                    continue;
                                } else {
                                    v___x_1405_ = l_Lean_Elab_Command_getRef___redArg(v___y_1388_);
                                    if crate::leanh::lean_obj_tag(v___x_1405_) == 0 {
                                        v_a_1406_ = crate::leanh::lean_ctor_get(v___x_1405_, 0);
                                        crate::leanh::lean_inc(v_a_1406_);
                                        crate::leanh::lean_dec_ref_known(v___x_1405_, 1);
                                        v___x_1407_ = l_Lean_Linter_linter_defProp;
                                        v___x_1408_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___closed__1_once), _init_l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___closed__1);
                                        crate::leanh::lean_inc(v_head_1392_);
                                        v___x_1409_ = l_Lean_MessageData_ofConstName(
                                            v_head_1392_,
                                            v___x_1385_,
                                        );
                                        v___x_1410_ =
                                            crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_1410_, 0, v___x_1408_);
                                        crate::leanh::lean_ctor_set(v___x_1410_, 1, v___x_1409_);
                                        v___x_1411_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___closed__3), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___closed__3_once), _init_l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___closed__3);
                                        v___x_1412_ =
                                            crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_1412_, 0, v___x_1410_);
                                        crate::leanh::lean_ctor_set(v___x_1412_, 1, v___x_1411_);
                                        v___x_1413_ = l_Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2(v___x_1407_, v_a_1406_, v___x_1412_, v___y_1388_, v___y_1389_);
                                        crate::leanh::lean_dec(v_a_1406_);
                                        if crate::leanh::lean_obj_tag(v___x_1413_) == 0 {
                                            crate::leanh::lean_dec_ref_known(v___x_1413_, 1);
                                            v_as_x27_1386_ = v_tail_1393_;
                                            v_b_1387_ = v___x_1394_;
                                            state = 0;
                                            continue;
                                        } else {
                                            crate::leanh::lean_dec_ref(v___x_1384_);
                                            return v___x_1413_;
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref(v___x_1384_);
                                        v_a_1415_ = crate::leanh::lean_ctor_get(v___x_1405_, 0);
                                        v_isSharedCheck_1422_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_1405_)) as u8;
                                        if v_isSharedCheck_1422_ == 0 {
                                            v___x_1417_ = v___x_1405_;
                                            v_isShared_1418_ = v_isSharedCheck_1422_;
                                            state = 1;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_1415_);
                                            crate::leanh::lean_dec(v___x_1405_);
                                            v___x_1417_ = crate::leanh::lean_box(0);
                                            v_isShared_1418_ = v_isSharedCheck_1422_;
                                            state = 1;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v___x_1384_);
                                v_a_1423_ = crate::leanh::lean_ctor_get(v___x_1401_, 0);
                                v_isSharedCheck_1430_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1401_)) as u8;
                                if v_isSharedCheck_1430_ == 0 {
                                    v___x_1425_ = v___x_1401_;
                                    v_isShared_1426_ = v_isSharedCheck_1430_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1423_);
                                    crate::leanh::lean_dec(v___x_1401_);
                                    v___x_1425_ = crate::leanh::lean_box(0);
                                    v_isShared_1426_ = v_isSharedCheck_1430_;
                                    state = 3;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_1395_);
                        v_as_x27_1386_ = v_tail_1393_;
                        v_b_1387_ = v___x_1394_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1418_ == 0 {
                    v___x_1420_ = v___x_1417_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1421_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1421_, 0, v_a_1415_);
                    v___x_1420_ = v_reuseFailAlloc_1421_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1420_;
            }
            3 => {
                if v_isShared_1426_ == 0 {
                    v___x_1428_ = v___x_1425_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1429_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1429_, 0, v_a_1423_);
                    v___x_1428_ = v_reuseFailAlloc_1429_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1428_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___boxed(
    mut v___x_1432_: *mut crate::leanh::LeanObject,
    mut v___x_1433_: *mut crate::leanh::LeanObject,
    mut v_as_x27_1434_: *mut crate::leanh::LeanObject,
    mut v_b_1435_: *mut crate::leanh::LeanObject,
    mut v___y_1436_: *mut crate::leanh::LeanObject,
    mut v___y_1437_: *mut crate::leanh::LeanObject,
    mut v___y_1438_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_9626__boxed_1439_: u8 = 0;
    let mut v_res_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_9626__boxed_1439_ = (crate::leanh::lean_unbox(v___x_1433_) as u8);
    v_res_1440_ = l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg(
        v___x_1432_,
        v___x_9626__boxed_1439_,
        v_as_x27_1434_,
        v_b_1435_,
        v___y_1436_,
        v___y_1437_,
    );
    crate::leanh::lean_dec(v___y_1437_);
    crate::leanh::lean_dec_ref(v___y_1436_);
    crate::leanh::lean_dec(v_as_x27_1434_);
    return v_res_1440_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__9_spec__11(
    mut v___x_1444_: *mut crate::leanh::LeanObject,
    mut v___x_1445_: u8,
    mut v_as_1446_: *mut crate::leanh::LeanObject,
    mut v_sz_1447_: usize,
    mut v_i_1448_: usize,
    mut v_b_1449_: *mut crate::leanh::LeanObject,
    mut v___y_1450_: *mut crate::leanh::LeanObject,
    mut v___y_1451_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1453_: u8 = 0;
    let mut v___x_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: usize = 0;
    let mut v___x_1461_: usize = 0;
    let mut v_a_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1466_: u8 = 0;
    let mut v___x_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1470_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1453_ = lean_usize_dec_lt(v_i_1448_, v_sz_1447_);
                if v___x_1453_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_1444_);
                    v___x_1454_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1454_, 0, v_b_1449_);
                    return v___x_1454_;
                } else {
                    crate::leanh::lean_dec_ref(v_b_1449_);
                    v___x_1455_ = crate::leanh::lean_box(0);
                    v_a_1456_ = lean_array_uget_borrowed(v_as_1446_, v_i_1448_);
                    crate::leanh::lean_inc(v_a_1456_);
                    v___x_1457_ = l_Lean_Linter_getDeclsByBody(v_a_1456_);
                    crate::leanh::lean_inc_ref(v___x_1444_);
                    v___x_1458_ = l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg(v___x_1444_, v___x_1445_, v___x_1457_, v___x_1455_, v___y_1450_, v___y_1451_);
                    crate::leanh::lean_dec(v___x_1457_);
                    if crate::leanh::lean_obj_tag(v___x_1458_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_1458_, 1);
                        v___x_1459_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__9_spec__11___closed__0;
                        v___x_1460_ = 1usize;
                        v___x_1461_ = lean_usize_add(v_i_1448_, v___x_1460_);
                        v_i_1448_ = v___x_1461_;
                        v_b_1449_ = v___x_1459_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v___x_1444_);
                        v_a_1463_ = crate::leanh::lean_ctor_get(v___x_1458_, 0);
                        v_isSharedCheck_1470_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1458_)) as u8;
                        if v_isSharedCheck_1470_ == 0 {
                            v___x_1465_ = v___x_1458_;
                            v_isShared_1466_ = v_isSharedCheck_1470_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1463_);
                            crate::leanh::lean_dec(v___x_1458_);
                            v___x_1465_ = crate::leanh::lean_box(0);
                            v_isShared_1466_ = v_isSharedCheck_1470_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1466_ == 0 {
                    v___x_1468_ = v___x_1465_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1469_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1469_, 0, v_a_1463_);
                    v___x_1468_ = v_reuseFailAlloc_1469_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1468_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__9_spec__11___boxed(
    mut v___x_1471_: *mut crate::leanh::LeanObject,
    mut v___x_1472_: *mut crate::leanh::LeanObject,
    mut v_as_1473_: *mut crate::leanh::LeanObject,
    mut v_sz_1474_: *mut crate::leanh::LeanObject,
    mut v_i_1475_: *mut crate::leanh::LeanObject,
    mut v_b_1476_: *mut crate::leanh::LeanObject,
    mut v___y_1477_: *mut crate::leanh::LeanObject,
    mut v___y_1478_: *mut crate::leanh::LeanObject,
    mut v___y_1479_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_9737__boxed_1480_: u8 = 0;
    let mut v_sz_boxed_1481_: usize = 0;
    let mut v_i_boxed_1482_: usize = 0;
    let mut v_res_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_9737__boxed_1480_ = (crate::leanh::lean_unbox(v___x_1472_) as u8);
    v_sz_boxed_1481_ = crate::leanh::lean_unbox_usize(v_sz_1474_);
    crate::leanh::lean_dec(v_sz_1474_);
    v_i_boxed_1482_ = crate::leanh::lean_unbox_usize(v_i_1475_);
    crate::leanh::lean_dec(v_i_1475_);
    v_res_1483_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__9_spec__11(v___x_1471_, v___x_9737__boxed_1480_, v_as_1473_, v_sz_boxed_1481_, v_i_boxed_1482_, v_b_1476_, v___y_1477_, v___y_1478_);
    crate::leanh::lean_dec(v___y_1478_);
    crate::leanh::lean_dec_ref(v___y_1477_);
    crate::leanh::lean_dec_ref(v_as_1473_);
    return v_res_1483_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__9(
    mut v___x_1484_: *mut crate::leanh::LeanObject,
    mut v___x_1485_: u8,
    mut v_as_1486_: *mut crate::leanh::LeanObject,
    mut v_sz_1487_: usize,
    mut v_i_1488_: usize,
    mut v_b_1489_: *mut crate::leanh::LeanObject,
    mut v___y_1490_: *mut crate::leanh::LeanObject,
    mut v___y_1491_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1493_: u8 = 0;
    let mut v___x_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: usize = 0;
    let mut v___x_1501_: usize = 0;
    let mut v___x_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1506_: u8 = 0;
    let mut v___x_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1510_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1493_ = lean_usize_dec_lt(v_i_1488_, v_sz_1487_);
                if v___x_1493_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_1484_);
                    v___x_1494_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1494_, 0, v_b_1489_);
                    return v___x_1494_;
                } else {
                    crate::leanh::lean_dec_ref(v_b_1489_);
                    v___x_1495_ = crate::leanh::lean_box(0);
                    v_a_1496_ = lean_array_uget_borrowed(v_as_1486_, v_i_1488_);
                    crate::leanh::lean_inc(v_a_1496_);
                    v___x_1497_ = l_Lean_Linter_getDeclsByBody(v_a_1496_);
                    crate::leanh::lean_inc_ref(v___x_1484_);
                    v___x_1498_ = l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg(v___x_1484_, v___x_1485_, v___x_1497_, v___x_1495_, v___y_1490_, v___y_1491_);
                    crate::leanh::lean_dec(v___x_1497_);
                    if crate::leanh::lean_obj_tag(v___x_1498_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_1498_, 1);
                        v___x_1499_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__9_spec__11___closed__0;
                        v___x_1500_ = 1usize;
                        v___x_1501_ = lean_usize_add(v_i_1488_, v___x_1500_);
                        v___x_1502_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__9_spec__11(v___x_1484_, v___x_1485_, v_as_1486_, v_sz_1487_, v___x_1501_, v___x_1499_, v___y_1490_, v___y_1491_);
                        return v___x_1502_;
                    } else {
                        crate::leanh::lean_dec_ref(v___x_1484_);
                        v_a_1503_ = crate::leanh::lean_ctor_get(v___x_1498_, 0);
                        v_isSharedCheck_1510_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1498_)) as u8;
                        if v_isSharedCheck_1510_ == 0 {
                            v___x_1505_ = v___x_1498_;
                            v_isShared_1506_ = v_isSharedCheck_1510_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1503_);
                            crate::leanh::lean_dec(v___x_1498_);
                            v___x_1505_ = crate::leanh::lean_box(0);
                            v_isShared_1506_ = v_isSharedCheck_1510_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1506_ == 0 {
                    v___x_1508_ = v___x_1505_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1509_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1509_, 0, v_a_1503_);
                    v___x_1508_ = v_reuseFailAlloc_1509_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1508_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__9___boxed(
    mut v___x_1511_: *mut crate::leanh::LeanObject,
    mut v___x_1512_: *mut crate::leanh::LeanObject,
    mut v_as_1513_: *mut crate::leanh::LeanObject,
    mut v_sz_1514_: *mut crate::leanh::LeanObject,
    mut v_i_1515_: *mut crate::leanh::LeanObject,
    mut v_b_1516_: *mut crate::leanh::LeanObject,
    mut v___y_1517_: *mut crate::leanh::LeanObject,
    mut v___y_1518_: *mut crate::leanh::LeanObject,
    mut v___y_1519_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_9793__boxed_1520_: u8 = 0;
    let mut v_sz_boxed_1521_: usize = 0;
    let mut v_i_boxed_1522_: usize = 0;
    let mut v_res_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_9793__boxed_1520_ = (crate::leanh::lean_unbox(v___x_1512_) as u8);
    v_sz_boxed_1521_ = crate::leanh::lean_unbox_usize(v_sz_1514_);
    crate::leanh::lean_dec(v_sz_1514_);
    v_i_boxed_1522_ = crate::leanh::lean_unbox_usize(v_i_1515_);
    crate::leanh::lean_dec(v_i_1515_);
    v_res_1523_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__9(v___x_1511_, v___x_9793__boxed_1520_, v_as_1513_, v_sz_boxed_1521_, v_i_boxed_1522_, v_b_1516_, v___y_1517_, v___y_1518_);
    crate::leanh::lean_dec(v___y_1518_);
    crate::leanh::lean_dec_ref(v___y_1517_);
    crate::leanh::lean_dec_ref(v_as_1513_);
    return v_res_1523_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6(
    mut v_init_1524_: *mut crate::leanh::LeanObject,
    mut v___x_1525_: *mut crate::leanh::LeanObject,
    mut v___x_1526_: u8,
    mut v_n_1527_: *mut crate::leanh::LeanObject,
    mut v_b_1528_: *mut crate::leanh::LeanObject,
    mut v___y_1529_: *mut crate::leanh::LeanObject,
    mut v___y_1530_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cs_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1535_: usize = 0;
    let mut v___x_1536_: usize = 0;
    let mut v___x_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1541_: u8 = 0;
    let mut v_fst_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1552_: u8 = 0;
    let mut v_a_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1556_: u8 = 0;
    let mut v___x_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1560_: u8 = 0;
    let mut v_vs_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1564_: usize = 0;
    let mut v___x_1565_: usize = 0;
    let mut v___x_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1570_: u8 = 0;
    let mut v_fst_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1581_: u8 = 0;
    let mut v_a_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1585_: u8 = 0;
    let mut v___x_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1589_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_n_1527_) == 0 {
                    v_cs_1532_ = crate::leanh::lean_ctor_get(v_n_1527_, 0);
                    v___x_1533_ = crate::leanh::lean_box(0);
                    v___x_1534_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1534_, 0, v___x_1533_);
                    crate::leanh::lean_ctor_set(v___x_1534_, 1, v_b_1528_);
                    v_sz_1535_ = lean_array_size(v_cs_1532_);
                    v___x_1536_ = 0usize;
                    v___x_1537_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__8(v_init_1524_, v___x_1525_, v___x_1526_, v_cs_1532_, v_sz_1535_, v___x_1536_, v___x_1534_, v___y_1529_, v___y_1530_);
                    if crate::leanh::lean_obj_tag(v___x_1537_) == 0 {
                        v_a_1538_ = crate::leanh::lean_ctor_get(v___x_1537_, 0);
                        v_isSharedCheck_1552_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1537_)) as u8;
                        if v_isSharedCheck_1552_ == 0 {
                            v___x_1540_ = v___x_1537_;
                            v_isShared_1541_ = v_isSharedCheck_1552_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1538_);
                            crate::leanh::lean_dec(v___x_1537_);
                            v___x_1540_ = crate::leanh::lean_box(0);
                            v_isShared_1541_ = v_isSharedCheck_1552_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1553_ = crate::leanh::lean_ctor_get(v___x_1537_, 0);
                        v_isSharedCheck_1560_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1537_)) as u8;
                        if v_isSharedCheck_1560_ == 0 {
                            v___x_1555_ = v___x_1537_;
                            v_isShared_1556_ = v_isSharedCheck_1560_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1553_);
                            crate::leanh::lean_dec(v___x_1537_);
                            v___x_1555_ = crate::leanh::lean_box(0);
                            v_isShared_1556_ = v_isSharedCheck_1560_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_1561_ = crate::leanh::lean_ctor_get(v_n_1527_, 0);
                    v___x_1562_ = crate::leanh::lean_box(0);
                    v___x_1563_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1563_, 0, v___x_1562_);
                    crate::leanh::lean_ctor_set(v___x_1563_, 1, v_b_1528_);
                    v_sz_1564_ = lean_array_size(v_vs_1561_);
                    v___x_1565_ = 0usize;
                    v___x_1566_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__9(v___x_1525_, v___x_1526_, v_vs_1561_, v_sz_1564_, v___x_1565_, v___x_1563_, v___y_1529_, v___y_1530_);
                    if crate::leanh::lean_obj_tag(v___x_1566_) == 0 {
                        v_a_1567_ = crate::leanh::lean_ctor_get(v___x_1566_, 0);
                        v_isSharedCheck_1581_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1566_)) as u8;
                        if v_isSharedCheck_1581_ == 0 {
                            v___x_1569_ = v___x_1566_;
                            v_isShared_1570_ = v_isSharedCheck_1581_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1567_);
                            crate::leanh::lean_dec(v___x_1566_);
                            v___x_1569_ = crate::leanh::lean_box(0);
                            v_isShared_1570_ = v_isSharedCheck_1581_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_1582_ = crate::leanh::lean_ctor_get(v___x_1566_, 0);
                        v_isSharedCheck_1589_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1566_)) as u8;
                        if v_isSharedCheck_1589_ == 0 {
                            v___x_1584_ = v___x_1566_;
                            v_isShared_1585_ = v_isSharedCheck_1589_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1582_);
                            crate::leanh::lean_dec(v___x_1566_);
                            v___x_1584_ = crate::leanh::lean_box(0);
                            v_isShared_1585_ = v_isSharedCheck_1589_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_1542_ = crate::leanh::lean_ctor_get(v_a_1538_, 0);
                if crate::leanh::lean_obj_tag(v_fst_1542_) == 0 {
                    v_snd_1543_ = crate::leanh::lean_ctor_get(v_a_1538_, 1);
                    crate::leanh::lean_inc(v_snd_1543_);
                    crate::leanh::lean_dec(v_a_1538_);
                    v___x_1544_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1544_, 0, v_snd_1543_);
                    if v_isShared_1541_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1540_, 0, v___x_1544_);
                        v___x_1546_ = v___x_1540_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1547_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1547_, 0, v___x_1544_);
                        v___x_1546_ = v_reuseFailAlloc_1547_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_1542_);
                    crate::leanh::lean_dec(v_a_1538_);
                    v_val_1548_ = crate::leanh::lean_ctor_get(v_fst_1542_, 0);
                    crate::leanh::lean_inc(v_val_1548_);
                    crate::leanh::lean_dec_ref_known(v_fst_1542_, 1);
                    if v_isShared_1541_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1540_, 0, v_val_1548_);
                        v___x_1550_ = v___x_1540_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1551_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1551_, 0, v_val_1548_);
                        v___x_1550_ = v_reuseFailAlloc_1551_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1546_;
            }
            3 => {
                return v___x_1550_;
            }
            4 => {
                if v_isShared_1556_ == 0 {
                    v___x_1558_ = v___x_1555_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1559_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1559_, 0, v_a_1553_);
                    v___x_1558_ = v_reuseFailAlloc_1559_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1558_;
            }
            6 => {
                v_fst_1571_ = crate::leanh::lean_ctor_get(v_a_1567_, 0);
                if crate::leanh::lean_obj_tag(v_fst_1571_) == 0 {
                    v_snd_1572_ = crate::leanh::lean_ctor_get(v_a_1567_, 1);
                    crate::leanh::lean_inc(v_snd_1572_);
                    crate::leanh::lean_dec(v_a_1567_);
                    v___x_1573_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1573_, 0, v_snd_1572_);
                    if v_isShared_1570_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1569_, 0, v___x_1573_);
                        v___x_1575_ = v___x_1569_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_1576_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1576_, 0, v___x_1573_);
                        v___x_1575_ = v_reuseFailAlloc_1576_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_1571_);
                    crate::leanh::lean_dec(v_a_1567_);
                    v_val_1577_ = crate::leanh::lean_ctor_get(v_fst_1571_, 0);
                    crate::leanh::lean_inc(v_val_1577_);
                    crate::leanh::lean_dec_ref_known(v_fst_1571_, 1);
                    if v_isShared_1570_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1569_, 0, v_val_1577_);
                        v___x_1579_ = v___x_1569_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_1580_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1580_, 0, v_val_1577_);
                        v___x_1579_ = v_reuseFailAlloc_1580_;
                        state = 8;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_1575_;
            }
            8 => {
                return v___x_1579_;
            }
            9 => {
                if v_isShared_1585_ == 0 {
                    v___x_1587_ = v___x_1584_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1588_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1588_, 0, v_a_1582_);
                    v___x_1587_ = v_reuseFailAlloc_1588_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1587_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__8(
    mut v_init_1590_: *mut crate::leanh::LeanObject,
    mut v___x_1591_: *mut crate::leanh::LeanObject,
    mut v___x_1592_: u8,
    mut v_as_1593_: *mut crate::leanh::LeanObject,
    mut v_sz_1594_: usize,
    mut v_i_1595_: usize,
    mut v_b_1596_: *mut crate::leanh::LeanObject,
    mut v___y_1597_: *mut crate::leanh::LeanObject,
    mut v___y_1598_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1600_: u8 = 0;
    let mut v___x_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1605_: u8 = 0;
    let mut v_a_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1611_: u8 = 0;
    let mut v___x_1612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: usize = 0;
    let mut v___x_1624_: usize = 0;
    let mut v_reuseFailAlloc_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1627_: u8 = 0;
    let mut v_a_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1631_: u8 = 0;
    let mut v___x_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1635_: u8 = 0;
    let mut v_isSharedCheck_1636_: u8 = 0;
    let mut v_unused_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1600_ = lean_usize_dec_lt(v_i_1595_, v_sz_1594_);
                if v___x_1600_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_1591_);
                    v___x_1601_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1601_, 0, v_b_1596_);
                    return v___x_1601_;
                } else {
                    v_snd_1602_ = crate::leanh::lean_ctor_get(v_b_1596_, 1);
                    v_isSharedCheck_1636_ = (!crate::leanh::lean_is_exclusive(v_b_1596_)) as u8;
                    if v_isSharedCheck_1636_ == 0 {
                        v_unused_1637_ = crate::leanh::lean_ctor_get(v_b_1596_, 0);
                        crate::leanh::lean_dec(v_unused_1637_);
                        v___x_1604_ = v_b_1596_;
                        v_isShared_1605_ = v_isSharedCheck_1636_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_1602_);
                        crate::leanh::lean_dec(v_b_1596_);
                        v___x_1604_ = crate::leanh::lean_box(0);
                        v_isShared_1605_ = v_isSharedCheck_1636_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_1606_ = lean_array_uget_borrowed(v_as_1593_, v_i_1595_);
                crate::leanh::lean_inc(v_snd_1602_);
                crate::leanh::lean_inc_ref(v___x_1591_);
                v___x_1607_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6(v_init_1590_, v___x_1591_, v___x_1592_, v_a_1606_, v_snd_1602_, v___y_1597_, v___y_1598_);
                if crate::leanh::lean_obj_tag(v___x_1607_) == 0 {
                    v_a_1608_ = crate::leanh::lean_ctor_get(v___x_1607_, 0);
                    v_isSharedCheck_1627_ = (!crate::leanh::lean_is_exclusive(v___x_1607_)) as u8;
                    if v_isSharedCheck_1627_ == 0 {
                        v___x_1610_ = v___x_1607_;
                        v_isShared_1611_ = v_isSharedCheck_1627_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1608_);
                        crate::leanh::lean_dec(v___x_1607_);
                        v___x_1610_ = crate::leanh::lean_box(0);
                        v_isShared_1611_ = v_isSharedCheck_1627_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1604_);
                    crate::leanh::lean_dec(v_snd_1602_);
                    crate::leanh::lean_dec_ref(v___x_1591_);
                    v_a_1628_ = crate::leanh::lean_ctor_get(v___x_1607_, 0);
                    v_isSharedCheck_1635_ = (!crate::leanh::lean_is_exclusive(v___x_1607_)) as u8;
                    if v_isSharedCheck_1635_ == 0 {
                        v___x_1630_ = v___x_1607_;
                        v_isShared_1631_ = v_isSharedCheck_1635_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1628_);
                        crate::leanh::lean_dec(v___x_1607_);
                        v___x_1630_ = crate::leanh::lean_box(0);
                        v_isShared_1631_ = v_isSharedCheck_1635_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_1608_) == 0 {
                    crate::leanh::lean_dec_ref(v___x_1591_);
                    v___x_1612_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1612_, 0, v_a_1608_);
                    if v_isShared_1605_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1604_, 0, v___x_1612_);
                        v___x_1614_ = v___x_1604_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1618_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1618_, 0, v___x_1612_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1618_, 1, v_snd_1602_);
                        v___x_1614_ = v_reuseFailAlloc_1618_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1610_);
                    crate::leanh::lean_dec(v_snd_1602_);
                    v_a_1619_ = crate::leanh::lean_ctor_get(v_a_1608_, 0);
                    crate::leanh::lean_inc(v_a_1619_);
                    crate::leanh::lean_dec_ref_known(v_a_1608_, 1);
                    v___x_1620_ = crate::leanh::lean_box(0);
                    if v_isShared_1605_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1604_, 1, v_a_1619_);
                        crate::leanh::lean_ctor_set(v___x_1604_, 0, v___x_1620_);
                        v___x_1622_ = v___x_1604_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1626_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1626_, 0, v___x_1620_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1626_, 1, v_a_1619_);
                        v___x_1622_ = v_reuseFailAlloc_1626_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_1611_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1610_, 0, v___x_1614_);
                    v___x_1616_ = v___x_1610_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1617_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1617_, 0, v___x_1614_);
                    v___x_1616_ = v_reuseFailAlloc_1617_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1616_;
            }
            5 => {
                v___x_1623_ = 1usize;
                v___x_1624_ = lean_usize_add(v_i_1595_, v___x_1623_);
                v_i_1595_ = v___x_1624_;
                v_b_1596_ = v___x_1622_;
                state = 0;
                continue;
            }
            6 => {
                if v_isShared_1631_ == 0 {
                    v___x_1633_ = v___x_1630_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1634_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1634_, 0, v_a_1628_);
                    v___x_1633_ = v_reuseFailAlloc_1634_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1633_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__8___boxed(
    mut v_init_1638_: *mut crate::leanh::LeanObject,
    mut v___x_1639_: *mut crate::leanh::LeanObject,
    mut v___x_1640_: *mut crate::leanh::LeanObject,
    mut v_as_1641_: *mut crate::leanh::LeanObject,
    mut v_sz_1642_: *mut crate::leanh::LeanObject,
    mut v_i_1643_: *mut crate::leanh::LeanObject,
    mut v_b_1644_: *mut crate::leanh::LeanObject,
    mut v___y_1645_: *mut crate::leanh::LeanObject,
    mut v___y_1646_: *mut crate::leanh::LeanObject,
    mut v___y_1647_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_9844__boxed_1648_: u8 = 0;
    let mut v_sz_boxed_1649_: usize = 0;
    let mut v_i_boxed_1650_: usize = 0;
    let mut v_res_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_9844__boxed_1648_ = (crate::leanh::lean_unbox(v___x_1640_) as u8);
    v_sz_boxed_1649_ = crate::leanh::lean_unbox_usize(v_sz_1642_);
    crate::leanh::lean_dec(v_sz_1642_);
    v_i_boxed_1650_ = crate::leanh::lean_unbox_usize(v_i_1643_);
    crate::leanh::lean_dec(v_i_1643_);
    v_res_1651_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__8(v_init_1638_, v___x_1639_, v___x_9844__boxed_1648_, v_as_1641_, v_sz_boxed_1649_, v_i_boxed_1650_, v_b_1644_, v___y_1645_, v___y_1646_);
    crate::leanh::lean_dec(v___y_1646_);
    crate::leanh::lean_dec_ref(v___y_1645_);
    crate::leanh::lean_dec_ref(v_as_1641_);
    return v_res_1651_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6___boxed(
    mut v_init_1652_: *mut crate::leanh::LeanObject,
    mut v___x_1653_: *mut crate::leanh::LeanObject,
    mut v___x_1654_: *mut crate::leanh::LeanObject,
    mut v_n_1655_: *mut crate::leanh::LeanObject,
    mut v_b_1656_: *mut crate::leanh::LeanObject,
    mut v___y_1657_: *mut crate::leanh::LeanObject,
    mut v___y_1658_: *mut crate::leanh::LeanObject,
    mut v___y_1659_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_9865__boxed_1660_: u8 = 0;
    let mut v_res_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_9865__boxed_1660_ = (crate::leanh::lean_unbox(v___x_1654_) as u8);
    v_res_1661_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6(v_init_1652_, v___x_1653_, v___x_9865__boxed_1660_, v_n_1655_, v_b_1656_, v___y_1657_, v___y_1658_);
    crate::leanh::lean_dec(v___y_1658_);
    crate::leanh::lean_dec_ref(v___y_1657_);
    crate::leanh::lean_dec_ref(v_n_1655_);
    return v_res_1661_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__7_spec__11(
    mut v___x_1665_: *mut crate::leanh::LeanObject,
    mut v___x_1666_: u8,
    mut v_as_1667_: *mut crate::leanh::LeanObject,
    mut v_sz_1668_: usize,
    mut v_i_1669_: usize,
    mut v_b_1670_: *mut crate::leanh::LeanObject,
    mut v___y_1671_: *mut crate::leanh::LeanObject,
    mut v___y_1672_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1674_: u8 = 0;
    let mut v___x_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: usize = 0;
    let mut v___x_1682_: usize = 0;
    let mut v_a_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1687_: u8 = 0;
    let mut v___x_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1691_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1674_ = lean_usize_dec_lt(v_i_1669_, v_sz_1668_);
                if v___x_1674_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_1665_);
                    v___x_1675_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1675_, 0, v_b_1670_);
                    return v___x_1675_;
                } else {
                    crate::leanh::lean_dec_ref(v_b_1670_);
                    v___x_1676_ = crate::leanh::lean_box(0);
                    v_a_1677_ = lean_array_uget_borrowed(v_as_1667_, v_i_1669_);
                    crate::leanh::lean_inc(v_a_1677_);
                    v___x_1678_ = l_Lean_Linter_getDeclsByBody(v_a_1677_);
                    crate::leanh::lean_inc_ref(v___x_1665_);
                    v___x_1679_ = l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg(v___x_1665_, v___x_1666_, v___x_1678_, v___x_1676_, v___y_1671_, v___y_1672_);
                    crate::leanh::lean_dec(v___x_1678_);
                    if crate::leanh::lean_obj_tag(v___x_1679_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_1679_, 1);
                        v___x_1680_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__7_spec__11___closed__0;
                        v___x_1681_ = 1usize;
                        v___x_1682_ = lean_usize_add(v_i_1669_, v___x_1681_);
                        v_i_1669_ = v___x_1682_;
                        v_b_1670_ = v___x_1680_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v___x_1665_);
                        v_a_1684_ = crate::leanh::lean_ctor_get(v___x_1679_, 0);
                        v_isSharedCheck_1691_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1679_)) as u8;
                        if v_isSharedCheck_1691_ == 0 {
                            v___x_1686_ = v___x_1679_;
                            v_isShared_1687_ = v_isSharedCheck_1691_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1684_);
                            crate::leanh::lean_dec(v___x_1679_);
                            v___x_1686_ = crate::leanh::lean_box(0);
                            v_isShared_1687_ = v_isSharedCheck_1691_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1687_ == 0 {
                    v___x_1689_ = v___x_1686_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1690_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1690_, 0, v_a_1684_);
                    v___x_1689_ = v_reuseFailAlloc_1690_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1689_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__7_spec__11___boxed(
    mut v___x_1692_: *mut crate::leanh::LeanObject,
    mut v___x_1693_: *mut crate::leanh::LeanObject,
    mut v_as_1694_: *mut crate::leanh::LeanObject,
    mut v_sz_1695_: *mut crate::leanh::LeanObject,
    mut v_i_1696_: *mut crate::leanh::LeanObject,
    mut v_b_1697_: *mut crate::leanh::LeanObject,
    mut v___y_1698_: *mut crate::leanh::LeanObject,
    mut v___y_1699_: *mut crate::leanh::LeanObject,
    mut v___y_1700_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_10057__boxed_1701_: u8 = 0;
    let mut v_sz_boxed_1702_: usize = 0;
    let mut v_i_boxed_1703_: usize = 0;
    let mut v_res_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_10057__boxed_1701_ = (crate::leanh::lean_unbox(v___x_1693_) as u8);
    v_sz_boxed_1702_ = crate::leanh::lean_unbox_usize(v_sz_1695_);
    crate::leanh::lean_dec(v_sz_1695_);
    v_i_boxed_1703_ = crate::leanh::lean_unbox_usize(v_i_1696_);
    crate::leanh::lean_dec(v_i_1696_);
    v_res_1704_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__7_spec__11(v___x_1692_, v___x_10057__boxed_1701_, v_as_1694_, v_sz_boxed_1702_, v_i_boxed_1703_, v_b_1697_, v___y_1698_, v___y_1699_);
    crate::leanh::lean_dec(v___y_1699_);
    crate::leanh::lean_dec_ref(v___y_1698_);
    crate::leanh::lean_dec_ref(v_as_1694_);
    return v_res_1704_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__7(
    mut v___x_1705_: *mut crate::leanh::LeanObject,
    mut v___x_1706_: u8,
    mut v_as_1707_: *mut crate::leanh::LeanObject,
    mut v_sz_1708_: usize,
    mut v_i_1709_: usize,
    mut v_b_1710_: *mut crate::leanh::LeanObject,
    mut v___y_1711_: *mut crate::leanh::LeanObject,
    mut v___y_1712_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1714_: u8 = 0;
    let mut v___x_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: usize = 0;
    let mut v___x_1722_: usize = 0;
    let mut v___x_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1727_: u8 = 0;
    let mut v___x_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1731_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1714_ = lean_usize_dec_lt(v_i_1709_, v_sz_1708_);
                if v___x_1714_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_1705_);
                    v___x_1715_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1715_, 0, v_b_1710_);
                    return v___x_1715_;
                } else {
                    crate::leanh::lean_dec_ref(v_b_1710_);
                    v___x_1716_ = crate::leanh::lean_box(0);
                    v_a_1717_ = lean_array_uget_borrowed(v_as_1707_, v_i_1709_);
                    crate::leanh::lean_inc(v_a_1717_);
                    v___x_1718_ = l_Lean_Linter_getDeclsByBody(v_a_1717_);
                    crate::leanh::lean_inc_ref(v___x_1705_);
                    v___x_1719_ = l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg(v___x_1705_, v___x_1706_, v___x_1718_, v___x_1716_, v___y_1711_, v___y_1712_);
                    crate::leanh::lean_dec(v___x_1718_);
                    if crate::leanh::lean_obj_tag(v___x_1719_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_1719_, 1);
                        v___x_1720_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__7_spec__11___closed__0;
                        v___x_1721_ = 1usize;
                        v___x_1722_ = lean_usize_add(v_i_1709_, v___x_1721_);
                        v___x_1723_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__7_spec__11(v___x_1705_, v___x_1706_, v_as_1707_, v_sz_1708_, v___x_1722_, v___x_1720_, v___y_1711_, v___y_1712_);
                        return v___x_1723_;
                    } else {
                        crate::leanh::lean_dec_ref(v___x_1705_);
                        v_a_1724_ = crate::leanh::lean_ctor_get(v___x_1719_, 0);
                        v_isSharedCheck_1731_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1719_)) as u8;
                        if v_isSharedCheck_1731_ == 0 {
                            v___x_1726_ = v___x_1719_;
                            v_isShared_1727_ = v_isSharedCheck_1731_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1724_);
                            crate::leanh::lean_dec(v___x_1719_);
                            v___x_1726_ = crate::leanh::lean_box(0);
                            v_isShared_1727_ = v_isSharedCheck_1731_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1727_ == 0 {
                    v___x_1729_ = v___x_1726_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1730_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1730_, 0, v_a_1724_);
                    v___x_1729_ = v_reuseFailAlloc_1730_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1729_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__7___boxed(
    mut v___x_1732_: *mut crate::leanh::LeanObject,
    mut v___x_1733_: *mut crate::leanh::LeanObject,
    mut v_as_1734_: *mut crate::leanh::LeanObject,
    mut v_sz_1735_: *mut crate::leanh::LeanObject,
    mut v_i_1736_: *mut crate::leanh::LeanObject,
    mut v_b_1737_: *mut crate::leanh::LeanObject,
    mut v___y_1738_: *mut crate::leanh::LeanObject,
    mut v___y_1739_: *mut crate::leanh::LeanObject,
    mut v___y_1740_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_10113__boxed_1741_: u8 = 0;
    let mut v_sz_boxed_1742_: usize = 0;
    let mut v_i_boxed_1743_: usize = 0;
    let mut v_res_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_10113__boxed_1741_ = (crate::leanh::lean_unbox(v___x_1733_) as u8);
    v_sz_boxed_1742_ = crate::leanh::lean_unbox_usize(v_sz_1735_);
    crate::leanh::lean_dec(v_sz_1735_);
    v_i_boxed_1743_ = crate::leanh::lean_unbox_usize(v_i_1736_);
    crate::leanh::lean_dec(v_i_1736_);
    v_res_1744_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__7(v___x_1732_, v___x_10113__boxed_1741_, v_as_1734_, v_sz_boxed_1742_, v_i_boxed_1743_, v_b_1737_, v___y_1738_, v___y_1739_);
    crate::leanh::lean_dec(v___y_1739_);
    crate::leanh::lean_dec_ref(v___y_1738_);
    crate::leanh::lean_dec_ref(v_as_1734_);
    return v_res_1744_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4(
    mut v___x_1745_: *mut crate::leanh::LeanObject,
    mut v___x_1746_: u8,
    mut v_t_1747_: *mut crate::leanh::LeanObject,
    mut v_init_1748_: *mut crate::leanh::LeanObject,
    mut v___y_1749_: *mut crate::leanh::LeanObject,
    mut v___y_1750_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_root_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1758_: u8 = 0;
    let mut v_a_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1766_: usize = 0;
    let mut v___x_1767_: usize = 0;
    let mut v___x_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1772_: u8 = 0;
    let mut v_fst_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1782_: u8 = 0;
    let mut v_a_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1786_: u8 = 0;
    let mut v___x_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1790_: u8 = 0;
    let mut v_isSharedCheck_1791_: u8 = 0;
    let mut v_a_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1795_: u8 = 0;
    let mut v___x_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1799_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_1752_ = crate::leanh::lean_ctor_get(v_t_1747_, 0);
                v_tail_1753_ = crate::leanh::lean_ctor_get(v_t_1747_, 1);
                crate::leanh::lean_inc_ref(v___x_1745_);
                v___x_1754_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6(v_init_1748_, v___x_1745_, v___x_1746_, v_root_1752_, v_init_1748_, v___y_1749_, v___y_1750_);
                if crate::leanh::lean_obj_tag(v___x_1754_) == 0 {
                    v_a_1755_ = crate::leanh::lean_ctor_get(v___x_1754_, 0);
                    v_isSharedCheck_1791_ = (!crate::leanh::lean_is_exclusive(v___x_1754_)) as u8;
                    if v_isSharedCheck_1791_ == 0 {
                        v___x_1757_ = v___x_1754_;
                        v_isShared_1758_ = v_isSharedCheck_1791_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1755_);
                        crate::leanh::lean_dec(v___x_1754_);
                        v___x_1757_ = crate::leanh::lean_box(0);
                        v_isShared_1758_ = v_isSharedCheck_1791_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_1745_);
                    v_a_1792_ = crate::leanh::lean_ctor_get(v___x_1754_, 0);
                    v_isSharedCheck_1799_ = (!crate::leanh::lean_is_exclusive(v___x_1754_)) as u8;
                    if v_isSharedCheck_1799_ == 0 {
                        v___x_1794_ = v___x_1754_;
                        v_isShared_1795_ = v_isSharedCheck_1799_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1792_);
                        crate::leanh::lean_dec(v___x_1754_);
                        v___x_1794_ = crate::leanh::lean_box(0);
                        v_isShared_1795_ = v_isSharedCheck_1799_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_1755_) == 0 {
                    crate::leanh::lean_dec_ref(v___x_1745_);
                    v_a_1759_ = crate::leanh::lean_ctor_get(v_a_1755_, 0);
                    crate::leanh::lean_inc(v_a_1759_);
                    crate::leanh::lean_dec_ref_known(v_a_1755_, 1);
                    if v_isShared_1758_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1757_, 0, v_a_1759_);
                        v___x_1761_ = v___x_1757_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1762_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1762_, 0, v_a_1759_);
                        v___x_1761_ = v_reuseFailAlloc_1762_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1757_);
                    v_a_1763_ = crate::leanh::lean_ctor_get(v_a_1755_, 0);
                    crate::leanh::lean_inc(v_a_1763_);
                    crate::leanh::lean_dec_ref_known(v_a_1755_, 1);
                    v___x_1764_ = crate::leanh::lean_box(0);
                    v___x_1765_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1765_, 0, v___x_1764_);
                    crate::leanh::lean_ctor_set(v___x_1765_, 1, v_a_1763_);
                    v_sz_1766_ = lean_array_size(v_tail_1753_);
                    v___x_1767_ = 0usize;
                    v___x_1768_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__7(v___x_1745_, v___x_1746_, v_tail_1753_, v_sz_1766_, v___x_1767_, v___x_1765_, v___y_1749_, v___y_1750_);
                    if crate::leanh::lean_obj_tag(v___x_1768_) == 0 {
                        v_a_1769_ = crate::leanh::lean_ctor_get(v___x_1768_, 0);
                        v_isSharedCheck_1782_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1768_)) as u8;
                        if v_isSharedCheck_1782_ == 0 {
                            v___x_1771_ = v___x_1768_;
                            v_isShared_1772_ = v_isSharedCheck_1782_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1769_);
                            crate::leanh::lean_dec(v___x_1768_);
                            v___x_1771_ = crate::leanh::lean_box(0);
                            v_isShared_1772_ = v_isSharedCheck_1782_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_1783_ = crate::leanh::lean_ctor_get(v___x_1768_, 0);
                        v_isSharedCheck_1790_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1768_)) as u8;
                        if v_isSharedCheck_1790_ == 0 {
                            v___x_1785_ = v___x_1768_;
                            v_isShared_1786_ = v_isSharedCheck_1790_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1783_);
                            crate::leanh::lean_dec(v___x_1768_);
                            v___x_1785_ = crate::leanh::lean_box(0);
                            v_isShared_1786_ = v_isSharedCheck_1790_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_1761_;
            }
            3 => {
                v_fst_1773_ = crate::leanh::lean_ctor_get(v_a_1769_, 0);
                if crate::leanh::lean_obj_tag(v_fst_1773_) == 0 {
                    v_snd_1774_ = crate::leanh::lean_ctor_get(v_a_1769_, 1);
                    crate::leanh::lean_inc(v_snd_1774_);
                    crate::leanh::lean_dec(v_a_1769_);
                    if v_isShared_1772_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1771_, 0, v_snd_1774_);
                        v___x_1776_ = v___x_1771_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1777_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_snd_1774_);
                        v___x_1776_ = v_reuseFailAlloc_1777_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_1773_);
                    crate::leanh::lean_dec(v_a_1769_);
                    v_val_1778_ = crate::leanh::lean_ctor_get(v_fst_1773_, 0);
                    crate::leanh::lean_inc(v_val_1778_);
                    crate::leanh::lean_dec_ref_known(v_fst_1773_, 1);
                    if v_isShared_1772_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1771_, 0, v_val_1778_);
                        v___x_1780_ = v___x_1771_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1781_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1781_, 0, v_val_1778_);
                        v___x_1780_ = v_reuseFailAlloc_1781_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_1776_;
            }
            5 => {
                return v___x_1780_;
            }
            6 => {
                if v_isShared_1786_ == 0 {
                    v___x_1788_ = v___x_1785_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1789_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1789_, 0, v_a_1783_);
                    v___x_1788_ = v_reuseFailAlloc_1789_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1788_;
            }
            8 => {
                if v_isShared_1795_ == 0 {
                    v___x_1797_ = v___x_1794_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1798_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1798_, 0, v_a_1792_);
                    v___x_1797_ = v_reuseFailAlloc_1798_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1797_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4___boxed(
    mut v___x_1800_: *mut crate::leanh::LeanObject,
    mut v___x_1801_: *mut crate::leanh::LeanObject,
    mut v_t_1802_: *mut crate::leanh::LeanObject,
    mut v_init_1803_: *mut crate::leanh::LeanObject,
    mut v___y_1804_: *mut crate::leanh::LeanObject,
    mut v___y_1805_: *mut crate::leanh::LeanObject,
    mut v___y_1806_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_10164__boxed_1807_: u8 = 0;
    let mut v_res_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_10164__boxed_1807_ = (crate::leanh::lean_unbox(v___x_1801_) as u8);
    v_res_1808_ = l_Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4(
        v___x_1800_,
        v___x_10164__boxed_1807_,
        v_t_1802_,
        v_init_1803_,
        v___y_1804_,
        v___y_1805_,
    );
    crate::leanh::lean_dec(v___y_1805_);
    crate::leanh::lean_dec_ref(v___y_1804_);
    crate::leanh::lean_dec_ref(v_t_1802_);
    return v_res_1808_;
}
pub unsafe fn l_Lean_Linter_DefProp_defPropLinter___lam__0(
    mut v_x_1809_: *mut crate::leanh::LeanObject,
    mut v___y_1810_: *mut crate::leanh::LeanObject,
    mut v___y_1811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1817_: u8 = 0;
    let mut v___x_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: u8 = 0;
    let mut v___x_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: u8 = 0;
    let mut v___x_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1835_: u8 = 0;
    let mut v___x_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1839_: u8 = 0;
    let mut v_unused_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1845_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1813_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_DefProp_defPropLinter_spec__0(v___y_1810_, v___y_1811_);
                v_a_1814_ = crate::leanh::lean_ctor_get(v___x_1813_, 0);
                v_isSharedCheck_1845_ = (!crate::leanh::lean_is_exclusive(v___x_1813_)) as u8;
                if v_isSharedCheck_1845_ == 0 {
                    v___x_1816_ = v___x_1813_;
                    v_isShared_1817_ = v_isSharedCheck_1845_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1814_);
                    crate::leanh::lean_dec(v___x_1813_);
                    v___x_1816_ = crate::leanh::lean_box(0);
                    v_isShared_1817_ = v_isSharedCheck_1845_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1818_ = l_Lean_Linter_linter_defProp;
                v___x_1819_ = l_Lean_Linter_getLinterValue(v___x_1818_, v_a_1814_);
                crate::leanh::lean_dec(v_a_1814_);
                if v___x_1819_ == 0 {
                    v___x_1820_ = crate::leanh::lean_box(0);
                    if v_isShared_1817_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1816_, 0, v___x_1820_);
                        v___x_1822_ = v___x_1816_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1823_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1823_, 0, v___x_1820_);
                        v___x_1822_ = v_reuseFailAlloc_1823_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1824_ = lean_st_ref_get(v___y_1811_);
                    v_messages_1825_ = crate::leanh::lean_ctor_get(v___x_1824_, 1);
                    crate::leanh::lean_inc_ref(v_messages_1825_);
                    crate::leanh::lean_dec(v___x_1824_);
                    v___x_1826_ = l_Lean_MessageLog_hasErrors(v_messages_1825_);
                    crate::leanh::lean_dec_ref(v_messages_1825_);
                    if v___x_1826_ == 0 {
                        crate::leanh::lean_del_object(v___x_1816_);
                        v___x_1827_ = lean_st_ref_get(v___y_1811_);
                        v___x_1828_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_DefProp_defPropLinter_spec__1___redArg(v___y_1811_);
                        v_a_1829_ = crate::leanh::lean_ctor_get(v___x_1828_, 0);
                        crate::leanh::lean_inc(v_a_1829_);
                        crate::leanh::lean_dec_ref(v___x_1828_);
                        v_env_1830_ = crate::leanh::lean_ctor_get(v___x_1827_, 0);
                        crate::leanh::lean_inc_ref(v_env_1830_);
                        crate::leanh::lean_dec(v___x_1827_);
                        v___x_1831_ = crate::leanh::lean_box(0);
                        v___x_1832_ = l_Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4(v_env_1830_, v___x_1826_, v_a_1829_, v___x_1831_, v___y_1810_, v___y_1811_);
                        crate::leanh::lean_dec(v_a_1829_);
                        if crate::leanh::lean_obj_tag(v___x_1832_) == 0 {
                            v_isSharedCheck_1839_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1832_)) as u8;
                            if v_isSharedCheck_1839_ == 0 {
                                v_unused_1840_ = crate::leanh::lean_ctor_get(v___x_1832_, 0);
                                crate::leanh::lean_dec(v_unused_1840_);
                                v___x_1834_ = v___x_1832_;
                                v_isShared_1835_ = v_isSharedCheck_1839_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_1832_);
                                v___x_1834_ = crate::leanh::lean_box(0);
                                v_isShared_1835_ = v_isSharedCheck_1839_;
                                state = 3;
                                continue;
                            }
                        } else {
                            return v___x_1832_;
                        }
                    } else {
                        v___x_1841_ = crate::leanh::lean_box(0);
                        if v_isShared_1817_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1816_, 0, v___x_1841_);
                            v___x_1843_ = v___x_1816_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_1844_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1844_, 0, v___x_1841_);
                            v___x_1843_ = v_reuseFailAlloc_1844_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_1822_;
            }
            3 => {
                if v_isShared_1835_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1834_, 0, v___x_1831_);
                    v___x_1837_ = v___x_1834_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1838_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1838_, 0, v___x_1831_);
                    v___x_1837_ = v_reuseFailAlloc_1838_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1837_;
            }
            5 => {
                return v___x_1843_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_DefProp_defPropLinter___lam__0___boxed(
    mut v_x_1846_: *mut crate::leanh::LeanObject,
    mut v___y_1847_: *mut crate::leanh::LeanObject,
    mut v___y_1848_: *mut crate::leanh::LeanObject,
    mut v___y_1849_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1850_ = l_Lean_Linter_DefProp_defPropLinter___lam__0(v_x_1846_, v___y_1847_, v___y_1848_);
    crate::leanh::lean_dec(v___y_1848_);
    crate::leanh::lean_dec_ref(v___y_1847_);
    crate::leanh::lean_dec(v_x_1846_);
    return v_res_1850_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_DefProp_defPropLinter_spec__0_spec__0(
    mut v_o_1865_: *mut crate::leanh::LeanObject,
    mut v___y_1866_: *mut crate::leanh::LeanObject,
    mut v___y_1867_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1869_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_DefProp_defPropLinter_spec__0_spec__0___redArg(v_o_1865_, v___y_1867_);
    return v___x_1869_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_DefProp_defPropLinter_spec__0_spec__0___boxed(
    mut v_o_1870_: *mut crate::leanh::LeanObject,
    mut v___y_1871_: *mut crate::leanh::LeanObject,
    mut v___y_1872_: *mut crate::leanh::LeanObject,
    mut v___y_1873_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1874_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_DefProp_defPropLinter_spec__0_spec__0(v_o_1870_, v___y_1871_, v___y_1872_);
    crate::leanh::lean_dec(v___y_1872_);
    crate::leanh::lean_dec_ref(v___y_1871_);
    return v_res_1874_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3(
    mut v___x_1875_: *mut crate::leanh::LeanObject,
    mut v___x_1876_: u8,
    mut v_as_1877_: *mut crate::leanh::LeanObject,
    mut v_as_x27_1878_: *mut crate::leanh::LeanObject,
    mut v_b_1879_: *mut crate::leanh::LeanObject,
    mut v_a_1880_: *mut crate::leanh::LeanObject,
    mut v___y_1881_: *mut crate::leanh::LeanObject,
    mut v___y_1882_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1884_ = l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg(
        v___x_1875_,
        v___x_1876_,
        v_as_x27_1878_,
        v_b_1879_,
        v___y_1881_,
        v___y_1882_,
    );
    return v___x_1884_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___boxed(
    mut v___x_1885_: *mut crate::leanh::LeanObject,
    mut v___x_1886_: *mut crate::leanh::LeanObject,
    mut v_as_1887_: *mut crate::leanh::LeanObject,
    mut v_as_x27_1888_: *mut crate::leanh::LeanObject,
    mut v_b_1889_: *mut crate::leanh::LeanObject,
    mut v_a_1890_: *mut crate::leanh::LeanObject,
    mut v___y_1891_: *mut crate::leanh::LeanObject,
    mut v___y_1892_: *mut crate::leanh::LeanObject,
    mut v___y_1893_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_10397__boxed_1894_: u8 = 0;
    let mut v_res_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_10397__boxed_1894_ = (crate::leanh::lean_unbox(v___x_1886_) as u8);
    v_res_1895_ = l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3(
        v___x_1885_,
        v___x_10397__boxed_1894_,
        v_as_1887_,
        v_as_x27_1888_,
        v_b_1889_,
        v_a_1890_,
        v___y_1891_,
        v___y_1892_,
    );
    crate::leanh::lean_dec(v___y_1892_);
    crate::leanh::lean_dec_ref(v___y_1891_);
    crate::leanh::lean_dec(v_as_x27_1888_);
    crate::leanh::lean_dec(v_as_1887_);
    return v_res_1895_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10(
    mut v_msgData_1896_: *mut crate::leanh::LeanObject,
    mut v___y_1897_: *mut crate::leanh::LeanObject,
    mut v___y_1898_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1900_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg(v_msgData_1896_, v___y_1898_);
    return v___x_1900_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___boxed(
    mut v_msgData_1901_: *mut crate::leanh::LeanObject,
    mut v___y_1902_: *mut crate::leanh::LeanObject,
    mut v___y_1903_: *mut crate::leanh::LeanObject,
    mut v___y_1904_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1905_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10(v_msgData_1901_, v___y_1902_, v___y_1903_);
    crate::leanh::lean_dec(v___y_1903_);
    crate::leanh::lean_dec_ref(v___y_1902_);
    return v_res_1905_;
}
pub unsafe fn l___private_Lean_Linter_DefProp_0__Lean_Linter_DefProp_initFn_00___x40_Lean_Linter_DefProp_3668228144____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1907_ = l_Lean_Linter_DefProp_defPropLinter;
    v___x_1908_ = l_Lean_Elab_Command_addLinter(v___x_1907_);
    return v___x_1908_;
}
pub unsafe fn l___private_Lean_Linter_DefProp_0__Lean_Linter_DefProp_initFn_00___x40_Lean_Linter_DefProp_3668228144____hygCtx___hyg_2____boxed(
    mut v_a_1909_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1910_ = l___private_Lean_Linter_DefProp_0__Lean_Linter_DefProp_initFn_00___x40_Lean_Linter_DefProp_3668228144____hygCtx___hyg_2_();
    return v_res_1910_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Linter_DefProp(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Linter_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Linter_linter_defProp = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_Linter_linter_defProp);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Linter_DefProp_0__Lean_Linter_DefProp_initFn_00___x40_Lean_Linter_DefProp_3668228144____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Linter_DefProp(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Linter_DefProp(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Linter_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Linter_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_DefProp(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Linter_DefProp(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Linter_DefProp(builtin);
}
